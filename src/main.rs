mod generator;

use anyhow::Context;
use rust_decimal::prelude::ToPrimitive;

trait HashMapInsertUniqueExt<K, V> {
    fn insert_unique(&mut self, key: K, value: V) -> Option<&mut V>;
}

impl<K: Eq + std::hash::Hash, V> HashMapInsertUniqueExt<K, V> for std::collections::HashMap<K, V> {
    /// Inserts a key-value pair only if the key doesn't exist.
    /// Returns Some(&mut value) on success, None if key already existed.
    fn insert_unique(&mut self, key: K, value: V) -> Option<&mut V> {
        match self.entry(key) {
            std::collections::hash_map::Entry::Vacant(e) => Some(e.insert(value)),
            std::collections::hash_map::Entry::Occupied(_) => None,
        }
    }
}

const SCALE: u32 = 4;
const PRECISION: u64 = 10_u64.pow(SCALE);

// code does not compile with if consts are not what we expect :)
const _: () = assert!(SCALE == 4, "SCALE must be exactly 4 decimal places");
const _: () = assert!(PRECISION == 10_000, "PRECISION must be exactly 10_000");

fn decimal_to_u64(d: rust_decimal::Decimal) -> anyhow::Result<u64> {
    if d.scale() > SCALE {
        anyhow::bail!("Amount has more than {} decimal places: {}", SCALE, d);
    }

    let scaled = d
        .checked_mul(rust_decimal::Decimal::from(PRECISION))
        .context("Multiplication overflow in decimal_to_u64")?;

    scaled.to_u64().context("Amount out of range for u64")
}

fn u64_to_decimal(n: u64) -> anyhow::Result<rust_decimal::Decimal> {
    rust_decimal::Decimal::from(n)
        .checked_div(rust_decimal::Decimal::from(PRECISION))
        .context("Division failed in u64_to_decimal")
}

fn i64_to_decimal(n: i64) -> anyhow::Result<rust_decimal::Decimal> {
    rust_decimal::Decimal::from(n)
        // todo, avoid casting with as
        .checked_div(rust_decimal::Decimal::from(PRECISION as i64))
        .context("Division failed in i64_to_decimal")
}

#[derive(serde::Deserialize)]
#[serde(rename_all = "lowercase")]
enum TxKind {
    Deposit,
    Withdrawal,
    Dispute,
    Resolve,
    Chargeback,
}

#[derive(serde::Deserialize)]
struct TxRecord {
    #[serde(rename = "type")]
    kind: TxKind,
    client: u16,
    tx: u32,
    #[serde(default, with = "rust_decimal::serde::str_option")]
    amount: Option<rust_decimal::Decimal>,
}

#[derive(serde::Serialize)]
struct ClientRow {
    client: u16,
    #[serde(with = "rust_decimal::serde::str")]
    available: rust_decimal::Decimal,
    #[serde(with = "rust_decimal::serde::str")]
    held: rust_decimal::Decimal,
    #[serde(with = "rust_decimal::serde::str")]
    total: rust_decimal::Decimal,
    locked: bool,
}

struct Account {
    /// Available balance can be negative when a dispute is opened after the user
    /// has already withdrawn some of the disputed funds. This represents a liability
    /// the user has with the payment processor.
    available_balance: i64,
    blocked_balance: u64,
    locked: bool,
}

struct Deposit {
    account_id: u16,
    amount: u64,
    disputed: bool,
}

enum TxAction {
    Deposit { tx_id: u32, amount: u64 },
    Withdrawal { tx_id: u32, amount: u64 },
    Dispute { tx_id: u32 },
    Resolve { tx_id: u32 },
    Chargeback { tx_id: u32 },
}

struct Tx {
    account_id: u16,
    action: TxAction,
}

fn process(
    accounts: &mut std::collections::HashMap<u16, Account>,
    deposits: &mut std::collections::HashMap<u32, Deposit>,
    withdrawals: &mut std::collections::HashMap<u32, u64>,
    tx: Tx,
) -> anyhow::Result<()> {
    let account_id = tx.account_id;
    match tx.action {
        TxAction::Deposit { tx_id, amount } => {
            if let Some(existing) = deposits.get(&tx_id) {
                // Paranoid check: is only idempotent with amounts are the same.
                anyhow::ensure!(
                    existing.amount == amount,
                    "Duplicate deposit tx_id {} with different amount",
                    tx_id
                );

                // Idempotent
                return Ok(());
            }

            match accounts.entry(account_id) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let acc = entry.get_mut();

                    if acc.locked {
                        return Ok(());
                    }

                    let amount_i64 = i64::try_from(amount).context("Deposit amount too large")?;
                    let new_balance = acc
                        .available_balance
                        .checked_add(amount_i64)
                        .context("Deposit would overflow available balance")?;

                    acc.available_balance = new_balance;
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let amount_i64 = i64::try_from(amount).context("Deposit amount too large")?;
                    entry.insert(Account {
                        available_balance: amount_i64,
                        blocked_balance: 0,
                        locked: false,
                    });
                }
            }

            deposits
                .insert_unique(
                    tx_id,
                    Deposit {
                        account_id,
                        amount,
                        disputed: false,
                    },
                )
                .with_context(|| format!("Unexpected: deposit tx_id {} already existed", tx_id))?;
        }
        TxAction::Withdrawal { tx_id, amount } => {
            if let Some(&existing_amount) = withdrawals.get(&tx_id) {
                // Paranoid check: is only idempotent with amounts are the same.
                anyhow::ensure!(
                    existing_amount == amount,
                    "Duplicate withdrawal tx_id {} with different amount",
                    tx_id
                );

                // Idempotent
                return Ok(());
            }

            withdrawals.insert_unique(tx_id, amount).with_context(|| {
                format!("Unexpected: withdrawal tx_id {} already existed", tx_id)
            })?;

            let amount_i64 = i64::try_from(amount).context("too big")?;

            accounts.entry(account_id).and_modify(|acc| {
                if acc.locked {
                    return;
                }

                // Withdrawals require sufficient available funds (non-negative result)
                if let Some(new_balance) = acc.available_balance.checked_sub(amount_i64) {
                    if new_balance >= 0 {
                        acc.available_balance = new_balance;
                    }
                }
            });
        }
        TxAction::Dispute { tx_id } => {
            // A dispute represents a client's claim that a transaction was erroneous and should be reversed.
            // The transaction shouldn't be reversed yet but the associated funds should be held. This means
            // that the clients available funds should decrease by the amount disputed, their held funds should
            // increase by the amount disputed, while their total funds should remain the same.
            //
            // Notice that a dispute does not state the amount disputed. Instead a dispute references the
            // transaction that is disputed by ID. If the tx specified by the dispute doesn't exist you can ignore it
            // and assume this is an error on our partners side.

            let std::collections::hash_map::Entry::Occupied(mut dep_entry) = deposits.entry(tx_id)
            else {
                return Ok(());
            };
            let dep = dep_entry.get_mut();

            // Paranoid check: dispute account should match the deposit account
            if dep.account_id != account_id {
                return Ok(());
            }

            // If the transaction is already disputed, we can ignore
            if dep.disputed {
                return Ok(());
            }

            // Invariant: if a deposit exists, its account must exist (created during deposit processing)
            let acc = accounts
                .get_mut(&account_id)
                .context("deposit references non-existent account")?;

            if acc.locked {
                return Ok(());
            }

            // Disputes are allowed to make available_balance negative.
            // This represents a liability the user has with the payment processor
            // when they withdraw funds and then the deposit is disputed.
            let amount_i64 = i64::try_from(dep.amount).context("Dispute amount too large")?;
            let Some(new_available) = acc.available_balance.checked_sub(amount_i64) else {
                return Ok(());
            };

            let new_blocked = acc
                .blocked_balance
                .checked_add(dep.amount)
                .context("Dispute would overflow blocked balance")?;

            dep.disputed = true;
            acc.available_balance = new_available;
            acc.blocked_balance = new_blocked;
        }
        TxAction::Resolve { tx_id } => {
            // A resolve represents a resolution to a dispute, releasing the associated held funds. Funds that
            // were previously disputed are no longer disputed. This means that the clients held funds should
            // decrease by the amount no longer disputed, their available funds should increase by the amount
            // no longer disputed, and their total funds should remain the same.

            let std::collections::hash_map::Entry::Occupied(mut dep_entry) = deposits.entry(tx_id)
            else {
                return Ok(());
            };
            let dep = dep_entry.get_mut();

            // Paranoid check: dispute account should match the deposit account
            if dep.account_id != account_id {
                return Ok(());
            }

            // Resolve should only be applied to a disputed transaction
            if !dep.disputed {
                return Ok(());
            }

            // Invariant: if a deposit exists, its account must exist
            let acc = accounts
                .get_mut(&account_id)
                .context("BUG: deposit references non-existent account")?;

            if acc.locked {
                return Ok(());
            }

            let Some(new_blocked) = acc.blocked_balance.checked_sub(dep.amount) else {
                return Ok(());
            };

            let amount_i64 = i64::try_from(dep.amount).context("Resolve amount too large")?;
            let new_available = acc
                .available_balance
                .checked_add(amount_i64)
                .context("Resolve would overflow available balance")?;

            dep.disputed = false;
            acc.available_balance = new_available;
            acc.blocked_balance = new_blocked;
        }
        TxAction::Chargeback { tx_id } => {
            // A chargeback is the final state of a dispute and represents the client reversing a transaction.
            // Funds that were held have now been withdrawn. This means that the clients held funds and total
            // funds should decrease by the amount previously disputed. If a chargeback occurs the client's
            // account should be immediately frozen.

            let std::collections::hash_map::Entry::Occupied(mut dep_entry) = deposits.entry(tx_id)
            else {
                return Ok(());
            };
            let dep = dep_entry.get_mut();

            // Paranoid check: dispute account should match the deposit account
            if dep.account_id != account_id {
                return Ok(());
            }

            // Chargeback should only be applied to a disputed transaction
            if !dep.disputed {
                return Ok(());
            }

            // Invariant: if a deposit exists, its account must exist
            let acc = accounts
                .get_mut(&account_id)
                .context("BUG: deposit references non-existent account")?;

            if acc.locked {
                return Ok(());
            }

            let Some(new_blocked) = acc.blocked_balance.checked_sub(dep.amount) else {
                return Ok(());
            };

            // Check if there are sufficient funds to fulfill the chargeback.
            // If available_balance is negative, it means the user already withdrew
            // funds that were later disputed. We cannot complete the chargeback
            // because the amount is not are not recoverable.
            let new_blocked_i64 =
                i64::try_from(new_blocked).context("Blocked balance too large for i64")?;
            let total_after_chargeback = acc
                .available_balance
                .checked_add(new_blocked_i64)
                .context("Total balance overflow")?;
            anyhow::ensure!(
                total_after_chargeback >= 0,
                "Insufficient funds to fulfill chargeback: account {} would have negative total balance {}",
                account_id,
                total_after_chargeback
            );

            acc.blocked_balance = new_blocked;
            acc.locked = true;
        }
    }
    Ok(())
}

fn process_csv<R: std::io::Read>(
    reader: R,
) -> anyhow::Result<std::collections::HashMap<u16, Account>> {
    let mut rdr = csv::ReaderBuilder::new()
        .trim(csv::Trim::All)
        .from_reader(reader);

    let mut accounts: std::collections::HashMap<u16, Account> = std::collections::HashMap::new();
    let mut deposits: std::collections::HashMap<u32, Deposit> = std::collections::HashMap::new();
    let mut withdrawals: std::collections::HashMap<u32, u64> = std::collections::HashMap::new();

    for (line_num, result) in rdr.deserialize().enumerate() {
        let line = line_num + 2; // +1 for 0-index, +1 for header
        let record: TxRecord = result.with_context(|| format!("Failed to parse row {}", line))?;

        let tx = match record.kind {
            TxKind::Deposit => {
                let amount_dec = record
                    .amount
                    .with_context(|| format!("Deposit missing amount at line {}", line))?;
                let amount = decimal_to_u64(amount_dec)
                    .with_context(|| format!("Invalid deposit amount at line {}", line))?;
                Tx {
                    account_id: record.client,
                    action: TxAction::Deposit {
                        tx_id: record.tx,
                        amount,
                    },
                }
            }
            TxKind::Withdrawal => {
                let amount_dec = record
                    .amount
                    .with_context(|| format!("Withdrawal missing amount at line {}", line))?;
                let amount = decimal_to_u64(amount_dec)
                    .with_context(|| format!("Invalid withdrawal amount at line {}", line))?;
                Tx {
                    account_id: record.client,
                    action: TxAction::Withdrawal {
                        tx_id: record.tx,
                        amount,
                    },
                }
            }
            TxKind::Dispute => Tx {
                account_id: record.client,
                action: TxAction::Dispute { tx_id: record.tx },
            },
            TxKind::Resolve => Tx {
                account_id: record.client,
                action: TxAction::Resolve { tx_id: record.tx },
            },
            TxKind::Chargeback => Tx {
                account_id: record.client,
                action: TxAction::Chargeback { tx_id: record.tx },
            },
        };

        process(&mut accounts, &mut deposits, &mut withdrawals, tx)
            .with_context(|| format!("Failed to process transaction at line {}", line))?;
    }

    Ok(accounts)
}

fn write_accounts_csv<W: std::io::Write>(
    accounts: std::collections::HashMap<u16, Account>,
    writer: W,
) -> anyhow::Result<()> {
    let mut wtr = csv::Writer::from_writer(writer);

    for (client_id, account) in accounts {
        let blocked_i64 =
            i64::try_from(account.blocked_balance).context("Blocked balance too large for i64")?;
        let total = account
            .available_balance
            .checked_add(blocked_i64)
            .context("Total balance overflow")?;
        let row = ClientRow {
            client: client_id,
            available: i64_to_decimal(account.available_balance)?,
            held: u64_to_decimal(account.blocked_balance)?,
            total: i64_to_decimal(total)?,
            locked: account.locked,
        };
        wtr.serialize(row).context("Failed to write record")?;
    }

    wtr.flush().context("Failed to flush CSV writer")?;
    Ok(())
}

fn print_usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run <transactions.csv>    Process transactions file");
    eprintln!("  cargo run generate <num_lines>  Generate test transactions");
}

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().collect();

    match args.get(1).map(|s| s.as_str()) {
        Some("generate") => {
            let num_lines: u32 = args
                .get(2)
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| anyhow::anyhow!("generate requires a valid number of lines"))?;

            generator::generate(num_lines);
        }
        Some(path) if std::path::Path::new(path).exists() => {
            let file = std::fs::File::open(path)
                .with_context(|| format!("Failed to open CSV file: {}", path))?;
            let accounts = process_csv(file)?;
            write_accounts_csv(accounts, std::io::stdout())?
        }
        Some(arg) => {
            anyhow::bail!("'{}' is not a valid file or command", arg);
        }
        None => {
            print_usage();
            anyhow::bail!("No arguments provided");
        }
    }
    Ok(())
}
