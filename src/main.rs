mod generator;

use anyhow::Context;
use rust_decimal::prelude::ToPrimitive;

const SCALE: u32 = 4;
const PRECISION: u64 = 10_u64.pow(SCALE);

// CSV column indices: type,client,tx,amount
const COL_TYPE: usize = 0;
const COL_CLIENT: usize = 1;
const COL_TX: usize = 2;
const COL_AMOUNT: usize = 3;

// code does not compile with if consts are not what we expect :)
const _: () = assert!(SCALE == 4, "SCALE must be exactly 4 decimal places");
const _: () = assert!(PRECISION == 10_000, "PRECISION must be exactly 10_000");
const _: () = assert!(COL_TYPE == 0, "COL_TYPE must be 0");
const _: () = assert!(COL_CLIENT == 1, "COL_CLIENT must be 1");
const _: () = assert!(COL_TX == 2, "COL_TX must be 2");
const _: () = assert!(COL_AMOUNT == 3, "COL_AMOUNT must be 3");

trait HashMapInsertUniqueExt<K, V> {
    fn insert_unique(&mut self, key: K, value: V) -> Option<&mut V>;
}

impl<K: Eq + std::hash::Hash, V, S: std::hash::BuildHasher> HashMapInsertUniqueExt<K, V>
    for std::collections::HashMap<K, V, S>
{
    /// Inserts a key-value pair only if the key doesn't exist.
    /// Returns Some(&mut value) on success, None if key already existed.
    fn insert_unique(&mut self, key: K, value: V) -> Option<&mut V> {
        match self.entry(key) {
            std::collections::hash_map::Entry::Vacant(e) => Some(e.insert(value)),
            std::collections::hash_map::Entry::Occupied(_) => None,
        }
    }
}

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

enum TxKind {
    Deposit,
    Withdrawal,
    Dispute,
    Resolve,
    Chargeback,
}

impl std::str::FromStr for TxKind {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "deposit" => Ok(TxKind::Deposit),
            "withdrawal" => Ok(TxKind::Withdrawal),
            "dispute" => Ok(TxKind::Dispute),
            "resolve" => Ok(TxKind::Resolve),
            "chargeback" => Ok(TxKind::Chargeback),
            _ => anyhow::bail!("Unknown transaction type: {}", s),
        }
    }
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
    accounts: &mut rustc_hash::FxHashMap<u16, Account>,
    deposits: &mut rustc_hash::FxHashMap<u32, Deposit>,
    withdrawals: &mut rustc_hash::FxHashMap<u32, u64>,
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

fn process_csv<R: std::io::Read>(reader: R) -> anyhow::Result<rustc_hash::FxHashMap<u16, Account>> {
    let mut rdr = csv::ReaderBuilder::new()
        .trim(csv::Trim::None)
        .from_reader(reader);

    let mut accounts: rustc_hash::FxHashMap<u16, Account> = rustc_hash::FxHashMap::default();
    let mut deposits: rustc_hash::FxHashMap<u32, Deposit> = rustc_hash::FxHashMap::default();
    let mut withdrawals: rustc_hash::FxHashMap<u32, u64> = rustc_hash::FxHashMap::default();

    for (line_num, result) in rdr.records().enumerate() {
        let line = line_num + 2; // +1 for 0-index, +1 for header
        let record = result.with_context(|| format!("Failed to parse row {}", line))?;

        let kind: TxKind = record
            .get(COL_TYPE)
            .with_context(|| format!("Missing type field at line {}", line))?
            .trim()
            .parse()
            .with_context(|| format!("Invalid transaction type at line {}", line))?;
        let client: u16 = record
            .get(COL_CLIENT)
            .with_context(|| format!("Missing client field at line {}", line))?
            .trim()
            .parse()
            .with_context(|| format!("Invalid client ID at line {}", line))?;
        let tx_id: u32 = record
            .get(COL_TX)
            .with_context(|| format!("Missing tx field at line {}", line))?
            .trim()
            .parse()
            .with_context(|| format!("Invalid transaction ID at line {}", line))?;

        let amount: Option<rust_decimal::Decimal> = {
            let s = record.get(COL_AMOUNT).unwrap_or("").trim();
            if s.is_empty() {
                None
            } else {
                Some(
                    s.parse()
                        .with_context(|| format!("Invalid amount at line {}", line))?,
                )
            }
        };

        let tx = match kind {
            TxKind::Deposit => {
                let amount_dec =
                    amount.with_context(|| format!("Deposit missing amount at line {}", line))?;
                let amount = decimal_to_u64(amount_dec)
                    .with_context(|| format!("Invalid deposit amount at line {}", line))?;
                Tx {
                    account_id: client,
                    action: TxAction::Deposit { tx_id, amount },
                }
            }
            TxKind::Withdrawal => {
                let amount_dec = amount
                    .with_context(|| format!("Withdrawal missing amount at line {}", line))?;
                let amount = decimal_to_u64(amount_dec)
                    .with_context(|| format!("Invalid withdrawal amount at line {}", line))?;
                Tx {
                    account_id: client,
                    action: TxAction::Withdrawal { tx_id, amount },
                }
            }
            TxKind::Dispute => Tx {
                account_id: client,
                action: TxAction::Dispute { tx_id },
            },
            TxKind::Resolve => Tx {
                account_id: client,
                action: TxAction::Resolve { tx_id },
            },
            TxKind::Chargeback => Tx {
                account_id: client,
                action: TxAction::Chargeback { tx_id },
            },
        };

        process(&mut accounts, &mut deposits, &mut withdrawals, tx)
            .with_context(|| format!("Failed to process transaction at line {}", line))?;
    }

    Ok(accounts)
}

fn write_accounts_csv<W: std::io::Write>(
    accounts: rustc_hash::FxHashMap<u16, Account>,
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

#[cfg(test)]
mod tests {
    use super::HashMapInsertUniqueExt;

    const PRECISION: i64 = 10_000;
    const PRECISION_U64: u64 = 10_000;

    #[test]
    fn insert_unique_returns_some_on_new_key() {
        let mut map: std::collections::HashMap<u32, &str> = std::collections::HashMap::new();
        let result = map.insert_unique(1, "value");
        assert!(result.is_some());
        assert_eq!(map.get(&1), Some(&"value"));
    }

    #[test]
    fn insert_unique_returns_none_on_existing_key() {
        let mut map: std::collections::HashMap<u32, &str> = std::collections::HashMap::new();
        map.insert(1, "first");
        let result = map.insert_unique(1, "second");
        assert!(result.is_none());
        assert_eq!(map.get(&1), Some(&"first")); // original value unchanged
    }

    #[test]
    fn insert_unique_returns_mutable_reference() {
        let mut map: std::collections::HashMap<u32, String> = std::collections::HashMap::new();
        let result = map.insert_unique(1, String::from("value"));
        if let Some(v) = result {
            v.push_str("_modified");
        }
        assert_eq!(map.get(&1), Some(&String::from("value_modified")));
    }

    fn try_run(
        txs: Vec<super::Tx>,
    ) -> anyhow::Result<(
        rustc_hash::FxHashMap<u16, super::Account>,
        rustc_hash::FxHashMap<u32, super::Deposit>,
    )> {
        let mut accounts = rustc_hash::FxHashMap::default();
        let mut deposits = rustc_hash::FxHashMap::default();
        let mut withdrawals: rustc_hash::FxHashMap<u32, u64> = rustc_hash::FxHashMap::default();
        for tx in txs {
            super::process(&mut accounts, &mut deposits, &mut withdrawals, tx)?;
        }
        Ok((accounts, deposits))
    }

    fn run(
        txs: Vec<super::Tx>,
    ) -> (
        rustc_hash::FxHashMap<u16, super::Account>,
        rustc_hash::FxHashMap<u32, super::Deposit>,
    ) {
        try_run(txs).unwrap()
    }

    fn run_err(txs: Vec<super::Tx>) -> anyhow::Error {
        match try_run(txs) {
            Ok(_) => panic!("Expected transaction processing to fail"),
            Err(e) => e,
        }
    }

    fn deposit(account_id: u16, tx_id: u32, amount: i64) -> super::Tx {
        super::Tx {
            account_id,
            action: super::TxAction::Deposit {
                tx_id,
                amount: amount as u64,
            },
        }
    }

    fn withdrawal(account_id: u16, tx_id: u32, amount: i64) -> super::Tx {
        super::Tx {
            account_id,
            action: super::TxAction::Withdrawal {
                tx_id,
                amount: amount as u64,
            },
        }
    }

    fn dispute(account_id: u16, tx_id: u32) -> super::Tx {
        super::Tx {
            account_id,
            action: super::TxAction::Dispute { tx_id },
        }
    }

    fn resolve(account_id: u16, tx_id: u32) -> super::Tx {
        super::Tx {
            account_id,
            action: super::TxAction::Resolve { tx_id },
        }
    }

    fn chargeback(account_id: u16, tx_id: u32) -> super::Tx {
        super::Tx {
            account_id,
            action: super::TxAction::Chargeback { tx_id },
        }
    }

    #[test]
    fn rejects_more_than_4_decimal_places() {
        use std::str::FromStr;
        assert!(super::decimal_to_u64(rust_decimal::Decimal::from_str("1.0000").unwrap()).is_ok());
        assert!(
            super::decimal_to_u64(rust_decimal::Decimal::from_str("1.00001").unwrap()).is_err()
        );
        assert!(
            super::decimal_to_u64(rust_decimal::Decimal::from_str("1.12345").unwrap()).is_err()
        );
    }

    // Deposit Tests

    #[test]
    fn deposit_increases_available_balance() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 2, 50 * PRECISION),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 150 * PRECISION);
    }

    #[test]
    fn no_deposit_when_locked() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            deposit(1, 2, 50 * PRECISION),
            chargeback(1, 1),
            deposit(1, 3, 51 * PRECISION),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 50 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
        assert!(acc.locked);
    }

    #[test]
    fn duplicate_deposit_same_amount_is_idempotent() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 1, 100 * PRECISION), // same amount - idempotent
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
    }

    #[test]
    fn duplicate_deposit_different_amount_is_error() {
        let result = try_run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 1, 50 * PRECISION), // different amount - error
        ]);
        assert!(result.is_err());
    }

    // Withdrawal Tests

    #[test]
    fn withdrawal_decreases_available_balance() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 40 * PRECISION),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 60 * PRECISION);
    }

    #[test]
    fn no_withdrawal_when_insufficient_balance() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 50 * PRECISION),
            withdrawal(1, 2, 100 * PRECISION),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 50 * PRECISION);
    }

    #[test]
    fn no_withdrawal_when_unknown_account() {
        let (accounts, _) = run(vec![withdrawal(1, 1, 100 * PRECISION)]);
        assert!(accounts.get(&1).is_none());
    }

    #[test]
    fn no_withdrawal_on_locked_account() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            chargeback(1, 1),
            withdrawal(1, 2, 50 * PRECISION),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert!(acc.locked);
    }

    #[test]
    fn can_withdrawal_when_only_disputed() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 2, 50 * PRECISION),
            dispute(1, 1),
            withdrawal(1, 3, 50 * PRECISION),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn duplicate_withdrawal_same_amount_is_idempotent() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 40 * PRECISION),
            withdrawal(1, 2, 40 * PRECISION), // same amount - idempotent
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 60 * PRECISION);
    }

    #[test]
    fn duplicate_withdrawal_different_amount_is_error() {
        let result = try_run(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 40 * PRECISION),
            withdrawal(1, 2, 30 * PRECISION), // different amount - error
        ]);
        assert!(result.is_err());
    }

    // Dispute Tests

    #[test]
    fn dispute_moves_funds_to_blocked() {
        let (accounts, _) = run(vec![deposit(1, 1, 100 * PRECISION), dispute(1, 1)]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn ignores_dispute_when_unkown_ref_id() {
        let (accounts, _) = run(vec![deposit(1, 1, 100 * PRECISION), dispute(1, 999)]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
    }

    #[test]
    fn no_dispute_when_account_id_mismatch() {
        let (accounts, _) = run(vec![deposit(1, 1, 100 * PRECISION), dispute(2, 1)]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
    }

    #[test]
    fn no_dispute_when_already_disputed() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 2, 50 * PRECISION),
            dispute(1, 1),
            dispute(1, 1), // duplicate dispute
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 50 * PRECISION);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn dispute_with_partial_withdrawal_creates_negative_balance() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 60 * PRECISION),
            dispute(1, 1),
        ]);
        let acc = accounts.get(&1).unwrap();
        // available = 40 - 100 = -60 (negative due to dispute)
        assert_eq!(acc.available_balance, -60 * PRECISION);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn no_dispute_on_locked_account() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 2, 50 * PRECISION),
            dispute(1, 1),
            chargeback(1, 1),
            dispute(1, 2),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 50 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
        assert!(acc.locked);
    }

    // Resolve Tests

    #[test]
    fn resolve_moves_funds_back_to_available() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            resolve(1, 1),
        ]);
        let acc = accounts.get(&1).unwrap();

        assert_eq!(acc.available_balance, 100 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
    }

    #[test]
    fn no_resolve_when_tx_not_found() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            resolve(1, 999),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn no_resolve_when_account_id_mismatch() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            resolve(2, 1),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn no_resolve_when_not_under_dispute() {
        let (accounts, _) = run(vec![deposit(1, 1, 100 * PRECISION), resolve(1, 1)]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
    }

    #[test]
    fn no_resolve_on_locked_account() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 2, 50 * PRECISION),
            dispute(1, 1),
            dispute(1, 2),
            chargeback(1, 1),
            resolve(1, 2),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 50 * PRECISION_U64);
        assert!(acc.locked);
    }

    #[test]
    fn double_resolve_is_noop() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            resolve(1, 1),
            resolve(1, 1),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
    }

    // Chargeback Tests

    #[test]
    fn chargeback_removes_blocked_and_locks() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            chargeback(1, 1),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 0);
        assert!(acc.locked);
    }

    #[test]
    fn no_chargeback_when_tx_not_found() {
        let (accounts, _) = run(vec![deposit(1, 1, 100 * PRECISION), chargeback(1, 999)]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
        assert!(!acc.locked);
    }

    #[test]
    fn no_chargeback_when_account_id_mismatch() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            dispute(1, 1),
            chargeback(2, 1),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
        assert!(!acc.locked);
    }

    #[test]
    fn no_chargeback_when_not_under_dispute() {
        let (accounts, _) = run(vec![deposit(1, 1, 100 * PRECISION), chargeback(1, 1)]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 100 * PRECISION);
        assert!(!acc.locked);
    }

    #[test]
    fn no_chargeback_on_locked_account() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            deposit(1, 2, 50 * PRECISION),
            dispute(1, 1),
            dispute(1, 2),
            chargeback(1, 1),
            chargeback(1, 2),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 50 * PRECISION_U64);
        assert!(acc.locked);
    }

    // Negative Balance Tests (disputes after partial withdrawal)

    #[test]
    fn dispute_allows_negative_available_balance() {
        // User deposits 100, withdraws 60, then deposit is disputed
        // Available should go negative: 40 - 100 = -60
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 60 * PRECISION),
            dispute(1, 1),
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, -60 * PRECISION);
        assert_eq!(acc.blocked_balance, 100 * PRECISION_U64);
    }

    #[test]
    fn postponed_chargeback_scenario() {
        let (accounts, _) = run(vec![
            deposit(1, 1, 10 * PRECISION),
            withdrawal(1, 2, 5 * PRECISION),
            dispute(1, 1),                // available = -5
            deposit(1, 3, 5 * PRECISION), // available = 5
            chargeback(1, 1),             // available = 0, blocked = 0, locked
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 0);
        assert!(acc.locked);
    }

    #[test]
    fn chargeback_fails_when_insufficient_funds() {
        let err = run_err(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 80 * PRECISION),
            dispute(1, 1),
            chargeback(1, 1),
        ]);
        assert!(
            err.to_string().contains("Insufficient funds"),
            "Expected 'Insufficient funds' error, got: {}",
            err
        );
    }

    #[test]
    fn resolve_after_negative_available_restores_balance() {
        // User deposits 100, withdraws 60, dispute (available=-60), then resolve
        // After resolve: available = -60 + 100 = 40
        let (accounts, _) = run(vec![
            deposit(1, 1, 100 * PRECISION),
            withdrawal(1, 2, 60 * PRECISION),
            dispute(1, 1), // available = -60, held = 100
            resolve(1, 1), // available =  40, held = 0
        ]);
        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 40 * PRECISION);
        assert_eq!(acc.blocked_balance, 0);
    }

    fn load_fixture(name: &str) -> rustc_hash::FxHashMap<u16, super::Account> {
        let path = format!("fixtures/{}.csv", name);
        let file =
            std::fs::File::open(&path).unwrap_or_else(|e| panic!("Failed to open {}: {}", path, e));
        super::process_csv(file).unwrap_or_else(|e| panic!("Failed to process {}: {}", path, e))
    }

    fn load_fixture_err(name: &str) -> anyhow::Error {
        let path = format!("fixtures/{}.csv", name);
        let file =
            std::fs::File::open(&path).unwrap_or_else(|e| panic!("Failed to open {}: {}", path, e));
        match super::process_csv(file) {
            Ok(_) => panic!("Expected fixture {} to fail", name),
            Err(e) => e,
        }
    }

    #[test]
    fn fixture_basic() {
        let accounts = load_fixture("basic");

        let acc1 = accounts.get(&1).unwrap();
        assert_eq!(acc1.available_balance, 556001);
        assert_eq!(acc1.blocked_balance, 0);
        assert!(!acc1.locked);

        let acc2 = accounts.get(&2).unwrap();
        assert_eq!(acc2.available_balance, 1950200);
        assert_eq!(acc2.blocked_balance, 0);
        assert!(!acc2.locked);
    }

    #[test]
    fn fixture_chargeback() {
        let accounts = load_fixture("chargeback");

        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 500000);
        assert_eq!(acc.blocked_balance, 0);
        assert!(acc.locked);
    }

    #[test]
    fn fixture_insufficient_funds() {
        let accounts = load_fixture("insufficient_funds");

        let acc1 = accounts.get(&1).unwrap();
        assert_eq!(acc1.available_balance, 500000);
        assert!(!acc1.locked);

        let acc2 = accounts.get(&2).unwrap();
        assert_eq!(acc2.available_balance, 200000);
        assert!(!acc2.locked);
    }

    #[test]
    fn fixture_resolve() {
        let accounts = load_fixture("resolve");

        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 500000);
        assert_eq!(acc.blocked_balance, 0);
        assert!(!acc.locked);
    }

    #[test]
    fn fixture_negative_balance() {
        let err = load_fixture_err("negative_balance");
        let err_chain = format!("{:?}", err);
        assert!(
            err_chain.contains("Insufficient funds"),
            "Expected 'Insufficient funds' error, got: {}",
            err_chain
        );
    }

    #[test]
    fn fixture_chargeback_no_funds() {
        let err = load_fixture_err("chargeback_no_funds");
        let err_chain = format!("{:?}", err);
        assert!(
            err_chain.contains("Insufficient funds"),
            "Expected 'Insufficient funds' error, got: {}",
            err_chain
        );
    }

    #[test]
    fn fixture_postponed_chargeback() {
        let accounts = load_fixture("postponed_chargeback");

        let acc = accounts.get(&1).unwrap();
        assert_eq!(acc.available_balance, 0);
        assert_eq!(acc.blocked_balance, 0);
        assert!(acc.locked);
    }

    #[test]
    fn fixture_whitespace_variations() {
        let accounts = load_fixture("whitespace_variations");

        let acc1 = accounts.get(&1).unwrap();
        assert_eq!(acc1.available_balance, 750000);

        let acc2 = accounts.get(&2).unwrap();
        assert_eq!(acc2.available_balance, 505000);
    }
}
