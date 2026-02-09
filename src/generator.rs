use rand::Rng;
use std::collections::HashMap;
use std::io::{self, BufWriter, Write};

enum TxType {
    Deposit,
    Withdrawal,
    Dispute,
    Resolve,
    Chargeback,
}

pub fn generate(num_lines: u32) {
    let num_clients: u16 = 100;
    let mut rng = rand::rng();
    let mut writer = BufWriter::new(io::stdout().lock());

    writeln!(writer, "type,client,tx,amount").unwrap();

    // Track deposits per client for valid references
    let mut client_deposits: HashMap<u16, Vec<u32>> = HashMap::new();
    let mut client_disputed: HashMap<u16, Vec<u32>> = HashMap::new();
    let mut next_tx_id: u32 = 1;

    // Weights: deposit 40%, withdrawal 30%, dispute 15%, resolve 10%, chargeback 5%
    const DEPOSIT_THRESHOLD: u32 = 40;
    const WITHDRAWAL_THRESHOLD: u32 = 70;
    const DISPUTE_THRESHOLD: u32 = 85;
    const RESOLVE_THRESHOLD: u32 = 95;

    // 30% chance of generating chaotic/invalid data
    const CHAOS_PROBABILITY: u32 = 30;

    for _ in 0..num_lines {
        let client_id: u16 = rng.random_range(1..=num_clients);
        let is_chaotic = rng.random_range(0..100) < CHAOS_PROBABILITY;

        let roll: u32 = rng.random_range(0..100);
        let tx_type = if roll < DEPOSIT_THRESHOLD {
            TxType::Deposit
        } else if roll < WITHDRAWAL_THRESHOLD {
            TxType::Withdrawal
        } else if roll < DISPUTE_THRESHOLD {
            TxType::Dispute
        } else if roll < RESOLVE_THRESHOLD {
            TxType::Resolve
        } else {
            TxType::Chargeback
        };

        match tx_type {
            TxType::Deposit => {
                let tx_id = next_tx_id;
                next_tx_id += 1;
                let amount: f64 = rng.random_range(1.0..=10000.0);
                client_deposits.entry(client_id).or_default().push(tx_id);
                writeln!(writer, "deposit,{},{},{:.4}", client_id, tx_id, amount).unwrap();
            }
            TxType::Withdrawal => {
                let tx_id = next_tx_id;
                next_tx_id += 1;
                // Chaotic: sometimes withdraw huge amounts that will likely fail
                let amount: f64 = if is_chaotic {
                    rng.random_range(50000.0..=100000.0)
                } else {
                    rng.random_range(1.0..=500.0)
                };
                writeln!(writer, "withdrawal,{},{},{:.4}", client_id, tx_id, amount).unwrap();
            }
            TxType::Dispute => {
                if is_chaotic {
                    // Chaotic: use random tx_id (likely invalid or wrong client)
                    let fake_tx_id = if next_tx_id > 1 {
                        rng.random_range(1..next_tx_id * 2)
                    } else {
                        999999
                    };
                    writeln!(writer, "dispute,{},{},", client_id, fake_tx_id).unwrap();
                } else {
                    // Valid dispute
                    let deposits = client_deposits.entry(client_id).or_default();
                    if deposits.is_empty() {
                        writeln!(writer, "dispute,{},{},", client_id, 999999).unwrap();
                    } else {
                        let idx = rng.random_range(0..deposits.len());
                        let tx_id = deposits.remove(idx);
                        client_disputed.entry(client_id).or_default().push(tx_id);
                        writeln!(writer, "dispute,{},{},", client_id, tx_id).unwrap();
                    }
                }
            }
            TxType::Resolve => {
                if is_chaotic {
                    // Chaotic: use random tx_id
                    let fake_tx_id = if next_tx_id > 1 {
                        rng.random_range(1..next_tx_id * 2)
                    } else {
                        999999
                    };
                    writeln!(writer, "resolve,{},{},", client_id, fake_tx_id).unwrap();
                } else {
                    // Valid resolve
                    let disputed = client_disputed.entry(client_id).or_default();
                    if disputed.is_empty() {
                        writeln!(writer, "resolve,{},{},", client_id, 999999).unwrap();
                    } else {
                        let idx = rng.random_range(0..disputed.len());
                        let tx_id = disputed.remove(idx);
                        client_deposits.entry(client_id).or_default().push(tx_id);
                        writeln!(writer, "resolve,{},{},", client_id, tx_id).unwrap();
                    }
                }
            }
            TxType::Chargeback => {
                if is_chaotic {
                    // Chaotic: use random tx_id
                    let fake_tx_id = if next_tx_id > 1 {
                        rng.random_range(1..next_tx_id * 2)
                    } else {
                        999999
                    };
                    writeln!(writer, "chargeback,{},{},", client_id, fake_tx_id).unwrap();
                } else {
                    // Valid chargeback
                    let disputed = client_disputed.entry(client_id).or_default();
                    if disputed.is_empty() {
                        writeln!(writer, "chargeback,{},{},", client_id, 999999).unwrap();
                    } else {
                        let idx = rng.random_range(0..disputed.len());
                        let tx_id = disputed.remove(idx);
                        writeln!(writer, "chargeback,{},{},", client_id, tx_id).unwrap();
                    }
                }
            }
        }
    }

    writer.flush().unwrap();
}
