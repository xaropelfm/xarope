# Xarope

This is xarope, a simple transaction processor payment system.

It reads a CSV of transactions and outputs CSV with the final state of all accounts.

## Usage

```bash
# Process a transactions file
cargo run -- transactions.csv > accounts.csv

# Generate test data
cargo run -- generate 1000 > transactions.csv
```

## AI Usage

In "real life", it's rare to have such a detailed spec in text. It's often the job of the developer to create the spec from a more high-level description of the problem.
Therefore, I didn't think it was fair to feed the PDF to Claude and ask it to oneshot it for me.

Instead, I read the spec, extracted requirements, and wrote the core logic myself to ensure **I** understood the problem:
* What are the requirements?
* How can I solve this?
* What is unclear? How will I deal with that?

I wrote a simple solution to the problem by hand: one function that receives the data structures for accounts and transactions, and processes them according to the rules. No CSV handling.
Then I started to iterate with the help of Claude to improve my productivity.

I used Claude to:
* Write tests
* Write a CSV generator to produce big inputs for profiling
* Help me reason about the consequences of my design decisions.
* Help me with benchmarks and optimizations.

## Time spent

I've spent more than the 2 to 3 hours mentioned in the PDF. Basically a Friday night, Sunday afternoon, and a little bit of my Monday morning. I would say I've spent around 10 hours on this project. I had the time available, enjoyed the problem and want the job, so I don't see why not put in the work :)

## Git

I usually use git while developing like a madman. Confusing commit messages, messy diffs, and so on. But when I want someone to review my code, I like to rewrite history to make it easier to review. This approach was used here, so the git history is clean and each commit has a clear purpose.

## Paranoia

As you will see, paranoia is a recurring theme here. I think that the right amount is perfectly reasonable on a financial application :)

## Decisions and thought process

### Disputes with insufficient available balance (Negative Balances)

Consider this scenario:
```csv
type,client,tx,amount
deposit,1,1,100
withdrawal,1,2,50
dispute,1,1
deposit,1,3,50
chargeback,1,1
```

At dispute time, the account has only 50 available but the disputed deposit was for 100. The spec requires that "the client's available funds should decrease by the amount disputed".

Although I think this is bad modeling, **I've decided to allow the available balance to go negative during disputes.**

My reasoning is that I wouldn't want to dismiss a dispute just because the user doesn't have enough available funds at the moment. I also don't want to abort execution, since this is a scenario that can happen in real life. The important thing seems to be balances at the time of chargeback, not at dispute.

A negative `available` represents a liability during the dispute process. As I mentioned, I think this is kind of bad... I would rather not have negative balances and instead add an `owed_amount` to represent this. Given the limitations of the spec, I didn't pursue this approach.

### Chargebacks require sufficient funds

The consequence of the above decision is that now we need to decide what happens if there is not enough money to cover the chargeback.

```csv
type,client,tx,amount
deposit,1,1,100
withdrawal,1,2,100
dispute,1,1
chargeback,1,1
```

In Brazil, we have this dispute/chargeback feature in the central bank's payment system (PIX) and in this scenario, the chargeback can be partially accepted, meaning that if there's some balance that can be recovered, it will be.

The spec is not clear on how to handle this scenario. My approach in "real life" would be the same as in this project: avoid processing what I'm unsure about rather than making assumptions that could be wrong and lead to incorrect behavior.

### Idempotency

The spec says that txids are unique. But don't trust, verify.

Duplicate deposits and withdrawals are handled as follows:
- **Same txid, same amount**: Idempotent - noop.
- **Same txid, different amount**: Error - data corruption.

Duplicate disputes, resolves and chargebacks are handled similarly, but don't require amount matching.

### Misc

- **Compile time asserts**: Constants have compile-time assertions to ensure they meet the spec's requirements (e.g., SCALE must be 4, PRECISION must be 10000). Wrong values don't even compile, which I think is kind of overkill for this project but cool.
- **Overflow protection:** All balance operations use `checked_add()` and explicit bounds checking. Transactions that would overflow cause the application to abort with an error.
- **Fixed-point arithmetic:** Amounts are stored as integers to avoid floating-point precision issues. Available balance uses `i64` (to allow negative balances during disputes), while held balance and transaction amounts use `u64`. The `Decimal` type is only used at I/O boundaries.

### Tests

#### Unit tests

Written by Claude, verified by me. Tests are organized by transaction type covering business logic scenarios.

#### Fixtures

Hand-solved test cases in `fixtures/` used to understand the problem and validate behavior.

#### Test data generator

The `generate` command creates randomized CSV data with weighted transaction distribution and "chaotic" edge cases (invalid references, excessive withdrawals, etc.).

```bash
cargo run --release -- generate 1000000 > large_test.csv
```

## Performance

I did time benchmarks, CPU and memory profiling to help guide optimizations.

Profiling data is available in the `profiling/` directory.

### Benchmark Environment

| Component | Specification |
|-----------|---------------|
| CPU | AMD Ryzen 9 9950X 16-Core (32 threads) |
| Memory | 64 GB DDR5 |
| OS | Linux 6.12.68 (NixOS) |
| Rust | 1.92.0 (release profile) |

### Results (100M transactions)

```bash
➜ hyperfine --warmup 3 './target/release/xarope samples/100M.csv'
```

| Version | Time | Key Optimization |
|---------|------|------------------|
| V1 | 21.6s | |
| V2 | 12.8s | Drop serde, zero-allocation trimming |
| V3 | 10.9s | FxHash (faster hashing) |
| V4 | 9.9s | Zero-copy ByteRecord |
