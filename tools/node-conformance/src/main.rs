//! Generates the Borsh conformance fixtures for `near-lean/node` from the pinned nearcore
//! crates. `node-conformance-fixtures <out dir>` writes one `<Type>.jsonl` per type and a
//! `manifest.json`; the output is a pure function of the code and the locked dependencies.

mod chain;
mod chain_fam;
mod epoch_fam;
mod fam;
mod rng;
mod sigs;
mod storage_fam;
mod sync_fam;
mod stateless_fam;
mod values;

use borsh::BorshDeserialize;
use fam::{hex, Fam, Manifest};
use rng::G;
use near_crypto::KeyType;
use near_primitives::account::{Account, AccountContract};
use near_primitives::action::delegate::{NonDelegateAction, SignedDelegateAction};
use near_primitives::action::Action;
use near_primitives::hash::CryptoHash;
use near_primitives::transaction::{SignedTransaction, Transaction};
use near_primitives_core::version::PROTOCOL_VERSION;
use std::collections::BTreeMap;
use std::path::PathBuf;
use values::*;

pub const SEED: u64 = 0x4e45_4152_0000_0001;
const REFERENCE: &str = include_str!("../../../near-lean/runtime/reference.json");

fn main() {
    let out_dir = PathBuf::from(
        std::env::args().nth(1).expect("usage: node-conformance-fixtures <out dir> [signatures file]"),
    );
    let signatures = std::env::args()
        .nth(2)
        .map(PathBuf::from)
        .unwrap_or_else(|| out_dir.join("../signatures.jsonl"));
    let reference: serde_json::Value = serde_json::from_str(REFERENCE).unwrap();
    let pinned = reference["reference_protocol_version"].as_u64().unwrap();
    assert_eq!(PROTOCOL_VERSION as u64, 86, "the oracle crates must be protocol 86");
    assert_eq!(PROTOCOL_VERSION as u64, pinned, "oracle protocol differs from reference.json");
    std::fs::create_dir_all(&out_dir).unwrap();
    let mut m = Manifest::new(PROTOCOL_VERSION as u64, reference["release"].as_str().unwrap(), SEED);

    primitives(&mut m, &out_dir);
    keys_and_accounts(&mut m, &out_dir);
    actions(&mut m, &out_dir);
    transactions(&mut m, &out_dir);
    receipts(&mut m, &out_dir);
    errors(&mut m, &out_dir);
    outcomes(&mut m, &out_dir);
    chain_fam::chain(&mut m, &out_dir);
    stateless_fam::stateless(&mut m, &out_dir);
    epoch_fam::epoch(&mut m, &out_dir);
    sync_fam::sync(&mut m, &out_dir);
    storage_fam::storage(&mut m, &out_dir);

    m.write(&out_dir);
    sigs::write(&signatures);
}

fn primitives(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<bool>::new("Bool", SEED);
    f.edge("false", false);
    f.edge("true", true);
    for (n, b) in [("2", vec![2u8]), ("255", vec![255]), ("empty", vec![])] {
        f.raw(n, b);
    }
    f.finish(m, dir);

    let mut f = Fam::<u128>::new("U128", SEED);
    for (n, v) in [("zero", 0u128), ("one", 1), ("u64max", u64::MAX as u128),
        ("2^64", 1u128 << 64), ("max", u128::MAX), ("2^127", 1u128 << 127)] {
        f.edge(n, v);
    }
    f.rand(30, |g| g.balance().as_yoctonear());
    f.raw("short", vec![1; 15]);
    f.finish(m, dir);

    let mut f = Fam::<String>::new("String", SEED);
    for (n, s) in [("empty", ""), ("ascii", "hello"), ("two-byte", "h\u{e9}llo"), ("three-byte", "\u{20ac}"),
        ("four-byte", "\u{1F600}"), ("max-scalar", "\u{10FFFF}"), ("nul", "a\0b")] {
        f.edge(n, s.to_string());
    }
    f.edge("long", "x".repeat(5000));
    f.rand(30, |g| g.string(40));
    for (n, b) in [
        ("bad-continuation", vec![1, 0, 0, 0, 0xFF]),
        ("lone-continuation", vec![1, 0, 0, 0, 0x80]),
        ("overlong-nul", vec![2, 0, 0, 0, 0xC0, 0x80]),
        ("overlong-3", vec![3, 0, 0, 0, 0xE0, 0x80, 0x80]),
        ("surrogate", vec![3, 0, 0, 0, 0xED, 0xA0, 0x80]),
        ("above-max", vec![4, 0, 0, 0, 0xF4, 0x90, 0x80, 0x80]),
        ("f5", vec![4, 0, 0, 0, 0xF5, 0x80, 0x80, 0x80]),
        ("cut-sequence", vec![2, 0, 0, 0, 0xC3, 0x28]),
        ("length-past-end", vec![9, 0, 0, 0, b'a']),
        ("huge-length", vec![0xFF, 0xFF, 0xFF, 0xFF, b'a']),
        ("max-surrogate-low", vec![3, 0, 0, 0, 0xED, 0x9F, 0xBF]),
        ("max-3-byte", vec![3, 0, 0, 0, 0xEF, 0xBF, 0xBF]),
        ("min-4-byte", vec![4, 0, 0, 0, 0xF0, 0x90, 0x80, 0x80]),
        ("below-min-4-byte", vec![4, 0, 0, 0, 0xF0, 0x8F, 0xBF, 0xBF]),
    ] {
        f.raw(n, b);
    }
    f.finish(m, dir);

    let mut f = Fam::<Vec<u8>>::new("Bytes", SEED);
    f.edge("empty", vec![]);
    f.edge("one", vec![7]);
    f.edge("4k", (0..4096).map(|i| i as u8).collect());
    f.rand(20, |g| g.bytes(64));
    f.raw("huge-length", vec![0xFF, 0xFF, 0xFF, 0xFF]);
    f.finish(m, dir);

    let mut f = Fam::<Option<u64>>::new("OptionU64", SEED);
    f.edge("none", None);
    f.edge("some", Some(u64::MAX));
    f.rand(10, |g| g.opt(|g| g.u64()));
    for (n, b) in [("tag2", vec![2u8]), ("tag255", vec![255, 0, 0, 0, 0, 0, 0, 0, 0]), ("short", vec![1, 0, 0])] {
        f.raw(n, b);
    }
    f.finish(m, dir);

    // A BTreeMap decodes without an order check: unsorted input is accepted and re-encodes
    // sorted, and a repeated key keeps its last value.
    let mut f = Fam::<std::collections::BTreeMap<Vec<u8>, Vec<u8>>>::new("BytesMap", SEED);
    f.edge("empty", Default::default());
    f.edge("two", [(vec![1], vec![2]), (vec![1, 0], vec![])].into_iter().collect());
    f.rand(20, |g| (0..g.below(5)).map(|_| (g.bytes(6), g.bytes(10))).collect());
    let entry = |k: &[u8], v: &[u8]| {
        let mut b = (k.len() as u32).to_le_bytes().to_vec();
        b.extend(k);
        b.extend((v.len() as u32).to_le_bytes());
        b.extend(v);
        b
    };
    let map = |es: &[Vec<u8>]| {
        let mut b = (es.len() as u32).to_le_bytes().to_vec();
        for e in es {
            b.extend(e);
        }
        b
    };
    f.raw("unsorted", map(&[entry(&[2], &[]), entry(&[1], &[9])]));
    f.raw("duplicate", map(&[entry(&[1], &[1]), entry(&[1], &[2])]));
    f.raw("prefix-order", map(&[entry(&[1, 0], &[]), entry(&[1], &[])]));
    f.finish(m, dir);
}

fn keys_and_accounts(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<CryptoHash>::new("CryptoHash", SEED);
    f.edge("zero", CryptoHash::default());
    f.edge("ones", CryptoHash([255; 32]));
    f.rand(30, |g| g.hash());
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::types::AccountId>::new("AccountId", SEED);
    for (n, a) in account_ids() {
        f.edge(&n, a);
    }
    f.edge("max-len", "a".repeat(64).parse().unwrap());
    f.edge("min-len", "ab".parse().unwrap());
    f.rand(40, |g| g.account());
    let s = |t: &str| {
        let mut b = (t.len() as u32).to_le_bytes().to_vec();
        b.extend(t.as_bytes());
        b
    };
    let long = "a".repeat(65);
    let longer = "a".repeat(100);
    for (i, t) in ["", "a", "A", "aA", "a b", "a..b", ".ab", "ab.", "-ab", "ab-", "a--b", "a__b",
        "a._b", "ab@c", "\u{e9}\u{e9}", "a\0", "Alice.near", &long, &longer, "0x", "a-.b", "a-b"]
        .iter().enumerate()
    {
        f.raw(&format!("probe-{i}"), s(t));
    }
    f.finish(m, dir);

    let mut f = Fam::<near_crypto::PublicKey>::new("PublicKey", SEED);
    for (n, ty) in [("ed25519", KeyType::ED25519), ("secp256k1", KeyType::SECP256K1), ("mldsa65", KeyType::MLDSA65)] {
        f.edge(n, pk_of(&mut G::new(SEED, n), ty));
        f.edge(&format!("{n}-empty"), near_crypto::PublicKey::empty(ty));
    }
    f.rand(30, |g| g.pk());
    f.raw("tag3", vec![3; 33]);
    f.raw("tag255", vec![255; 33]);
    f.finish(m, dir);

    let mut f = Fam::<near_crypto::Signature>::new("Signature", SEED);
    for (n, ty) in [("ed25519", KeyType::ED25519), ("secp256k1", KeyType::SECP256K1), ("mldsa65", KeyType::MLDSA65)] {
        f.edge(n, sig_of(&mut G::new(SEED, n), ty));
    }
    f.edge("ed25519-empty", near_crypto::Signature::empty(KeyType::ED25519));
    f.edge("mldsa65-empty", near_crypto::Signature::empty(KeyType::MLDSA65));
    f.rand(30, |g| g.sig());
    // The last byte of an Ed25519 signature must have its top three bits clear.
    for top in [0x00u8, 0x1F, 0x20, 0x40, 0x80, 0xE0, 0xFF] {
        let mut b = vec![0u8; 65];
        b[64] = top;
        f.raw(&format!("ed25519-last-{top:02x}"), b);
    }
    f.raw("tag3", vec![3; 65]);
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::account::AccessKey>::new("AccessKey", SEED);
    for i in 0..N_PERMISSION {
        f.edge(&format!("permission-{i}"), near_primitives::account::AccessKey {
            nonce: u64::MAX,
            permission: permission(&mut G::new(SEED, "ak"), i),
        });
    }
    f.rand(150, access_key);
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::account::AccessKeyPermission>::new("AccessKeyPermission", SEED);
    for i in 0..N_PERMISSION {
        f.edge(&format!("variant-{i}"), permission(&mut G::new(SEED, "perm"), i));
    }
    f.rand(30, |g| {
        let i = g.below(N_PERMISSION);
        permission(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::account::FunctionCallPermission>::new("FunctionCallPermission", SEED);
    f.edge("empty", near_primitives::account::FunctionCallPermission {
        allowance: None,
        receiver_id: String::new(),
        method_names: vec![],
    });
    f.rand(30, fc_permission);
    f.finish(m, dir);

    let mut f = Fam::<AccountContract>::new("AccountContract", SEED);
    for i in 0..N_CONTRACT {
        f.edge(&format!("variant-{i}"), contract(&mut G::new(SEED, "contract"), i));
    }
    f.rand(30, |g| {
        let i = g.below(N_CONTRACT);
        contract(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::global_contract::GlobalContractIdentifier>::new(
        "GlobalContractIdentifier", SEED);
    for i in 0..N_GLOBAL_ID {
        f.edge(&format!("variant-{i}"), id_ident(&mut G::new(SEED, "gid"), i));
    }
    f.rand(20, |g| {
        let i = g.below(N_GLOBAL_ID);
        id_ident(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::deterministic_account_id::DeterministicAccountStateInit>::new(
        "DeterministicAccountStateInit", SEED);
    f.rand(40, state_init);
    f.finish(m, dir);

    let mut f = Fam::<Account>::new("Account", SEED);
    let g = &mut G::new(SEED, "account");
    let (a, l) = (g.balance(), g.balance());
    f.edge("v1-no-contract", Account::new(a, l, AccountContract::None, 100));
    f.edge("v1-local", Account::new(a, l, AccountContract::Local(g.hash()), u64::MAX));
    f.edge("v2-global", Account::new(a, l, AccountContract::Global(g.hash()), 0));
    f.edge("v2-global-by-account", Account::new(a, l, AccountContract::GlobalByAccount(g.account()), 1));
    f.rand(150, |g| {
        let i = g.below(N_CONTRACT);
        let c = contract(g, i);
        // `u128::MAX` as a V1 amount would read back as the V2 sentinel.
        let amount = near_primitives::types::Balance::from_yoctonear(g.balance().as_yoctonear().min(u128::MAX - 1));
        Account::new(amount, g.balance(), c, g.u64())
    });
    // V2 with a contract that V1 could hold: only reachable by decoding.
    for tag in 0..4u8 {
        let mut b = u128::MAX.to_le_bytes().to_vec();
        b.push(0);
        b.extend(5u128.to_le_bytes());
        b.extend(6u128.to_le_bytes());
        b.extend(7u64.to_le_bytes());
        b.push(tag);
        b.extend([0xAB; 32]);
        if tag == 3 {
            b.truncate(b.len() - 32);
            b.extend([2, 0, 0, 0, b'a', b'b']);
        }
        f.raw(&format!("v2-contract-{tag}"), b);
    }
    let mut bad = u128::MAX.to_le_bytes().to_vec();
    bad.push(1);
    f.raw("bad-version", bad);
    f.finish(m, dir);
}

fn actions(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<Action>::new("Action", SEED);
    for i in 0..N_ACTION {
        f.edge(&format!("variant-{i}"), action(&mut G::new(SEED, "action"), i));
    }
    f.edge("deploy-max", Action::DeployContract(near_primitives::action::DeployContractAction {
        code: vec![0xA5; 20000],
    }));
    f.edge("create-account", Action::CreateAccount(near_primitives::action::CreateAccountAction {}));
    f.rand(300, rand_action);
    f.finish(m, dir);

    let mut f = Fam::<NonDelegateAction>::new("NonDelegateAction", SEED);
    for i in 0..N_BASE_ACTION {
        f.edge(&format!("variant-{i}"), NonDelegateAction::try_from(base_action(&mut G::new(SEED, "nda"), i)).unwrap());
    }
    f.rand(60, |g| {
        let i = g.below(N_BASE_ACTION);
        NonDelegateAction::try_from(base_action(g, i)).unwrap()
    });
    f.raw("delegate-tag", vec![8; 40]);
    f.raw("delegate-v2-tag", vec![14; 40]);
    f.finish(m, dir);

    let mut f = Fam::<SignedDelegateAction>::new("SignedDelegateAction", SEED);
    f.hash(|a: &SignedDelegateAction| vec![("hash", hex(&a.delegate_action.get_nep461_hash().0))]);
    f.rand(60, signed_delegate);
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::action::delegate::VersionedSignedDelegateAction>::new(
        "VersionedSignedDelegateAction", SEED);
    f.hash(|a: &near_primitives::action::delegate::VersionedSignedDelegateAction| {
        vec![("hash", hex(&a.delegate_action.get_nep461_hash().0))]
    });
    f.rand(60, signed_delegate_v2);
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::transaction::TransactionNonce>::new("TransactionNonce", SEED);
    for i in 0..N_NONCE {
        f.edge(&format!("variant-{i}"), nonce(&mut G::new(SEED, "nonce"), i));
    }
    f.rand(10, |g| {
        let i = g.below(N_NONCE);
        nonce(g, i)
    });
    f.finish(m, dir);
}

fn transactions(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<Transaction>::new("Transaction", SEED);
    f.hash(|t: &Transaction| vec![("hash", hex(&t.get_hash_and_size().0.0))]);
    {
        let g = &mut G::new(SEED, "tx-edge");
        f.edge("v0", Transaction::V0(transaction_v0(g)));
        f.edge("v1", Transaction::V1(transaction_v1(g)));
        let mut t = transaction_v0(g);
        t.actions = vec![];
        f.edge("v0-no-actions", Transaction::V0(t));
        let mut t = transaction_v0(g);
        t.signer_id = "a".repeat(64).parse().unwrap();
        t.receiver_id = "b".repeat(64).parse().unwrap();
        t.actions = (0..100).map(|_| Action::Transfer(near_primitives::action::TransferAction {
            deposit: near_primitives::types::Balance::from_yoctonear(u128::MAX),
        })).collect();
        f.edge("v0-many-transfers", Transaction::V0(t));
        let mut t = transaction_v1(g);
        t.public_key = g.pk_of(KeyType::MLDSA65);
        f.edge("v1-mldsa", Transaction::V1(t));
    }
    f.rand(200, transaction);
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::transaction::TransactionV0>::new("TransactionV0", SEED);
    f.rand(40, transaction_v0);
    f.finish(m, dir);

    let mut f = Fam::<near_primitives::transaction::TransactionV1>::new("TransactionV1", SEED);
    f.rand(40, transaction_v1);
    f.finish(m, dir);

    let mut f = Fam::<SignedTransaction>::new("SignedTransaction", SEED);
    f.hash(|t: &SignedTransaction| vec![("hash", hex(&t.get_hash().0))]);
    f.rand(200, signed_transaction);
    {
        let g = &mut G::new(SEED, "stx-edge");
        for ty in [KeyType::ED25519, KeyType::SECP256K1, KeyType::MLDSA65] {
            let sk = g.secret(ty);
            let mut t = transaction_v1(g);
            t.public_key = sk.public_key();
            let t = Transaction::V1(t);
            let h = t.get_hash_and_size().0;
            f.edge(&format!("v1-{ty}"), SignedTransaction::new(g.sign(&sk, h.as_ref()), t));
        }
    }
    f.finish(m, dir);
}

fn receipts(m: &mut Manifest, dir: &PathBuf) {
    use near_primitives::receipt::*;
    let mut f = Fam::<Receipt>::new("Receipt", SEED);
    f.rand(200, receipt);
    f.finish(m, dir);

    let mut f = Fam::<ReceiptEnum>::new("ReceiptEnum", SEED);
    for i in 0..N_RECEIPT_ENUM {
        f.edge(&format!("variant-{i}"), receipt_enum(&mut G::new(SEED, "renum"), i));
    }
    f.rand(60, |g| {
        let i = g.below(N_RECEIPT_ENUM);
        receipt_enum(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ActionReceipt>::new("ActionReceipt", SEED);
    f.rand(60, action_receipt);
    f.finish(m, dir);

    let mut f = Fam::<ActionReceiptV2>::new("ActionReceiptV2", SEED);
    f.rand(60, action_receipt_v2);
    f.finish(m, dir);

    let mut f = Fam::<DataReceipt>::new("DataReceipt", SEED);
    f.edge("none", DataReceipt { data_id: CryptoHash::default(), data: None });
    f.edge("empty", DataReceipt { data_id: CryptoHash::default(), data: Some(vec![]) });
    f.rand(40, data_receipt);
    f.finish(m, dir);

    let mut f = Fam::<DataReceiver>::new("DataReceiver", SEED);
    f.rand(20, |g| DataReceiver { data_id: g.hash(), receiver_id: g.account() });
    f.finish(m, dir);

    let mut f = Fam::<GlobalContractDistributionReceipt>::new("GlobalContractDistributionReceipt", SEED);
    for i in 0..2 {
        f.edge(&format!("v{}", i + 1), distribution(&mut G::new(SEED, "dist"), i));
    }
    f.rand(40, |g| {
        let i = g.below(2);
        distribution(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<StateStoredReceipt>::new("StateStoredReceipt", SEED);
    for i in 0..2 {
        f.edge(&format!("v{i}"), state_stored(&mut G::new(SEED, "ssr"), i));
    }
    f.rand(60, |g| {
        let i = g.below(2);
        state_stored(g, i)
    });
    f.raw("version-2", {
        let mut b = vec![255, 255, 2];
        b.extend([0; 40]);
        b
    });
    f.raw("bad-magic", vec![255, 254, 0]);
    f.finish(m, dir);

    let mut f = Fam::<ReceiptOrStateStoredReceipt>::new("ReceiptOrStateStoredReceipt", SEED);
    for i in 0..3 {
        f.edge(&format!("case-{i}"), receipt_or_stored(&mut G::new(SEED, "rss"), i));
    }
    f.rand(80, |g| {
        let i = g.below(3);
        receipt_or_stored(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<TrieQueueIndices>::new("TrieQueueIndices", SEED);
    f.edge("zero", TrieQueueIndices::default());
    f.rand(10, queue_indices);
    f.finish(m, dir);

    let mut f = Fam::<BufferedReceiptIndices>::new("BufferedReceiptIndices", SEED);
    f.edge("empty", BufferedReceiptIndices::default());
    f.rand(30, buffered);
    f.finish(m, dir);

    let mut f = Fam::<PromiseYieldTimeout>::new("PromiseYieldTimeout", SEED);
    f.rand(20, |g| PromiseYieldTimeout { account_id: g.account(), data_id: g.hash(), expires_at: g.u64() });
    f.finish(m, dir);

    let mut f = Fam::<ReceivedData>::new("ReceivedData", SEED);
    f.edge("none", ReceivedData { data: None });
    f.rand(10, |g| ReceivedData { data: g.opt(|g| g.bytes(40)) });
    f.finish(m, dir);
}

fn errors(m: &mut Manifest, dir: &PathBuf) {
    use near_primitives::errors::*;
    macro_rules! enum_family {
        ($name:literal, $ty:ty, $n:expr, $mk:expr, $rand:expr) => {{
            let mut f = Fam::<$ty>::new($name, SEED);
            for i in 0..$n {
                let mk: &dyn Fn(&mut G, usize) -> $ty = &$mk;
                f.edge(&format!("variant-{i}"), mk(&mut G::new(SEED, concat!($name, "-edge")), i));
            }
            f.rand($rand, |g| {
                let i = g.below($n);
                let mk: &dyn Fn(&mut G, usize) -> $ty = &$mk;
                mk(g, i)
            });
            f.finish(m, dir);
        }};
    }
    enum_family!("TxExecutionError", TxExecutionError, N_TX_ERROR, tx_error, 300);
    enum_family!("InvalidTxError", InvalidTxError, N_INVALID_TX, invalid_tx, 100);
    enum_family!("ActionErrorKind", ActionErrorKind, N_ACTION_KIND, action_kind, 100);
    enum_family!("InvalidAccessKeyError", InvalidAccessKeyError, N_ACCESS_KEY_ERROR, access_key_error, 30);
    enum_family!("ActionsValidationError", ActionsValidationError, N_ACTIONS_VALIDATION, actions_validation, 60);
    enum_family!("ReceiptValidationError", ReceiptValidationError, N_RECEIPT_VALIDATION, receipt_validation, 30);
    enum_family!("StorageError", StorageError, N_STORAGE, storage_error, 20);
    enum_family!("FunctionCallError", FunctionCallError, N_FUNCTION_CALL, function_call_error, 40);
    enum_family!("CompilationError", CompilationError, N_COMPILATION, compilation_error, 10);
    enum_family!("HostError", HostError, N_HOST, host_error, 60);
    enum_family!("PrepareError", PrepareError, N_PREPARE, |_g: &mut G, i| prepare_error(i), 0);
    enum_family!("WasmTrap", WasmTrap, N_TRAP, |_g: &mut G, i| wasm_trap(i), 0);
    enum_family!("MethodResolveError", MethodResolveError, 3, |_g: &mut G, i| method_resolve(i), 0);

    let mut f = Fam::<ActionError>::new("ActionError", SEED);
    f.rand(100, action_error);
    f.finish(m, dir);

    let mut f = Fam::<MissingTrieValue>::new("MissingTrieValue", SEED);
    f.rand(10, missing_trie_value);
    f.finish(m, dir);
}

fn outcomes(m: &mut Manifest, dir: &PathBuf) {
    use near_primitives::merkle::MerklePathItem;
    use near_primitives::profile_data_v2::ProfileDataV2;
    use near_primitives::profile_data_v3::ProfileDataV3;
    use near_primitives::transaction::*;

    let mut f = Fam::<ProfileDataV2>::new("ProfileDataV2", SEED);
    f.edge("zero", ProfileDataV2::default());
    f.edge("test", ProfileDataV2::test());
    f.rand(15, profile_v2);
    // The decoder pads short arrays with zeros and drops extra entries.
    for n in [0u32, 10, 71, 73, 100] {
        let mut b = n.to_le_bytes().to_vec();
        for i in 0..n {
            b.extend((i as u64 + 1).to_le_bytes());
        }
        f.raw(&format!("len-{n}"), b);
    }
    f.finish(m, dir);

    let mut f = Fam::<ProfileDataV3>::new("ProfileDataV3", SEED);
    f.edge("zero", ProfileDataV3::default());
    f.edge("test", ProfileDataV3::test());
    f.rand(15, profile_v3);
    for (a, e) in [(0u32, 0u32), (25, 87), (27, 89), (60, 200), (26, 0), (0, 88)] {
        let mut b = Vec::new();
        for n in [a, e] {
            b.extend(n.to_le_bytes());
            for i in 0..n {
                b.extend((i as u64 + 1).to_le_bytes());
            }
        }
        b.extend(9u64.to_le_bytes());
        f.raw(&format!("len-{a}-{e}"), b);
    }
    f.finish(m, dir);

    let mut f = Fam::<ExecutionMetadata>::new("ExecutionMetadata", SEED);
    for i in 0..N_METADATA {
        f.edge(&format!("variant-{i}"), metadata(&mut G::new(SEED, "meta"), i));
    }
    f.rand(16, |g| {
        let i = g.below(N_METADATA);
        metadata(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ExecutionStatus>::new("ExecutionStatus", SEED);
    for i in 0..N_STATUS {
        f.edge(&format!("variant-{i}"), status(&mut G::new(SEED, "status"), i));
    }
    f.rand(60, |g| {
        let i = g.below(N_STATUS);
        status(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<PartialExecutionOutcome>::new("PartialExecutionOutcome", SEED);
    f.rand(40, |g| PartialExecutionOutcome::from(&outcome(g)));
    f.finish(m, dir);

    let mut f = Fam::<ExecutionOutcome>::new("ExecutionOutcome", SEED);
    f.rand(150, outcome);
    f.finish(m, dir);

    let mut f = Fam::<ExecutionOutcomeWithId>::new("ExecutionOutcomeWithId", SEED);
    f.hash(|o: &ExecutionOutcomeWithId| {
        let hashes = o.to_hashes();
        let cat: Vec<u8> = hashes.iter().flat_map(|h| h.0).collect();
        vec![("hash", hex(&CryptoHash::hash_borsh(&hashes).0)), ("hashes", hex(&cat))]
    });
    f.rand(150, outcome_with_id);
    f.edge("no-logs", ExecutionOutcomeWithId {
        id: CryptoHash::default(),
        outcome: ExecutionOutcome { logs: vec![], ..outcome(&mut G::new(SEED, "ol")) },
    });
    f.finish(m, dir);

    let mut f = Fam::<ExecutionOutcomeWithIdAndProof>::new("ExecutionOutcomeWithIdAndProof", SEED);
    f.rand(40, outcome_with_id_and_proof);
    f.finish(m, dir);

    let mut f = Fam::<ExecutionOutcomeWithProof>::new("ExecutionOutcomeWithProof", SEED);
    f.rand(30, outcome_with_proof);
    f.finish(m, dir);

    let mut f = Fam::<MerklePathItem>::new("MerklePathItem", SEED);
    f.rand(10, |g| merkle_path(g).pop().unwrap_or(MerklePathItem {
        hash: CryptoHash::default(),
        direction: near_primitives::merkle::Direction::Left,
    }));
    f.raw("direction-2", {
        let mut b = vec![0; 32];
        b.push(2);
        b
    });
    f.finish(m, dir);

    let _ = (Account::new, BTreeMap::<u8, u8>::new, <Action as BorshDeserialize>::try_from_slice);
}
