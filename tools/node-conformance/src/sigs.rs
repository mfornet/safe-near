//! A record of the ED25519 and SECP256K1 signatures the oracle makes (the signature as 64 or 65
//! bytes, the key as 32 or 64), so that the Lean side can verify the real signatures in the Borsh
//! fixtures. The fixture files do not carry the signer's key, and the
//! fixtures stay byte for byte what they were; `signatures.jsonl` is written beside them.
//!
//! Every accepted line that is not a mutation or a hand-written byte string gets a record (the
//! Lean side checks only those, because the signatures of a mutated line are no longer valid) with
//! the keys and signatures recorded since the previous such line was built: `sigs` (a signature made by the oracle, with its key and message) and `signers` (the
//! keys of validator signers whose signatures nearcore's constructors make internally; the Lean
//! side tries them for the signatures of that value).

use near_crypto::{PublicKey, SecretKey, Signature};
use std::sync::Mutex;

pub enum Entry {
    Sig { sig: Vec<u8>, public: Vec<u8>, msg: Vec<u8> },
    Signer { public: [u8; 32] },
}

static PENDING: Mutex<Vec<Entry>> = Mutex::new(Vec::new());
static LINES: Mutex<Vec<String>> = Mutex::new(Vec::new());

fn hex(b: &[u8]) -> String {
    crate::fam::hex(b)
}

/// Record `sig` as made by `public` over `msg`; other key types are ignored.
pub fn record(sig: &Signature, public: &PublicKey, msg: &[u8]) {
    let entry = match (sig, public) {
        (Signature::ED25519(s), PublicKey::ED25519(k)) => {
            Entry::Sig { sig: s.to_bytes().to_vec(), public: k.0.to_vec(), msg: msg.to_vec() }
        }
        (Signature::SECP256K1(s), PublicKey::SECP256K1(k)) => Entry::Sig {
            sig: <[u8; 65]>::from(s.clone()).to_vec(),
            public: k.as_ref().to_vec(),
            msg: msg.to_vec(),
        },
        _ => return,
    };
    PENDING.lock().unwrap().push(entry);
}

/// Record a validator signer whose signatures are made inside nearcore's constructors.
pub fn record_signer(public: &PublicKey) {
    if let PublicKey::ED25519(k) = public {
        PENDING.lock().unwrap().push(Entry::Signer { public: k.0 });
    }
}

/// Sign `msg` with `sk` and record the signature.
pub fn sign(sk: &SecretKey, msg: &[u8]) -> Signature {
    let sig = sk.sign(msg);
    record(&sig, &sk.public_key(), msg);
    sig
}

/// Forget what was recorded for a value that did not become a line.
pub fn discard() {
    PENDING.lock().unwrap().clear();
}

/// Attach what was recorded since the last call to line number `index` (from 0, in file order)
/// of type `ty`. Names are not unique within a file, positions are.
pub fn attach(ty: &str, index: usize, name: &str) {
    let entries = std::mem::take(&mut *PENDING.lock().unwrap());
    let mut sigs = vec![];
    let mut signers: Vec<String> = vec![];
    for e in entries {
        match e {
            Entry::Sig { sig, public, msg } => sigs.push(serde_json::json!({
                "sig": hex(&sig), "public": hex(&public), "msg": hex(&msg) })),
            Entry::Signer { public } => {
                let h = hex(&public);
                if !signers.contains(&h) {
                    signers.push(h);
                }
            }
        }
    }
    let line = serde_json::json!({ "type": ty, "line": index, "name": name, "sigs": sigs, "signers": signers });
    LINES.lock().unwrap().push(serde_json::to_string(&line).unwrap());
}

pub fn write(path: &std::path::Path) {
    let lines = LINES.lock().unwrap();
    std::fs::write(path, lines.join("\n") + "\n").unwrap();
}
