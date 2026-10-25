//! The M8b oracle for the validator: Reed-Solomon, chunk construction, and the signed messages a
//! validator produces. Everything is built with the pinned crates (`near-primitives` and
//! `reed-solomon-erasure` 6.0.0, the code `nearcore` 2.13.4 runs); the Lean side reproduces each line.
//!
//! `cargo run --release --locked --bin validator-fixtures -- ../../near-lean/node/fixtures/validator`
#![allow(deprecated)]

#[path = "chain.rs"]
mod chain;
#[path = "fam.rs"]
mod fam;
#[path = "rng.rs"]
mod rng;
#[path = "sigs.rs"]
mod sigs;
#[path = "values.rs"]
mod values;
mod validator_block;
mod validator_chunk;
mod validator_msgs;
mod validator_rs;

use std::path::PathBuf;

pub use fam::hex;

/// A file of JSON lines.
pub struct Out {
    dir: PathBuf,
    files: std::collections::BTreeMap<String, Vec<String>>,
}

impl Out {
    pub fn new(dir: PathBuf) -> Self {
        std::fs::create_dir_all(&dir).unwrap();
        Out { dir, files: Default::default() }
    }

    pub fn line(&mut self, file: &str, v: serde_json::Value) {
        self.files.entry(file.to_string()).or_default().push(serde_json::to_string(&v).unwrap());
    }

    pub fn finish(self) {
        let mut counts = serde_json::Map::new();
        for (name, lines) in &self.files {
            std::fs::write(self.dir.join(format!("{name}.jsonl")), lines.join("\n") + "\n").unwrap();
            counts.insert(name.clone(), lines.len().into());
        }
        let manifest = serde_json::json!({
            "protocol_version": near_primitives::version::PROTOCOL_VERSION,
            "crates": "near-primitives =0.37.4, reed-solomon-erasure =6.0.0",
            "lines": counts,
        });
        std::fs::write(
            self.dir.join("manifest.json"),
            serde_json::to_string_pretty(&manifest).unwrap() + "\n",
        )
        .unwrap();
    }
}

fn main() {
    assert_eq!(near_primitives::version::PROTOCOL_VERSION, 86, "the oracle crates must be protocol 86");
    let first = std::env::args().nth(1).expect("usage: validator-fixtures <out dir> | --verify-zstd <file>");
    if first == "--verify-zstd" {
        validator_msgs::verify_zstd(&std::env::args().nth(2).expect("a file"));
        return;
    }
    let dir = PathBuf::from(first);
    let mut out = Out::new(dir);
    validator_rs::reed_solomon(&mut out);
    validator_chunk::chunks(&mut out);
    validator_msgs::messages(&mut out);
    validator_block::blocks(&mut out);
    out.finish();
}
