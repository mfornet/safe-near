//! Fixture families: one per type, each a JSON-lines file. Every positive line has been decoded
//! and re-encoded by the pinned crates; every negative line has been rejected by them.

use crate::rng::G;
use borsh::{BorshDeserialize, BorshSerialize};
use std::collections::{BTreeMap, HashSet};
use std::path::Path;

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

pub struct Manifest {
    protocol_version: u64,
    release: String,
    seed: u64,
    types: BTreeMap<String, (usize, usize)>,
}

impl Manifest {
    pub fn new(protocol_version: u64, release: &str, seed: u64) -> Self {
        Manifest { protocol_version, release: release.to_string(), seed, types: BTreeMap::new() }
    }

    pub fn write(&self, dir: &Path) {
        let types: serde_json::Map<String, serde_json::Value> = self
            .types
            .iter()
            .map(|(k, (p, n))| (k.clone(), serde_json::json!({ "accept": p, "reject": n })))
            .collect();
        let v = serde_json::json!({
            "protocol_version": self.protocol_version,
            "nearcore_release": self.release,
            "crates": "near-primitives =0.37.4, near-crypto =0.37.4, near-primitives-core =0.37.4",
            "seed": format!("{:#018x}", self.seed),
            "types": types,
        });
        std::fs::write(dir.join("manifest.json"), serde_json::to_string_pretty(&v).unwrap() + "\n")
            .unwrap();
    }
}

type Hasher<T> = Box<dyn Fn(&T) -> Vec<(&'static str, String)>>;

pub struct Fam<T> {
    ty: String,
    g: G,
    lines: Vec<String>,
    seen: HashSet<Vec<u8>>,
    hasher: Option<Hasher<T>>,
    accept: usize,
    reject: usize,
    max_mutated_len: usize,
}

impl<T: BorshSerialize + BorshDeserialize> Fam<T> {
    pub fn new(ty: &str, seed: u64) -> Self {
        Fam {
            ty: ty.to_string(),
            g: G::new(seed, &format!("{ty}/mutations")),
            lines: vec![],
            seen: HashSet::new(),
            hasher: None,
            accept: 0,
            reject: 0,
            max_mutated_len: 6000,
        }
    }

    /// Values longer than this are emitted without mutations.
    pub fn mutate_up_to(&mut self, len: usize) {
        self.max_mutated_len = len;
    }

    /// The derived hashes of a value, as `(field, hex)` pairs.
    pub fn hash(&mut self, f: impl Fn(&T) -> Vec<(&'static str, String)> + 'static) {
        self.hasher = Some(Box::new(f));
    }

    /// A hand-written value; it and its mutations are emitted.
    pub fn edge(&mut self, name: &str, v: T) {
        self.positive(name, &v, true);
    }

    /// `n` seeded random values; the first few also get mutations.
    pub fn rand(&mut self, n: usize, f: impl Fn(&mut G) -> T) {
        self.rand_with(n, 12, f);
    }

    /// `n` seeded random values; the first `mutated` also get mutations.
    pub fn rand_with(&mut self, n: usize, mutated: usize, f: impl Fn(&mut G) -> T) {
        let mut g = G::new(0x5eed, &format!("{}/values", self.ty));
        for i in 0..n {
            let v = f(&mut g);
            self.positive(&format!("rand-{i}"), &v, i < mutated);
        }
    }

    /// Bytes classified by the oracle: rejected, accepted, or accepted and re-encoded differently.
    pub fn raw(&mut self, name: &str, bytes: Vec<u8>) {
        if !self.seen.insert(bytes.clone()) {
            return;
        }
        match T::try_from_slice(&bytes) {
            Err(_) => {
                self.reject += 1;
                self.lines.push(format!(
                    "{{\"type\":\"{}\",\"name\":\"{name}\",\"borsh\":\"{}\",\"reject\":true}}",
                    self.ty,
                    hex(&bytes)
                ));
            }
            Ok(d) => {
                let again = borsh::to_vec(&d).unwrap();
                self.emit(name, &bytes, &d, (again != bytes).then_some(again));
            }
        }
    }

    fn positive(&mut self, name: &str, v: &T, mutate: bool) {
        let bytes = borsh::to_vec(v).unwrap();
        let d = T::try_from_slice(&bytes)
            .unwrap_or_else(|e| panic!("{}/{name}: the oracle cannot decode its own encoding: {e}", self.ty));
        assert_eq!(borsh::to_vec(&d).unwrap(), bytes, "{}/{name}: re-encoding differs", self.ty);
        if !self.seen.insert(bytes.clone()) {
            crate::sigs::discard();
            return;
        }
        self.emit(name, &bytes, &d, None);
        crate::sigs::attach(&self.ty, self.lines.len() - 1, name);
        if mutate && bytes.len() <= self.max_mutated_len {
            self.mutations(name, &bytes);
        }
    }

    fn mutations(&mut self, name: &str, bytes: &[u8]) {
        let n = bytes.len();
        if n > 0 {
            self.raw(&format!("{name}/trunc"), bytes[..n - 1].to_vec());
            let pos = self.g.below(n);
            let mut m = bytes.to_vec();
            m[pos] ^= 1 + self.g.below(255) as u8;
            self.raw(&format!("{name}/flip{pos}"), m);
            let mut m = bytes.to_vec();
            m[0] = 255;
            self.raw(&format!("{name}/tag255"), m);
        }
        if n > 1 {
            self.raw(&format!("{name}/half"), bytes[..n / 2].to_vec());
        }
        let mut m = bytes.to_vec();
        m.push(0);
        self.raw(&format!("{name}/trailing"), m);
    }

    fn emit(&mut self, name: &str, bytes: &[u8], d: &T, canonical: Option<Vec<u8>>) {
        self.accept += 1;
        let hashes = match &self.hasher {
            Some(f) => f(d).iter().map(|(k, v)| format!(",\"{k}\":\"{v}\"")).collect(),
            None => ",\"hash\":null".to_string(),
        };
        let canonical = canonical.map(|c| format!(",\"canonical\":\"{}\"", hex(&c))).unwrap_or_default();
        self.lines.push(format!(
            "{{\"type\":\"{}\",\"name\":\"{name}\",\"borsh\":\"{}\"{hashes}{canonical}}}",
            self.ty,
            hex(bytes)
        ));
    }

    pub fn finish(self, m: &mut Manifest, dir: &Path) {
        assert!(self.accept > 0, "{}: no accepted values", self.ty);
        std::fs::write(dir.join(format!("{}.jsonl", self.ty)), self.lines.join("\n") + "\n").unwrap();
        m.types.insert(self.ty, (self.accept, self.reject));
    }
}
