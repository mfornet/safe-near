//! Seeded value generation. Every function is a pure function of the generator state.

use near_crypto::{KeyType, PublicKey, SecretKey, Signature};
use near_primitives::hash::CryptoHash;
use near_primitives::types::{AccountId, Balance, Gas};
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

pub struct G(pub ChaCha8Rng);

fn fnv(s: &str) -> u64 {
    s.bytes().fold(0xcbf29ce484222325, |h, b| (h ^ b as u64).wrapping_mul(0x100000001b3))
}

const ALNUM: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789";
const HEX: &[u8] = b"0123456789abcdef";

impl G {
    /// A generator whose stream depends only on `seed` and `label`.
    pub fn new(seed: u64, label: &str) -> G {
        G(ChaCha8Rng::seed_from_u64(seed ^ fnv(label)))
    }

    pub fn u64(&mut self) -> u64 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => u64::MAX,
            3 => self.0.gen_range(0..1000),
            4 => 1u64 << self.0.gen_range(0..64),
            _ => self.0.next_u64(),
        }
    }

    pub fn u32(&mut self) -> u32 {
        self.u64() as u32
    }

    pub fn u16(&mut self) -> u16 {
        self.u64() as u16
    }

    pub fn below(&mut self, n: usize) -> usize {
        self.0.gen_range(0..n)
    }

    pub fn bool(&mut self) -> bool {
        self.0.gen_bool(0.5)
    }

    pub fn gas(&mut self) -> Gas {
        Gas::from_gas(self.u64())
    }

    pub fn balance(&mut self) -> Balance {
        let v = match self.below(8) {
            0 => 0,
            1 => 1,
            2 => u128::MAX,
            3 => 10u128.pow(24),
            4 => 1u128 << self.0.gen_range(0..128),
            5 => self.0.next_u64() as u128,
            _ => ((self.0.next_u64() as u128) << 64) | self.0.next_u64() as u128,
        };
        Balance::from_yoctonear(v)
    }

    pub fn bytes(&mut self, max: usize) -> Vec<u8> {
        let n = if self.below(4) == 0 { 0 } else { self.below(max + 1) };
        let mut v = vec![0u8; n];
        self.0.fill_bytes(&mut v);
        v
    }

    pub fn hash(&mut self) -> CryptoHash {
        let mut b = [0u8; 32];
        if self.below(16) != 0 {
            self.0.fill_bytes(&mut b);
        }
        CryptoHash(b)
    }

    /// A valid account id of any of the shapes NEAR uses.
    pub fn account(&mut self) -> AccountId {
        let s = match self.below(10) {
            0 => {
                let n = self.below(2) + 2;
                (0..n).map(|_| ALNUM[self.below(36)] as char).collect()
            }
            1 => (0..64).map(|_| HEX[self.below(16)] as char).collect(),
            2 => format!("0x{}", (0..40).map(|_| HEX[self.below(16)] as char).collect::<String>()),
            3 => format!("0s{}", (0..40).map(|_| HEX[self.below(16)] as char).collect::<String>()),
            4 => {
                let root: String = (0..self.below(8) + 3).map(|_| ALNUM[self.below(36)] as char).collect();
                format!("{root}.near")
            }
            _ => {
                let mut s = String::new();
                let parts = self.below(4) + 1;
                for i in 0..parts {
                    if i > 0 {
                        s.push(['.', '-', '_'][self.below(3)]);
                    }
                    for _ in 0..self.below(10) + 1 {
                        s.push(ALNUM[self.below(36)] as char);
                    }
                }
                if s.len() < 2 {
                    s.push('x');
                }
                s.truncate(64);
                while !s.ends_with(|c: char| c.is_ascii_alphanumeric()) {
                    s.pop();
                }
                if s.len() < 2 {
                    s.push('x');
                }
                s
            }
        };
        s.parse().unwrap()
    }

    pub fn string(&mut self, max: usize) -> String {
        let n = if self.below(4) == 0 { 0 } else { self.below(max + 1) };
        (0..n)
            .map(|_| match self.below(10) {
                0 => char::from_u32(0x80 + self.below(0x700) as u32).unwrap(),
                1 => '\u{1F600}',
                _ => (b' ' + self.below(95) as u8) as char,
            })
            .collect()
    }

    pub fn secret(&mut self, ty: KeyType) -> SecretKey {
        let seed = format!("k{}", self.0.next_u64());
        SecretKey::from_seed(ty, &seed)
    }

    /// An ED25519 or SECP256K1 key, or rarely an ML-DSA-65 one.
    pub fn key_type(&mut self) -> KeyType {
        match self.below(150) {
            0 => KeyType::MLDSA65,
            1..=40 => KeyType::SECP256K1,
            _ => KeyType::ED25519,
        }
    }

    pub fn pk(&mut self) -> PublicKey {
        let ty = self.key_type();
        self.secret(ty).public_key()
    }

    pub fn pk_of(&mut self, ty: KeyType) -> PublicKey {
        self.secret(ty).public_key()
    }

    /// A real signature of a random message, by a random key.
    pub fn sig(&mut self) -> Signature {
        let ty = self.key_type();
        self.sig_of(ty)
    }

    pub fn sig_of(&mut self, ty: KeyType) -> Signature {
        let sk = self.secret(ty);
        let msg = self.hash();
        self.sign(&sk, &msg.0)
    }

    /// ED25519 and SECP256K1 signing is deterministic. ML-DSA-65 signing is randomised, so its
    /// signatures are seeded random bytes of the right length (Borsh does not verify them).
    pub fn sign(&mut self, sk: &SecretKey, msg: &[u8]) -> Signature {
        match sk.key_type() {
            KeyType::MLDSA65 => {
                let mut b = vec![0u8; 3309];
                self.0.fill_bytes(&mut b);
                Signature::from_parts(KeyType::MLDSA65, &b).unwrap()
            }
            _ => sk.sign(msg),
        }
    }

    pub fn opt<T>(&mut self, f: impl FnOnce(&mut G) -> T) -> Option<T> {
        if self.bool() { Some(f(self)) } else { None }
    }

    pub fn vec<T>(&mut self, max: usize, mut f: impl FnMut(&mut G) -> T) -> Vec<T> {
        let n = if self.below(3) == 0 { 0 } else { self.below(max + 1) };
        (0..n).map(|_| f(self)).collect()
    }
}
