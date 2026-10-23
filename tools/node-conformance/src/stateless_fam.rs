//! The M1c stateless validation families: chunk endorsements, chunk state witnesses, partial
//! encoded witnesses, the contract-distribution messages and the SPICE variants.
//!
//! Signed messages are built with a real ED25519 signer. nearcore does not expose the signed
//! bytes, but it verifies the signature over `borsh(inner)`; the generators assert `verify`, and
//! the `sigData` field is the Borsh prefix before the (65 byte) signature, which is exactly those
//! bytes.
#![allow(deprecated)]

use crate::chain::*;
use crate::fam::{hex, Fam, Manifest};
use crate::rng::G;
use crate::values::*;
use crate::SEED;
use borsh::{BorshDeserialize, BorshSerialize};
use near_crypto::{KeyType, PublicKey};
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::{ChunkHash, EncodedShardChunkBody, ReceiptProof};
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::ShardId;
use near_primitives::spice::partial_data::*;
use near_primitives::spice::state_witness::*;
use near_primitives::stateless_validation::chunk_endorsement::ChunkEndorsement;
use near_primitives::stateless_validation::contract_distribution::*;
use near_primitives::stateless_validation::partial_witness::*;
use near_primitives::stateless_validation::state_witness::*;
use near_primitives::stateless_validation::stored_chunk_state_transition_data::*;
use near_primitives::stateless_validation::ChunkProductionKey;
use near_primitives::types::{ChunkExecutionResultHash, EpochId, SpiceChunkId};
use near_primitives::utils::compression::CompressedData;
use near_primitives::validator_signer::{InMemoryValidatorSigner, ValidatorSigner};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

pub fn h(c: &CryptoHash) -> String {
    hex(&c.0)
}

/// An ED25519 signer for a random account.
pub fn signer(g: &mut G) -> ValidatorSigner {
    let seed = format!("s{}", g.u64());
    InMemoryValidatorSigner::from_seed(g.account(), KeyType::ED25519, &seed)
}

fn key(g: &mut G) -> ChunkProductionKey {
    ChunkProductionKey { shard_id: shard(g), epoch_id: epoch_id(g), height_created: g.u64() }
}

fn code_hash(g: &mut G) -> CodeHash {
    CodeHash(g.hash())
}

fn code_bytes(g: &mut G) -> CodeBytes {
    CodeBytes(Arc::from(g.bytes(120)))
}

fn main_transition(g: &mut G) -> MainTransitionKey {
    MainTransitionKey { block_hash: g.hash(), shard_id: shard(g) }
}

/// Distinct code hashes in ascending order (a `HashSet` iterates in an unspecified order).
fn code_hashes(g: &mut G) -> Vec<CodeHash> {
    let set: HashSet<CodeHash> = g.vec(5, code_hash).into_iter().collect();
    let mut v: Vec<_> = set.into_iter().collect();
    v.sort();
    v
}

/// The bytes before the 65 byte ED25519 signature at the end of `b`, after `skip` leading bytes.
fn before_signature(b: &[u8], skip: usize, trailing: usize) -> String {
    let end = b.len() - trailing - 65;
    assert_eq!(b[end], 0, "not an ED25519 signature");
    hex(&b[skip..end])
}

fn sig_fields<T: BorshSerialize>(v: &T) -> Vec<(&'static str, String)> {
    vec![("sigData", before_signature(&borsh::to_vec(v).unwrap(), 1, 0))]
}

/// `[tag] ++ inner ++ signature` decoded by nearcore; panics unless `verify` accepts it.
fn signed<T: BorshDeserialize>(
    tag: Option<u8>,
    inner: Vec<u8>,
    signer: &ValidatorSigner,
    verify: impl Fn(&T, &PublicKey) -> bool,
) -> T {
    let mut b: Vec<u8> = tag.into_iter().collect();
    b.extend(&inner);
    b.extend(borsh::to_vec(&signer.sign_bytes(&inner)).unwrap());
    let v = T::try_from_slice(&b).expect("signed message does not decode");
    assert!(verify(&v, &signer.public_key()), "signature does not cover the Borsh of inner");
    v
}

fn ser<T: BorshSerialize>(v: &T) -> Vec<u8> {
    borsh::to_vec(v).unwrap()
}

pub fn endorsement(g: &mut G) -> ChunkEndorsement {
    let s = signer(g);
    let i = g.below(N_CHUNK_HEADER);
    let header = chunk_header(g, i);
    let e = ChunkEndorsement::new(epoch_id(g), &header, &s);
    assert!(e.verify(&s.public_key()));
    assert!(ChunkEndorsement::validate_signature(
        e.chunk_hash(),
        &e.signature(),
        &s.public_key()
    ));
    e
}

fn endorsement_fields(e: &ChunkEndorsement) -> Vec<(&'static str, String)> {
    let b = borsh::to_vec(e).unwrap();
    // tag, inner (chunk hash and the 16 byte differentiator), signature, metadata, signature.
    let inner_end = 1 + 32 + 4 + 16;
    let meta_start = inner_end + 65;
    vec![
        ("sigData", hex(&b[1..inner_end])),
        ("metaSigData", before_signature(&b, meta_start, 0)),
        ("key", hex(&borsh::to_vec(&e.chunk_production_key()).unwrap())),
    ]
}

fn witness_transition(g: &mut G) -> ChunkStateTransition {
    ChunkStateTransition { block_hash: g.hash(), base_state: partial_state(g), post_state_root: g.hash() }
}

pub fn witness(g: &mut G) -> ChunkStateWitness {
    let i = g.below(N_CHUNK_HEADER);
    let proofs: HashMap<ChunkHash, ReceiptProof> =
        g.vec(3, |g| (ChunkHash(g.hash()), receipt_proof(g))).into_iter().collect();
    ChunkStateWitness::new(
        epoch_id(g),
        chunk_header(g, i),
        witness_transition(g),
        proofs,
        g.hash(),
        g.vec(2, signed_transaction),
        g.vec(3, witness_transition),
        g.vec(2, signed_transaction),
    )
}

fn witness_fields(w: &ChunkStateWitness) -> Vec<(&'static str, String)> {
    vec![
        ("key", hex(&ser(&w.chunk_production_key()))),
        ("ack", hex(&ser(&ChunkStateWitnessAck::new(w)))),
    ]
}

fn partial_witness(g: &mut G, s: &ValidatorSigner) -> PartialEncodedStateWitness {
    let i = g.below(N_CHUNK_HEADER);
    let w = PartialEncodedStateWitness::new(
        epoch_id(g),
        chunk_header(g, i),
        g.below(1 << 20),
        g.bytes(200),
        g.below(1 << 24),
        s,
    );
    assert!(w.verify(&s.public_key()));
    w
}

fn partial_witness_v2(g: &mut G, s: &ValidatorSigner) -> PartialEncodedStateWitnessV2 {
    let i = g.below(N_CHUNK_HEADER);
    let w = PartialEncodedStateWitnessV2::new(
        epoch_id(g),
        chunk_header(g, i),
        g.below(1 << 20),
        g.bytes(200),
        g.below(1 << 24),
        s,
    );
    assert!(w.verify(&s.public_key()));
    w
}

fn versioned_fields(w: &VersionedPartialEncodedStateWitness) -> Vec<(&'static str, String)> {
    let mut f = sig_fields(w);
    f.push(("key", hex(&ser(&w.chunk_production_key()))));
    f
}

fn contract_accesses(g: &mut G) -> ChunkContractAccesses {
    let s = signer(g);
    let inner = ser(&(key(g), code_hashes(g), main_transition(g), "ChunkContractAccessesInner".to_string()));
    signed(Some(0), inner, &s, |v: &ChunkContractAccesses, pk| v.verify_signature(pk))
}

fn code_request(g: &mut G) -> ContractCodeRequest {
    let s = signer(g);
    let inner = ser(&(
        s.validator_id().clone(),
        key(g),
        code_hashes(g),
        main_transition(g),
        "ContractCodeRequestInner".to_string(),
    ));
    signed(Some(0), inner, &s, |v: &ContractCodeRequest, pk| v.verify_signature(pk))
}

fn contracts(g: &mut G) -> Vec<CodeBytes> {
    g.vec(4, code_bytes)
}

fn code_response_v1(g: &mut G) -> ContractCodeResponseV1 {
    ContractCodeResponseV1::encode(key(g), &contracts(g)).unwrap()
}

fn code_response_v2(g: &mut G) -> ContractCodeResponseV2 {
    let s = signer(g);
    let r = ContractCodeResponseV2::encode(key(g), &contracts(g), &s).unwrap();
    assert!(ContractCodeResponse::V2(r.clone()).verify_signature(&s.public_key()));
    r
}

fn deploys_part(g: &mut G) -> PartialEncodedContractDeploysPart {
    PartialEncodedContractDeploysPart {
        part_ord: g.below(1 << 16),
        data: g.bytes(150).into_boxed_slice(),
        encoded_length: g.below(1 << 20),
    }
}

fn deploys(g: &mut G) -> PartialEncodedContractDeploys {
    let s = signer(g);
    let d = PartialEncodedContractDeploys::new(key(g), deploys_part(g), &s);
    assert!(d.verify_signature(&s.public_key()));
    d
}

fn spice_id(g: &mut G) -> SpiceChunkId {
    spice_chunk_id(g)
}

fn spice_accesses(g: &mut G) -> SpiceChunkContractAccesses {
    let s = signer(g);
    let inner = ser(&(spice_id(g), code_hashes(g), "SpiceChunkContractAccessesInner".to_string()));
    signed(None, inner, &s, |v: &SpiceChunkContractAccesses, pk| v.verify_signature(pk))
}

fn spice_request(g: &mut G) -> SpiceContractCodeRequest {
    let s = signer(g);
    let inner = ser(&(
        s.validator_id().clone(),
        spice_id(g),
        code_hashes(g),
        "SpiceContractCodeRequestInner".to_string(),
    ));
    signed(None, inner, &s, |v: &SpiceContractCodeRequest, pk| v.verify_signature(pk))
}

fn data_id(g: &mut G) -> SpiceDataIdentifier {
    if g.bool() {
        SpiceDataIdentifier::ReceiptProof {
            block_hash: g.hash(),
            from_shard_id: shard(g),
            to_shard_id: shard(g),
        }
    } else {
        SpiceDataIdentifier::Witness { block_hash: g.hash(), shard_id: shard(g) }
    }
}

fn data_part(g: &mut G) -> SpiceDataPart {
    SpiceDataPart { part_ord: g.u64(), part: g.bytes(80).into_boxed_slice(), merkle_proof: merkle_path(g) }
}

fn partial_data(g: &mut G) -> SpicePartialData {
    let s = signer(g);
    let commitment = SpiceDataCommitment { hash: g.hash(), root: g.hash(), encoded_length: g.u64() };
    let d = SpicePartialData::new(data_id(g), commitment, g.vec(3, data_part), &s);
    assert!(d.clone().into_verified(&s.public_key()).is_some());
    d
}

/// The Borsh pair of the inner data and the differentiator, which `into_verified` checks.
fn partial_data_fields(d: &SpicePartialData) -> Vec<(&'static str, String)> {
    let b = ser(d);
    let sender = ser(d.sender());
    let inner_end = b.len() - 65 - sender.len();
    let mut data = b[..inner_end].to_vec();
    data.extend(ser(&"SpicePartialData".to_string()));
    vec![("sigData", hex(&data))]
}

fn spice_witness(g: &mut G) -> SpiceChunkStateWitness {
    let proofs: HashMap<_, ReceiptProof> = g.vec(3, |g| (shard(g), receipt_proof(g))).into_iter().collect();
    let accesses: HashSet<CodeHash> = g.vec(4, code_hash).into_iter().collect();
    SpiceChunkStateWitness::new(
        spice_id(g),
        SpiceChunkStateTransition { base_state: partial_state(g), post_state_root: g.hash() },
        proofs,
        g.hash(),
        g.vec(2, signed_transaction),
        ChunkExecutionResultHash(g.hash()),
        compute_contract_accesses_hash(&accesses),
        g.opt(|g| Box::new(chunk_body(g))),
    )
}

pub fn stateless(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<ChunkProductionKey>::new("ChunkProductionKey", SEED);
    f.edge("max", ChunkProductionKey { shard_id: u64::MAX.into(), epoch_id: EpochId(CryptoHash([255; 32])), height_created: u64::MAX });
    f.rand(15, key);
    f.finish(m, dir);

    let mut f = Fam::<ChunkEndorsement>::new("ChunkEndorsement", SEED);
    f.hash(endorsement_fields);
    f.rand(25, endorsement);
    f.raw("tag0", {
        let mut b = ser(&endorsement(&mut eg("endorsement-tag0")));
        b[0] = 0;
        b
    });
    f.raw("tag2", {
        let mut b = ser(&endorsement(&mut eg("endorsement-tag2")));
        b[0] = 2;
        b
    });
    f.finish(m, dir);

    let mut f = Fam::<ChunkStateWitnessAck>::new("ChunkStateWitnessAck", SEED);
    f.rand(10, |g| ChunkStateWitnessAck { chunk_hash: ChunkHash(g.hash()) });
    f.finish(m, dir);

    let mut f = Fam::<ChunkStateTransition>::new("ChunkStateTransition", SEED);
    f.edge("default", ChunkStateTransition::default());
    f.rand(15, witness_transition);
    f.finish(m, dir);

    let mut f = Fam::<ChunkStateWitness>::new("ChunkStateWitness", SEED);
    f.hash(witness_fields);
    f.edge("dummy", ChunkStateWitness::new_dummy(7, 2.into(), CryptoHash([3; 32])));
    f.rand_with(14, 3, witness);
    f.mutate_up_to(100_000);
    // A HashMap decodes in any key order and a repeated key keeps its last value.
    let (e, hd, t) = (epoch_id(&mut eg("w-raw")), chunk_header(&mut eg("w-raw-h"), 1), witness_transition(&mut eg("w-raw-t")));
    let (p1, p2) = (receipt_proof(&mut eg("w-raw-p1")), receipt_proof(&mut eg("w-raw-p2")));
    let (k1, k2) = (ChunkHash(CryptoHash([1; 32])), ChunkHash(CryptoHash([2; 32])));
    let raw_witness = |entries: Vec<Vec<u8>>| {
        let mut b = vec![1u8];
        b.extend(ser(&(e.clone(), hd.clone(), t.clone())));
        b.extend(map_bytes(entries));
        b.extend(ser(&(CryptoHash([9; 32]), Vec::<SignedTransaction>::new(), Vec::<ChunkStateTransition>::new(), Vec::<SignedTransaction>::new())));
        b
    };
    f.raw("sorted", raw_witness(vec![ser(&(k1.clone(), p1.clone())), ser(&(k2.clone(), p2.clone()))]));
    f.raw("unsorted", raw_witness(vec![ser(&(k2.clone(), p2.clone())), ser(&(k1.clone(), p1.clone()))]));
    f.raw("duplicate", raw_witness(vec![ser(&(k1.clone(), p1.clone())), ser(&(k1.clone(), p2.clone()))]));
    f.raw("tag0", {
        let mut b = ser(&witness(&mut eg("witness-tag0")));
        b[0] = 0;
        b
    });
    f.finish(m, dir);

    let mut f = Fam::<EncodedChunkStateWitness>::new("EncodedChunkStateWitness", SEED);
    f.edge("empty", EncodedChunkStateWitness::from(Vec::<u8>::new().into_boxed_slice()));
    f.edge("small", EncodedChunkStateWitness::encode(&ChunkStateWitness::new_dummy(1, 0.into(), CryptoHash([1; 32]))).unwrap().0);
    f.rand(10, |g| EncodedChunkStateWitness::from(g.bytes(300).into_boxed_slice()));
    f.finish(m, dir);

    let mut f = Fam::<StoredChunkStateTransitionData>::new("StoredChunkStateTransitionData", SEED);
    f.rand(15, |g| {
        StoredChunkStateTransitionData::V1(StoredChunkStateTransitionDataV1 {
            base_state: partial_state(g),
            receipts_hash: g.hash(),
            contract_accesses: g.vec(4, code_hash),
            contract_deploys: g.vec(3, code_bytes),
        })
    });
    f.finish(m, dir);

    let mut f = Fam::<CodeHash>::new("CodeHash", SEED);
    f.rand(8, code_hash);
    f.finish(m, dir);

    let mut f = Fam::<CodeBytes>::new("CodeBytes", SEED);
    f.hash(|c: &CodeBytes| vec![("hash", h(&c.hash().0))]);
    f.edge("empty", CodeBytes(Arc::from(vec![])));
    f.rand(10, code_bytes);
    f.finish(m, dir);

    // `compute_contract_accesses_hash` over the set of the hashes.
    let mut f = Fam::<Vec<CodeHash>>::new("CodeHashes", SEED);
    f.hash(|v: &Vec<CodeHash>| {
        let set: HashSet<CodeHash> = v.iter().cloned().collect();
        vec![("hash", h(&compute_contract_accesses_hash(&set)))]
    });
    f.edge("empty", vec![]);
    f.edge("repeated", vec![CodeHash(CryptoHash([2; 32])), CodeHash(CryptoHash([1; 32])), CodeHash(CryptoHash([2; 32]))]);
    f.rand(20, |g| g.vec(6, code_hash));
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedStateWitness>::new("PartialEncodedStateWitness", SEED);
    f.hash(sig_fields_unversioned);
    f.rand(15, |g| {
        let s = signer(g);
        partial_witness(g, &s)
    });
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedStateWitnessV2>::new("PartialEncodedStateWitnessV2", SEED);
    f.hash(sig_fields_unversioned);
    f.rand(15, |g| {
        let s = signer(g);
        partial_witness_v2(g, &s)
    });
    f.finish(m, dir);

    let mut f = Fam::<VersionedPartialEncodedStateWitness>::new("VersionedPartialEncodedStateWitness", SEED);
    f.hash(versioned_fields);
    f.rand(30, |g| {
        let s = signer(g);
        if g.bool() {
            VersionedPartialEncodedStateWitness::V1(partial_witness(g, &s))
        } else {
            VersionedPartialEncodedStateWitness::V2(partial_witness_v2(g, &s))
        }
    });
    f.finish(m, dir);

    let mut f = Fam::<MainTransitionKey>::new("MainTransitionKey", SEED);
    f.rand(8, main_transition);
    f.finish(m, dir);

    let mut f = Fam::<ChunkContractAccesses>::new("ChunkContractAccesses", SEED);
    f.hash(sig_fields);
    f.edge("empty", {
        let s = signer(&mut eg("cca-empty"));
        let inner = ser(&(key(&mut eg("cca-empty-key")), Vec::<CodeHash>::new(), main_transition(&mut eg("cca-empty-m")), "ChunkContractAccessesInner".to_string()));
        signed(Some(0), inner, &s, |v: &ChunkContractAccesses, pk| v.verify_signature(pk))
    });
    f.rand(15, contract_accesses);
    f.finish(m, dir);

    let mut f = Fam::<ContractCodeRequest>::new("ContractCodeRequest", SEED);
    f.hash(sig_fields);
    f.rand(15, code_request);
    f.finish(m, dir);

    let mut f = Fam::<ContractCodeResponseV1>::new("ContractCodeResponseV1", SEED);
    f.edge("empty", ContractCodeResponseV1::encode(key(&mut eg("ccr1")), &vec![]).unwrap());
    f.rand(10, code_response_v1);
    f.finish(m, dir);

    let mut f = Fam::<ContractCodeResponseV2>::new("ContractCodeResponseV2", SEED);
    f.hash(|r: &ContractCodeResponseV2| vec![("sigData", before_signature(&ser(r), 0, 0))]);
    f.rand(10, code_response_v2);
    f.finish(m, dir);

    let mut f = Fam::<ContractCodeResponse>::new("ContractCodeResponse", SEED);
    f.hash(|r: &ContractCodeResponse| {
        let mut v = vec![("key", hex(&ser(r.chunk_production_key())))];
        if let ContractCodeResponse::V2(_) = r {
            v.push(("sigData", before_signature(&ser(r), 1, 0)));
        }
        v
    });
    f.rand(20, |g| {
        if g.bool() {
            ContractCodeResponse::V1(code_response_v1(g))
        } else {
            ContractCodeResponse::V2(code_response_v2(g))
        }
    });
    f.finish(m, dir);

    let mut f = Fam::<ChunkContractDeploys>::new("ChunkContractDeploys", SEED);
    f.rand(8, |g| ChunkContractDeploys::compress_contracts(&contracts(g)).unwrap());
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedContractDeploysPart>::new("PartialEncodedContractDeploysPart", SEED);
    f.rand(10, deploys_part);
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedContractDeploys>::new("PartialEncodedContractDeploys", SEED);
    f.hash(sig_fields);
    f.rand(15, deploys);
    f.finish(m, dir);

    let mut f = Fam::<SpiceChunkContractAccesses>::new("SpiceChunkContractAccesses", SEED);
    f.hash(|a: &SpiceChunkContractAccesses| vec![("sigData", before_signature(&ser(a), 0, 0))]);
    f.rand(15, spice_accesses);
    f.finish(m, dir);

    let mut f = Fam::<SpiceContractCodeRequest>::new("SpiceContractCodeRequest", SEED);
    f.hash(|a: &SpiceContractCodeRequest| vec![("sigData", before_signature(&ser(a), 0, 0))]);
    f.rand(15, spice_request);
    f.finish(m, dir);

    let mut f = Fam::<SpiceContractCodeResponse>::new("SpiceContractCodeResponse", SEED);
    f.rand(10, |g| SpiceContractCodeResponse::encode(spice_id(g), &contracts(g)).unwrap());
    f.finish(m, dir);

    let mut f = Fam::<SpiceChunkStateWitness>::new("SpiceChunkStateWitness", SEED);
    f.rand_with(12, 3, spice_witness);
    f.mutate_up_to(100_000);
    let (c, tr) = (spice_id(&mut eg("sw-raw")), SpiceChunkStateTransition { base_state: partial_state(&mut eg("sw-raw-s")), post_state_root: CryptoHash([5; 32]) });
    let (p1, p2) = (receipt_proof(&mut eg("sw-raw-p1")), receipt_proof(&mut eg("sw-raw-p2")));
    let raw_spice = |entries: Vec<Vec<u8>>| {
        let mut b = vec![0u8];
        b.extend(ser(&(c.clone(), tr.clone())));
        b.extend(map_bytes(entries));
        b.extend(ser(&(CryptoHash([9; 32]), Vec::<SignedTransaction>::new(), ChunkExecutionResultHash(CryptoHash([8; 32])), CryptoHash([7; 32]), None::<EncodedShardChunkBody>)));
        b
    };
    let (a, b2) = (ser(&(ShardId::new(1), p1.clone())), ser(&(ShardId::new(2), p2.clone())));
    f.raw("sorted", raw_spice(vec![a.clone(), b2.clone()]));
    f.raw("unsorted", raw_spice(vec![b2.clone(), a.clone()]));
    f.raw("duplicate", raw_spice(vec![a.clone(), ser(&(ShardId::new(1), p2.clone()))]));
    f.finish(m, dir);

    let mut f = Fam::<SpiceDataIdentifier>::new("SpiceDataIdentifier", SEED);
    f.rand(12, data_id);
    f.finish(m, dir);

    let mut f = Fam::<SpiceDataCommitment>::new("SpiceDataCommitment", SEED);
    f.rand(8, |g| SpiceDataCommitment { hash: g.hash(), root: g.hash(), encoded_length: g.u64() });
    f.finish(m, dir);

    let mut f = Fam::<SpiceDataPart>::new("SpiceDataPart", SEED);
    f.rand(10, data_part);
    f.finish(m, dir);

    let mut f = Fam::<SpicePartialData>::new("SpicePartialData", SEED);
    f.hash(partial_data_fields);
    f.rand(15, partial_data);
    f.finish(m, dir);

    let mut f = Fam::<SpiceVerifiedPartialData>::new("SpiceVerifiedPartialData", SEED);
    f.rand(10, |g| SpiceVerifiedPartialData {
        id: data_id(g),
        commitment: SpiceDataCommitment { hash: g.hash(), root: g.hash(), encoded_length: g.u64() },
        parts: g.vec(3, data_part),
        sender: g.account(),
    });
    f.finish(m, dir);
}

/// A Borsh map from its encoded entries, in the given order.
fn map_bytes(entries: Vec<Vec<u8>>) -> Vec<u8> {
    let mut b = (entries.len() as u32).to_le_bytes().to_vec();
    for e in entries {
        b.extend(e);
    }
    b
}

fn sig_fields_unversioned<T: BorshSerialize>(v: &T) -> Vec<(&'static str, String)> {
    vec![("sigData", before_signature(&ser(v), 0, 0))]
}

/// A distinct label for each independent stream of edge-case values.
fn eg(label: &str) -> G {
    G::new(SEED, label)
}
