//! The signed messages of a validator: approvals, chunk endorsements, partial state witnesses and
//! their acknowledgement, and the zstd frames the node writes.

use crate::chain::*;
use crate::rng::G;
use crate::validator_chunk::{bh, signer_text};
use crate::{hex, Out};
use near_crypto::InMemorySigner;
use near_primitives::block_header::Approval;
use near_primitives::reed_solomon::ReedSolomonEncoder;
use near_primitives::stateless_validation::chunk_endorsement::ChunkEndorsement;
use near_primitives::stateless_validation::partial_witness::VersionedPartialEncodedStateWitness;
use near_primitives::stateless_validation::state_witness::{ChunkStateWitness, ChunkStateWitnessAck, EncodedChunkStateWitness};
use near_primitives::types::AccountId;
use near_primitives::utils::compression::CompressedData;
use near_primitives::validator_signer::{InMemoryValidatorSigner, ValidatorSigner};
use near_primitives::version::PROTOCOL_VERSION;
use serde_json::json;

fn signer(seed: &str, account: &str) -> (ValidatorSigner, String, String) {
    let sk = signer_text(seed);
    let id: AccountId = account.parse().unwrap();
    let s = InMemoryValidatorSigner::from_signer(InMemorySigner::from_secret_key(id, sk.clone()));
    (s, account.to_string(), sk.to_string())
}

pub fn messages(out: &mut Out) {
    let mut g = G::new(0x4d53_4753, "validator/messages");
    // Approvals: endorsements and skips.
    for i in 0..24 {
        let (s, account, secret) = signer(&format!("approver-{i}"), &format!("validator{}.test", i % 5));
        let parent_hash = g.hash();
        let parent_height = g.u64().min(u64::MAX - 100);
        let target = match i % 3 {
            0 => parent_height + 1,
            1 => parent_height + 2 + g.below(5) as u64,
            _ => parent_height + 1,
        };
        let a = Approval::new(parent_hash, parent_height, target, &s);
        out.line("approval", json!({
            "account": account, "secret": secret, "parentHash": hex(&parent_hash.0),
            "parentHeight": parent_height, "targetHeight": target, "approval": bh(&a),
        }));
    }
    // Chunk endorsements.
    for i in 0..12 {
        let (s, account, secret) = signer(&format!("endorser-{i}"), &format!("validator{}.test", i % 5));
        let header = modern_chunk_header(&mut g);
        let epoch = epoch_id(&mut g);
        let e = ChunkEndorsement::new(epoch, &header, &s);
        out.line("endorsement", json!({
            "account": account, "secret": secret, "epochId": bh(&epoch), "header": bh(&header),
            "endorsement": bh(&e),
        }));
    }
    // Partial encoded state witnesses, built one at a time and by `generate_state_witness_parts`.
    for i in 0..10 {
        let (s, account, secret) = signer(&format!("witness-{i}"), &format!("producer{}.test", i % 3));
        let header = modern_chunk_header(&mut g);
        let epoch = epoch_id(&mut g);
        let part = g.bytes(300);
        let ord = g.below(12);
        let length = part.len() + g.below(50);
        let w = VersionedPartialEncodedStateWitness::new(epoch, header.clone(), ord, part.clone(), length, &s, PROTOCOL_VERSION);
        out.line("partial-witness", json!({
            "account": account, "secret": secret, "epochId": bh(&epoch), "header": bh(&header),
            "partOrd": ord, "part": hex(&part), "encodedLength": length, "witness": bh(&w),
        }));
    }
    for n in 1..=8usize {
        for len in [0usize, 1, 100, 5000] {
            let (s, account, secret) = signer(&format!("witness-parts-{n}-{len}"), "producer.test");
            let header = modern_chunk_header(&mut g);
            let epoch = epoch_id(&mut g);
            let bytes: Vec<u8> = (0..len).map(|_| g.below(256) as u8).collect();
            let encoded = EncodedChunkStateWitness::from_boxed_slice(bytes.clone().into_boxed_slice());
            let validators: Vec<AccountId> = (0..n).map(|k| format!("cv{k}.test").parse().unwrap()).collect();
            // generate_state_witness_parts (chain/client/.../partial_witness_actor.rs)
            let encoder = ReedSolomonEncoder::new(n, 0.6);
            let (parts, encoded_length) = encoder.encode(&encoded);
            let witnesses: Vec<String> = parts
                .into_iter()
                .enumerate()
                .map(|(ord, part)| {
                    bh(&VersionedPartialEncodedStateWitness::new(
                        epoch,
                        header.clone(),
                        ord,
                        part.unwrap().into_vec(),
                        encoded_length,
                        &s,
                        PROTOCOL_VERSION,
                    ))
                })
                .collect();
            out.line("witness-parts", json!({
                "account": account, "secret": secret, "epochId": bh(&epoch), "header": bh(&header),
                "validators": validators.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
                "bytes": hex(&bytes), "witnesses": witnesses,
            }));
        }
    }
    // The acknowledgement.
    for _ in 0..4 {
        let header = modern_chunk_header(&mut g);
        let witness = ChunkStateWitness::new(
            epoch_id(&mut g),
            header.clone(),
            Default::default(),
            Default::default(),
            g.hash(),
            vec![],
            vec![],
            vec![],
        );
        out.line("witness-ack", json!({"header": bh(&header), "ack": bh(&ChunkStateWitnessAck::new(&witness))}));
    }
}

/// Reads JSON lines `{"input": hex, "frame": hex}` from `path` and checks that the `zstd` crate
/// decodes every frame to its input.
pub fn verify_zstd(path: &str) {
    let text = std::fs::read_to_string(path).unwrap();
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let v: serde_json::Value = serde_json::from_str(line).unwrap();
        let input = unhex(v["input"].as_str().unwrap());
        let frame = unhex(v["frame"].as_str().unwrap());
        let decoded = zstd::stream::decode_all(&frame[..]).unwrap_or_else(|e| panic!("frame {n}: {e}"));
        assert_eq!(decoded, input, "frame {n}");
        // the way the witness is decoded: a streaming decoder with the Borsh reader on top
        let mut dec = zstd::stream::Decoder::new(&frame[..]).unwrap();
        let mut buf = vec![];
        std::io::Read::read_to_end(&mut dec, &mut buf).unwrap();
        assert_eq!(buf, input, "frame {n} (stream)");
        n += 1;
    }
    println!("zstd: {n} frames decoded by the zstd crate");
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}
