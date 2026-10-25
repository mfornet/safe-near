//! Block production: `Block::produce` (`core/primitives/src/block.rs`) over a previous header, chunk
//! headers, endorsements and approvals, with a fake clock.

use crate::chain::*;
use crate::rng::G;
use crate::validator_chunk::{bh, signer_text};
use crate::{hex, Out};
use near_crypto::{InMemorySigner, KeyType, Signature};
use near_primitives::block::Block;
use near_primitives::block_header::BlockHeader;
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::{ChunkHash, ShardChunkHeader, ShardChunkHeaderInner, ShardChunkHeaderV3};
use near_primitives::stateless_validation::chunk_endorsements_bitmap::ChunkEndorsementsBitmap;
use near_primitives::types::{AccountId, Balance, EpochId, Gas};
use near_primitives::validator_signer::InMemoryValidatorSigner;
use near_primitives::version::PROTOCOL_VERSION;
use near_primitives_core::num_rational::Rational32;
use serde_json::json;

fn chunk_header(g: &mut G, signer: &near_primitives::validator_signer::ValidatorSigner, height: u64, included: bool) -> ShardChunkHeader {
    let mut inner = if g.bool() {
        ShardChunkHeaderInner::V4(inner_v4(g))
    } else {
        ShardChunkHeaderInner::V5(inner_v5(g))
    };
    let small = |g: &mut G| Gas::from_gas(g.below(1_000_000) as u64 * 1_000_000);
    match &mut inner {
        ShardChunkHeaderInner::V4(i) => {
            i.prev_gas_used = small(g);
            i.gas_limit = Gas::from_gas(1_000_000_000_000_000);
            i.prev_balance_burnt = Balance::from_yoctonear(g.below(1_000_000) as u128);
            i.height_created = height - 1;
        }
        ShardChunkHeaderInner::V5(i) => {
            i.prev_gas_used = small(g);
            i.gas_limit = Gas::from_gas(1_000_000_000_000_000);
            i.prev_balance_burnt = Balance::from_yoctonear(g.below(1_000_000) as u128);
            i.height_created = height - 1;
        }
        _ => unreachable!(),
    }
    let mut h = ShardChunkHeaderV3 {
        inner,
        height_included: if included { height } else { height - 1 - g.below(3) as u64 },
        signature: Signature::empty(KeyType::ED25519),
        hash: ChunkHash::default(),
    };
    h.init();
    h.signature = signer.sign_bytes(h.hash.as_ref());
    ShardChunkHeader::V3(h)
}

pub fn blocks(out: &mut Out) {
    let mut g = G::new(0x424c_4f43, "validator/blocks");
    let rate = Rational32::new(1, 100);
    let (min_price, max_price) = (Balance::from_yoctonear(100_000_000), Balance::from_yoctonear(10u128.pow(24)));
    for case in 0..40 {
        let seed = format!("block-producer-{}", case % 4);
        let sk = signer_text(&seed);
        let account: AccountId = format!("producer{}.test", case % 4).parse().unwrap();
        let signer = InMemoryValidatorSigner::from_signer(InMemorySigner::from_secret_key(account.clone(), sk.clone()));
        let n_shards = 1 + g.below(4);
        let prev_height = 1000 + g.below(1000) as u64;
        let prev_hash_of_prev = g.hash();
        let prev_timestamp = 1_700_000_000_000_000_000u64 + g.below(1 << 30) as u64;
        let prev_ordinal = 500 + g.below(100) as u64;
        // the previous header, itself a real one
        let prev_self_hash_placeholder = g.hash();
        let _ = prev_self_hash_placeholder;
        let ds_final_is_prev = g.bool();
        let prev_last_ds = if ds_final_is_prev { prev_hash_of_prev } else { g.hash() };
        let prev = BlockHeader::new(
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
            prev_height,
            prev_hash_of_prev,
            g.hash(),
            g.hash(),
            g.hash(),
            g.hash(),
            g.hash(),
            g.hash(),
            prev_timestamp,
            g.hash(),
            vec![],
            vec![true; n_shards],
            prev_ordinal,
            epoch_id(&mut g),
            epoch_id(&mut g),
            Balance::from_yoctonear(1_000_000_000 + g.below(1 << 30) as u128),
            Balance::from_yoctonear(10u128.pow(27) + g.below(1 << 30) as u128),
            &signer,
            g.hash(),
            prev_last_ds,
            Some(g.hash()),
            vec![],
            g.hash(),
            g.hash(),
            prev_height - 1,
            Some(ChunkEndorsementsBitmap::from_endorsements(vec![vec![true]; n_shards])),
            None,
            None,
            None,
        );
        let skip = if case % 3 == 0 { 0 } else { g.below(4) as u64 };
        let height = prev_height + 1 + skip;
        let chunks: Vec<ShardChunkHeader> = (0..n_shards)
            .map(|_| {
                let included = g.below(3) != 0;
                chunk_header(&mut g, &signer, height, included)
            })
            .collect();
        let endorsements: Vec<Vec<Option<Box<Signature>>>> = (0..n_shards)
            .map(|_| (0..g.below(5)).map(|_| if g.bool() { Some(Box::new(sign_msg(&mut g, b"endorse"))) } else { None }).collect())
            .collect();
        let approvals: Vec<Option<Box<Signature>>> = (0..g.below(5))
            .map(|_| if g.bool() { Some(Box::new(sign_msg(&mut g, b"approve"))) } else { None })
            .collect();
        let epoch = epoch_id(&mut g);
        let next_epoch = epoch_id(&mut g);
        let next_bp = g.hash();
        let merkle_root = g.hash();
        let sync_hash = if g.bool() { Some(g.hash()) } else { None };
        let minted = if g.below(4) == 0 { Some(Balance::from_yoctonear(g.below(1 << 30) as u128)) } else { None };
        let split = if g.below(5) == 0 { Some((near_primitives::types::ShardId::new(g.below(4) as u64), format!("split{}.test", g.below(3)).parse::<AccountId>().unwrap())) } else { None };
        let now = match case % 4 {
            0 => prev_timestamp.saturating_sub(5),
            1 => prev_timestamp,
            2 => prev_timestamp + 7,
            _ => prev_timestamp + 1_000_000_000,
        };
        let fake = near_time::FakeClock::new(near_time::Utc::from_unix_timestamp_nanos(now as i128).unwrap());
        let block = Block::produce(
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
            &prev,
            height,
            prev_ordinal + 1,
            chunks.clone(),
            endorsements.clone(),
            epoch,
            next_epoch,
            sync_hash,
            approvals.clone(),
            rate,
            min_price,
            max_price,
            minted,
            &signer.clone().into(),
            next_bp,
            merkle_root,
            fake.clock(),
            None,
            None,
            split.clone(),
            None,
        );
        out.line("block", json!({
            "protocol": PROTOCOL_VERSION,
            "account": account.to_string(),
            "secret": sk.to_string(),
            "prev": bh(&prev),
            "height": height,
            "blockOrdinal": prev_ordinal + 1,
            "chunks": bh(&chunks),
            "chunkEndorsements": bh(&endorsements),
            "epochId": bh(&epoch),
            "nextEpochId": bh(&next_epoch),
            "epochSyncDataHash": bh(&sync_hash),
            "approvals": bh(&approvals),
            "rate": [1, 100],
            "minGasPrice": min_price.as_yoctonear().to_string(),
            "maxGasPrice": max_price.as_yoctonear().to_string(),
            "mintedAmount": bh(&minted),
            "nextBpHash": hex(&next_bp.0),
            "blockMerkleRoot": hex(&merkle_root.0),
            "now": now,
            "shardSplit": bh(&split),
            "block": bh(&block),
            "hash": hex(&block.header().hash().0),
        }));
        let _: &CryptoHash = block.header().hash();
        let _ = EpochId::default();
    }
}
