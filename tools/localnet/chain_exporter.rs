//! Block-sequence exporter for a stopped neard localnet (build-time overlay on `state-viewer`).
//!
//! Writes, for one node database, everything the Lean chain validator needs and everything the
//! node itself concluded:
//!
//! * `meta.json`: genesis parameters, the economics configuration, the validator keys used for
//!   the invalid variants;
//! * `blocks.jsonl`: every block from genesis to the head (Borsh) with the values neard derived
//!   and stored for it (`BlockInfo`, block merkle tree, `ChunkExtra` per shard, the approvers
//!   `EpochManager` ordered, the block and chunk producers, the chunk validator assignments);
//! * `epochs.jsonl`: the `EpochInfo` and the shard layout of every epoch id the blocks mention;
//! * `variants.jsonl`: deliberately invalid blocks made from valid ones, each with the verdict of
//!   the pinned `Chain::start_process_block_async` (the entry point that runs `validate_header`,
//!   `validate_block` and `preprocess_block`) on the exact chain state that precedes the base block.
//!
//! The chain code writes small bookkeeping (processed heights, invalid blocks) even when it
//! rejects a block, so run it on a copy of the node directory with `--writable`.
//!
//! Usage: safe-near-chain-export --home DIR --out DIR [--key FILE]... [--bases N] [--seed S] [--writable]
use anyhow::{Context, Result, anyhow, bail};
use borsh::to_vec as borsh_bytes;
use near_chain::{
    BlockProcessingArtifact, Chain, ChainGenesis, ChainStore, ChainStoreAccess, DoomslugThresholdMode,
    Provenance,
};
use near_chain_configs::GenesisValidationMode;
use near_crypto::{InMemorySigner, Signature, Signer};
use near_epoch_manager::shard_tracker::ShardTracker;
use near_epoch_manager::{EpochManager, EpochManagerAdapter};
use near_primitives::block::{Block, BlockHeader};
use near_primitives::block_body::BlockBody;
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::ShardChunkHeader;
use near_primitives::types::EpochId;
use near_primitives::utils::MaybeValidated;
use near_store::{Mode, NodeStorage};
use near_time::Clock;
use nearcore::{NightshadeRuntimeExt, load_config};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::io::Write;
use std::path::PathBuf;
use std::sync::Arc;

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        text.push(DIGITS[(byte >> 4) as usize] as char);
        text.push(DIGITS[(byte & 15) as usize] as char);
    }
    text
}

fn hash_hex(hash: &CryptoHash) -> String {
    hex(hash.as_ref())
}

fn sid(id: near_primitives::types::ShardId) -> u64 {
    id.to_string().parse().expect("shard ids are numbers")
}

struct Args {
    home: PathBuf,
    out: PathBuf,
    keys: Vec<PathBuf>,
    bases: usize,
    seed: u64,
    writable: bool,
}

fn parse_args() -> Result<Args> {
    let (mut home, mut out, mut keys, mut bases, mut seed, mut writable) =
        (None, None, Vec::new(), 24usize, 1u64, false);
    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        let mut value = || args.next().ok_or_else(|| anyhow!("{flag} needs a value"));
        match flag.as_str() {
            "--home" => home = Some(PathBuf::from(value()?)),
            "--out" => out = Some(PathBuf::from(value()?)),
            "--key" => keys.push(PathBuf::from(value()?)),
            "--bases" => bases = value()?.parse()?,
            "--seed" => seed = value()?.parse()?,
            "--writable" => writable = true,
            other => bail!("unknown argument {other}"),
        }
    }
    Ok(Args { home: home.context("--home")?, out: out.context("--out")?, keys, bases, seed, writable })
}

/// A deterministic generator (SplitMix64) so the choice of base blocks is a function of the seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_3C0F_B6A9);
        z ^ (z >> 31)
    }
}

/// The variant name of an error, without its payload.
fn error_kind(error: &near_chain::Error) -> String {
    let text = format!("{error:?}");
    text.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect()
}

struct Context_ {
    chain: Chain,
    chain_store: ChainStore,
    epoch_manager: Arc<near_epoch_manager::EpochManagerHandle>,
    signers: Vec<(String, Signer)>,
}

impl Context_ {
    fn signer_for(&self, account: &str) -> Option<&Signer> {
        self.signers.iter().find(|(a, _)| a == account).map(|(_, s)| s)
    }

    fn producer(&self, block: &Block) -> Result<String> {
        Ok(self
            .epoch_manager
            .get_block_producer(block.header().epoch_id(), block.header().height())?
            .to_string())
    }
}

/// Re-derive what the producer would derive after the body changed, and sign: the block body hash,
/// the cached hash and the signature.
fn finalize(block: &mut Block, signer: &Signer) -> Result<()> {
    let body_hash = block.compute_block_body_hash().context("block body hash")?;
    let Block::BlockV4(b) = block else { bail!("only block V4 is supported") };
    let BlockHeader::BlockHeaderV6(h) = &mut b.header else { bail!("only header V6 is supported") };
    h.inner_rest.block_body_hash = body_hash;
    h.init();
    h.signature = signer.sign(h.hash.as_ref());
    Ok(())
}

/// Rebuild a block through Borsh so every cached hash (header and chunk headers) is recomputed.
fn reload(block: &Block) -> Result<Block> {
    Ok(borsh::from_slice(&borsh_bytes(block)?)?)
}

fn header_v6(block: &mut Block) -> Result<&mut near_primitives::block_header::BlockHeaderV6> {
    let Block::BlockV4(b) = block else { bail!("only block V4 is supported") };
    let BlockHeader::BlockHeaderV6(h) = &mut b.header else { bail!("only header V6 is supported") };
    Ok(h)
}

fn body_v2(block: &mut Block) -> Result<&mut near_primitives::block_body::BlockBodyV2> {
    let Block::BlockV4(b) = block else { bail!("only block V4 is supported") };
    let BlockBody::V2(body) = &mut b.body else { bail!("only block body V2 is supported") };
    Ok(body)
}

fn flip_signature(signature: &Signature) -> Signature {
    let mut bytes = borsh_bytes(signature).expect("signature");
    let last = bytes.len() - 2;
    bytes[last] ^= 1;
    borsh::from_slice(&bytes).expect("signature")
}

type Mutation = fn(&Context_, &Block, &Block) -> Result<Option<(Block, Option<String>)>>;

/// One kind of invalid variant: its name, what it tests, and the function building it from a base
/// block (and the previous block). The optional string names the account whose key re-signs the
/// header; `None` leaves the original signature (the variant is then rejected by the signature check).
struct Kind {
    name: &'static str,
    build: Mutation,
}

/// Sign as the producer of the (possibly mutated) header's epoch and height; when that producer is
/// unknown or has no key here (a mutated epoch id, say), as the producer of the base block.
fn sign_as_producer(ctx: &Context_, block: &mut Block, base: &Block) -> Result<()> {
    let producer = match ctx.producer(block) {
        Ok(account) if ctx.signer_for(&account).is_some() => account,
        _ => ctx.producer(base)?,
    };
    let signer = ctx.signer_for(&producer).with_context(|| format!("no key for producer {producer}"))?;
    finalize(block, signer)
}

/// Build the variants of one base block.
fn kinds() -> Vec<Kind> {
    macro_rules! header_kind {
        ($name:expr, |$ctx:ident, $b:ident, $prev:ident, $h:ident| $body:block) => {
            Kind {
                name: $name,
                build: |$ctx, $b, $prev| {
                    let mut block = $b.clone();
                    {
                        let $h = header_v6(&mut block)?;
                        let _ = &$prev;
                        let ok: bool = $body;
                        if !ok {
                            return Ok(None);
                        }
                    }
                    sign_as_producer($ctx, &mut block, $b)?;
                    Ok(Some((reload(&block)?, None)))
                },
            }
        };
    }
    vec![
        Kind {
            name: "bad-signature",
            build: |_, b, _| {
                let mut block = b.clone();
                let h = header_v6(&mut block)?;
                h.signature = flip_signature(&h.signature);
                Ok(Some((block, None)))
            },
        },
        Kind {
            name: "wrong-signer",
            build: |ctx, b, _| {
                let producer = ctx.producer(b)?;
                let Some((_, other)) = ctx.signers.iter().find(|(a, _)| *a != producer) else {
                    // a single validator: sign with a key that is not in the epoch at all
                    let other = InMemorySigner::from_seed(
                        "intruder".parse().unwrap(),
                        near_crypto::KeyType::ED25519,
                        "intruder",
                    );
                    let mut block = b.clone();
                    finalize(&mut block, &other)?;
                    return Ok(Some((reload(&block)?, None)));
                };
                let mut block = b.clone();
                finalize(&mut block, other)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "tampered-body",
            build: |_, b, _| {
                let mut block = b.clone();
                let body = body_v2(&mut block)?;
                let mut proof = borsh_bytes(&body.vrf_proof)?;
                proof[0] ^= 1;
                body.vrf_proof = borsh::from_slice(&proof)?;
                Ok(Some((block, None)))
            },
        },
        header_kind!("wrong-prev-hash", |ctx, b, prev, h| {
            // the grandparent: an existing block that is not the parent
            let grandparent = *prev.header().prev_hash();
            if grandparent == CryptoHash::default() {
                false
            } else {
                h.prev_hash = grandparent;
                true
            }
        }),
        header_kind!("unknown-prev-hash", |ctx, b, prev, h| {
            h.prev_hash = CryptoHash::hash_bytes(b"no such block");
            true
        }),
        header_kind!("height-plus-one", |ctx, b, prev, h| {
            h.inner_lite.height += 1;
            true
        }),
        header_kind!("height-equals-prev", |ctx, b, prev, h| {
            h.inner_lite.height = prev.header().height();
            true
        }),
        header_kind!("timestamp-not-after-prev", |ctx, b, prev, h| {
            h.inner_lite.timestamp = prev.header().raw_timestamp();
            true
        }),
        header_kind!("wrong-epoch-id", |ctx, b, prev, h| {
            h.inner_lite.epoch_id = EpochId(CryptoHash::hash_bytes(b"epoch"));
            true
        }),
        header_kind!("wrong-next-epoch-id", |ctx, b, prev, h| {
            h.inner_lite.next_epoch_id = EpochId(CryptoHash::hash_bytes(b"next epoch"));
            true
        }),
        header_kind!("wrong-next-bp-hash", |ctx, b, prev, h| {
            h.inner_lite.next_bp_hash = CryptoHash::hash_bytes(b"bp");
            true
        }),
        header_kind!("no-approvals", |ctx, b, prev, h| {
            let n = h.inner_rest.approvals.len();
            h.inner_rest.approvals = vec![None; n];
            n > 0
        }),
        header_kind!("too-many-approvals", |ctx, b, prev, h| {
            let n = h.inner_rest.approvals.len();
            h.inner_rest.approvals = vec![None; n + 1];
            true
        }),
        header_kind!("bad-approval-signature", |ctx, b, prev, h| {
            let mut done = false;
            for slot in h.inner_rest.approvals.iter_mut() {
                if let Some(signature) = slot {
                    **signature = flip_signature(signature);
                    done = true;
                    break;
                }
            }
            done
        }),
        header_kind!("wrong-last-final-block", |ctx, b, prev, h| {
            h.inner_rest.last_final_block = CryptoHash::hash_bytes(b"final");
            true
        }),
        header_kind!("wrong-last-ds-final-block", |ctx, b, prev, h| {
            h.inner_rest.last_ds_final_block = CryptoHash::hash_bytes(b"ds final");
            true
        }),
        header_kind!("wrong-block-merkle-root", |ctx, b, prev, h| {
            h.inner_lite.block_merkle_root = CryptoHash::hash_bytes(b"merkle");
            true
        }),
        header_kind!("wrong-block-ordinal", |ctx, b, prev, h| {
            h.inner_rest.block_ordinal += 1;
            true
        }),
        header_kind!("wrong-gas-price", |ctx, b, prev, h| {
            h.inner_rest.next_gas_price = near_primitives::types::Balance::from_yoctonear(
                h.inner_rest.next_gas_price.as_yoctonear() + 1,
            );
            true
        }),
        header_kind!("wrong-total-supply", |ctx, b, prev, h| {
            h.inner_rest.total_supply = near_primitives::types::Balance::from_yoctonear(
                h.inner_rest.total_supply.as_yoctonear() + 1,
            );
            true
        }),
        header_kind!("wrong-random-value", |ctx, b, prev, h| {
            h.inner_rest.random_value = CryptoHash::hash_bytes(b"random");
            true
        }),
        header_kind!("wrong-chunk-mask", |ctx, b, prev, h| {
            if let Some(first) = h.inner_rest.chunk_mask.first_mut() {
                *first = !*first;
                true
            } else {
                false
            }
        }),
        header_kind!("short-chunk-mask", |ctx, b, prev, h| {
            h.inner_rest.chunk_mask.pop().is_some()
        }),
        header_kind!("wrong-chunk-headers-root", |ctx, b, prev, h| {
            h.inner_rest.chunk_headers_root = CryptoHash::hash_bytes(b"chunks");
            true
        }),
        header_kind!("wrong-prev-state-root", |ctx, b, prev, h| {
            h.inner_lite.prev_state_root = CryptoHash::hash_bytes(b"state");
            true
        }),
        header_kind!("wrong-tx-root", |ctx, b, prev, h| {
            h.inner_rest.chunk_tx_root = CryptoHash::hash_bytes(b"tx");
            true
        }),
        header_kind!("wrong-receipts-root", |ctx, b, prev, h| {
            h.inner_rest.prev_chunk_outgoing_receipts_root = CryptoHash::hash_bytes(b"receipts");
            true
        }),
        header_kind!("wrong-prev-height", |ctx, b, prev, h| {
            h.inner_rest.prev_height += 1;
            true
        }),
        header_kind!("wrong-epoch-sync-data-hash", |ctx, b, prev, h| {
            h.inner_rest.epoch_sync_data_hash = match h.inner_rest.epoch_sync_data_hash {
                Some(_) => None,
                None => Some(CryptoHash::hash_bytes(b"sync")),
            };
            true
        }),
        header_kind!("wrong-validator-proposals", |ctx, b, prev, h| {
            h.inner_rest.prev_validator_proposals.push(
                near_primitives::types::validator_stake::ValidatorStake::new(
                    "intruder".parse().unwrap(),
                    near_crypto::PublicKey::empty(near_crypto::KeyType::ED25519),
                    near_primitives::types::Balance::from_yoctonear(1),
                ),
            );
            true
        }),
        header_kind!("wrong-protocol-version", |ctx, b, prev, h| {
            h.inner_rest.latest_protocol_version = 1;
            true
        }),
        header_kind!("wrong-endorsement-bitmap", |ctx, b, prev, h| {
            h.inner_rest.chunk_endorsements = Default::default();
            true
        }),
        Kind {
            name: "bad-vrf-proof",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let body = body_v2(&mut block)?;
                let mut proof = borsh_bytes(&body.vrf_proof)?;
                proof[0] ^= 1;
                body.vrf_proof = borsh::from_slice(&proof)?;
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "bad-vrf-value",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let body = body_v2(&mut block)?;
                let mut value = borsh_bytes(&body.vrf_value)?;
                value[0] ^= 1;
                body.vrf_value = borsh::from_slice(&value)?;
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "bad-chunk-signature",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let height = block.header().height();
                let body = body_v2(&mut block)?;
                let Some(chunk) = body.chunks.iter_mut().find(|c| c.is_new_chunk(height)) else {
                    return Ok(None);
                };
                match chunk {
                    ShardChunkHeader::V3(h) => h.signature = flip_signature(&h.signature),
                    _ => return Ok(None),
                }
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "chunk-wrong-prev-block-hash",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let height = block.header().height();
                let body = body_v2(&mut block)?;
                let Some(chunk) = body.chunks.iter_mut().find(|c| c.is_new_chunk(height)) else {
                    return Ok(None);
                };
                match chunk {
                    ShardChunkHeader::V3(h) => {
                        let mut bytes = borsh_bytes(&h.inner)?;
                        // ShardChunkHeaderInner is tagged; the prev block hash follows the tag.
                        bytes[1] ^= 1;
                        h.inner = borsh::from_slice(&bytes)?;
                    }
                    _ => return Ok(None),
                }
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "bad-endorsement-signature",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let body = body_v2(&mut block)?;
                for shard in body.chunk_endorsements.iter_mut() {
                    for slot in shard.iter_mut() {
                        if let Some(signature) = slot {
                            **signature = flip_signature(signature);
                            sign_as_producer(ctx, &mut block, b)?;
                            return Ok(Some((reload(&block)?, None)));
                        }
                    }
                }
                Ok(None)
            },
        },
        Kind {
            name: "missing-endorsements",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let body = body_v2(&mut block)?;
                let mut changed = false;
                for shard in body.chunk_endorsements.iter_mut() {
                    for slot in shard.iter_mut() {
                        changed |= slot.take().is_some();
                    }
                }
                if !changed {
                    return Ok(None);
                }
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "endorsements-for-old-chunk",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let height = block.header().height();
                let chunks = block.chunks().iter_raw().map(|c| c.is_new_chunk(height)).collect::<Vec<_>>();
                let body = body_v2(&mut block)?;
                let Some(index) = chunks.iter().position(|new| !*new) else { return Ok(None) };
                let donor = body.chunk_endorsements.iter().find(|s| !s.is_empty()).cloned();
                let Some(donor) = donor else { return Ok(None) };
                body.chunk_endorsements[index] = donor;
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
        Kind {
            name: "missing-chunk-endorsement-shard",
            build: |ctx, b, _| {
                let mut block = b.clone();
                let body = body_v2(&mut block)?;
                if body.chunk_endorsements.pop().is_none() {
                    return Ok(None);
                }
                sign_as_producer(ctx, &mut block, b)?;
                Ok(Some((reload(&block)?, None)))
            },
        },
    ]
}

fn verdict(chain: &mut Chain, block: &Block) -> Result<Value> {
    let mut artifacts = BlockProcessingArtifact::default();
    let result = chain.start_process_block_async(
        MaybeValidated::from(Arc::new(block.clone())),
        Provenance::NONE,
        &mut artifacts,
        None,
    );
    match result {
        Ok(()) => bail!("a variant was accepted by nearcore: the generator is wrong"),
        Err(error) => Ok(json!({"accepted": false, "error": error_kind(&error), "message": format!("{error:?}")})),
    }
}

fn main() -> Result<()> {
    let args = parse_args()?;
    let near_config = load_config(&args.home, GenesisValidationMode::Full)
        .map_err(|e| anyhow!("loading config: {e:#}"))?;
    let opener = NodeStorage::opener(
        &args.home,
        &near_config.config.store,
        near_config.config.cold_store.as_ref(),
        near_config.cloud_storage_context(),
    );
    let storage = opener.open_in_mode(if args.writable { Mode::ReadWriteExisting } else { Mode::ReadOnly })?;
    let store = storage.get_hot_store();
    let epoch_manager =
        EpochManager::new_arc_handle(store.clone(), &near_config.genesis.config, Some(&args.home));
    let runtime = nearcore::NightshadeRuntime::from_config(
        &args.home,
        store.clone(),
        &near_config,
        epoch_manager.clone(),
    )?;
    let shard_tracker = ShardTracker::new(
        near_config.client_config.tracked_shards_config.clone(),
        epoch_manager.clone(),
        near_config.validator_signer.clone(),
    );
    let chain_genesis = ChainGenesis::new(&near_config.genesis.config);
    let chain = Chain::new_for_view_client(
        Clock::real(),
        epoch_manager.clone(),
        shard_tracker,
        runtime,
        &chain_genesis,
        DoomslugThresholdMode::TwoThirds,
        false,
        near_config.validator_signer.clone(),
    )?;
    let chain_store =
        ChainStore::new(store.clone(), false, near_config.genesis.config.transaction_validity_period);
    std::fs::create_dir_all(&args.out)?;

    let mut signers = Vec::new();
    for path in &args.keys {
        let signer = InMemorySigner::from_file(path).with_context(|| format!("key file {}", path.display()))?;
        let text = std::fs::read_to_string(path)?;
        let account = serde_json::from_str::<Value>(&text)?["account_id"]
            .as_str()
            .context("account_id")?
            .to_string();
        signers.push((account, signer));
    }
    let mut ctx = Context_ { chain, chain_store, epoch_manager: epoch_manager.clone(), signers };

    // The canonical chain, genesis to head.
    let head = ctx.chain_store.head()?;
    let genesis_height = near_config.genesis.config.genesis_height;
    let mut blocks_out = std::io::BufWriter::new(std::fs::File::create(args.out.join("blocks.jsonl"))?);
    let mut epoch_ids: BTreeSet<[u8; 32]> = BTreeSet::new();
    let mut hashes = Vec::new();
    let mut blocks = Vec::new();
    for height in genesis_height..=head.height {
        let Ok(hash) = ctx.chain_store.get_block_hash_by_height(height) else { continue };
        let block = ctx.chain_store.get_block(&hash)?;
        hashes.push(hash);
        blocks.push(block);
    }
    for (index, block) in blocks.iter().enumerate() {
        let header = block.header();
        let hash = *header.hash();
        let height = header.height();
        epoch_ids.insert(header.epoch_id().0.0);
        epoch_ids.insert(header.next_epoch_id().0.0);
        let is_genesis = header.is_genesis();
        let block_info = epoch_manager.get_block_info(&hash)?;
        let tree = ctx.chain_store.get_block_merkle_tree(&hash)?;
        let epoch_id = *header.epoch_id();
        let mut chunk_extras = Vec::new();
        let mut chunk_producers = Vec::new();
        let mut chunk_validators = Vec::new();
        let mut approvers = Value::Null;
        let mut block_producer = Value::Null;
        if !is_genesis {
            let layout = epoch_manager.get_shard_layout(&epoch_id)?;
            for shard_id in layout.shard_ids() {
                let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(shard_id, &layout);
                if let Ok(extra) = ctx.chain_store.get_chunk_extra(&hash, &uid) {
                    chunk_extras.push(json!([sid(shard_id), hex(&borsh_bytes(&*extra)?)]));
                }
            }
            for (shard_index, chunk) in block.chunks().iter_raw().enumerate() {
                let shard_id = layout.get_shard_id(shard_index)?;
                if chunk.is_new_chunk(height) {
                    let producer = epoch_manager.get_chunk_producer_info_db(header.prev_hash(), shard_id)?;
                    chunk_producers.push(json!([sid(shard_id), producer.account_id().to_string()]));
                    let assignments =
                        epoch_manager.get_chunk_validator_assignments(&epoch_id, shard_id, chunk.height_created())?;
                    let rows: Vec<Value> = assignments
                        .assignments()
                        .iter()
                        .map(|(account, stake)| json!([account.to_string(), stake.as_yoctonear().to_string()]))
                        .collect();
                    chunk_validators.push(json!([sid(shard_id), rows]));
                }
            }
            let ordered = epoch_manager.get_epoch_block_approvers_ordered(header.prev_hash())?;
            approvers = Value::Array(
                ordered
                    .iter()
                    .map(|a| {
                        json!([
                            a.account_id.to_string(),
                            a.stake_this_epoch.as_yoctonear().to_string(),
                            a.stake_next_epoch.as_yoctonear().to_string()
                        ])
                    })
                    .collect(),
            );
            block_producer = json!(epoch_manager.get_block_producer(&epoch_id, height)?.to_string());
        }
        let next_is_epoch_start = epoch_manager.is_next_block_epoch_start(&hash)?;
        let line = json!({
            "height": height,
            "hash": hash_hex(&hash),
            "prevHash": hash_hex(header.prev_hash()),
            "isGenesis": is_genesis,
            "block": hex(&borsh_bytes(&**block)?),
            "derived": {
                "blockInfo": hex(&borsh_bytes(&*block_info)?),
                "blockMerkleTree": hex(&borsh_bytes(&*tree)?),
                "blockMerkleRoot": hash_hex(&tree.root()),
                "blockProducer": block_producer,
                "approvers": approvers,
                "chunkProducers": chunk_producers,
                "chunkValidators": chunk_validators,
                "chunkExtras": chunk_extras,
                "nextBlockStartsEpoch": next_is_epoch_start,
                "epochId": hash_hex(&epoch_id.0),
                "nextEpochId": hash_hex(&header.next_epoch_id().0),
            },
            "index": index,
        });
        writeln!(blocks_out, "{}", serde_json::to_string(&line)?)?;
    }
    blocks_out.flush()?;

    // Epochs.
    let mut epochs_out = std::io::BufWriter::new(std::fs::File::create(args.out.join("epochs.jsonl"))?);
    for id in &epoch_ids {
        let epoch_id = EpochId(CryptoHash(*id));
        let Ok(info) = epoch_manager.get_epoch_info(&epoch_id) else { continue };
        let layout = epoch_manager.get_shard_layout(&epoch_id)?;
        let line = json!({
            "epochId": hex(id),
            "epochInfo": hex(&borsh_bytes(&*info)?),
            "shardLayout": hex(&borsh_bytes(&layout)?),
            "protocolVersion": info.protocol_version(),
            "epochHeight": info.epoch_height(),
        });
        writeln!(epochs_out, "{}", serde_json::to_string(&line)?)?;
    }
    epochs_out.flush()?;

    // Variants.
    let mut rng = Rng(args.seed);
    let mut candidates: Vec<usize> = Vec::new();
    // epoch boundaries (first block of an epoch, the block before) and blocks with a missing chunk
    for index in 2..blocks.len() {
        let header = blocks[index].header();
        let prev = blocks[index - 1].header();
        let new_epoch = header.epoch_id() != prev.epoch_id();
        let before_boundary = index + 1 < blocks.len() && blocks[index + 1].header().epoch_id() != header.epoch_id();
        let missing = header.chunk_mask().iter().any(|m| !*m);
        let skipped = header.height() != prev.height() + 1;
        if new_epoch || before_boundary || missing || skipped {
            candidates.push(index);
        }
    }
    let mut bases: BTreeSet<usize> = BTreeSet::new();
    bases.insert(1.min(blocks.len() - 1));
    bases.insert(2.min(blocks.len() - 1));
    let wanted = (args.bases / 2).max(1);
    let step = (candidates.len() / wanted).max(1);
    for index in candidates.iter().step_by(step).take(wanted) {
        bases.insert(*index);
    }
    while bases.len() < args.bases && blocks.len() > 3 {
        bases.insert(3 + (rng.next() as usize) % (blocks.len() - 3));
    }
    let mut variants_out = std::io::BufWriter::new(std::fs::File::create(args.out.join("variants.jsonl"))?);
    let mut count = 0usize;
    let mut kinds_seen = BTreeSet::new();
    for &index in &bases {
        let base = &blocks[index];
        let prev = &blocks[index - 1];
        for kind in kinds() {
            let Some((block, _)) = (kind.build)(&ctx, base, prev)
                .with_context(|| format!("variant {} at index {index}", kind.name))?
            else {
                continue;
            };
            let outcome = verdict(&mut ctx.chain, &block)
                .with_context(|| format!("variant {} at height {}", kind.name, base.header().height()))?;
            kinds_seen.insert(kind.name);
            let line = json!({
                "name": kind.name,
                "baseHeight": base.header().height(),
                "baseHash": hash_hex(base.header().hash()),
                "block": hex(&borsh_bytes(&block)?),
                "expected": outcome,
            });
            writeln!(variants_out, "{}", serde_json::to_string(&line)?)?;
            count += 1;
        }
    }
    variants_out.flush()?;

    let config = &near_config.genesis.config;
    let rate = config.gas_price_adjustment_rate;
    let meta = json!({
        "formatVersion": 1,
        "chainId": config.chain_id,
        "protocolVersion": config.protocol_version,
        "genesisHeight": genesis_height,
        "genesisHash": hash_hex(&hashes[0]),
        "headHeight": head.height,
        "blocks": blocks.len(),
        "epochLength": config.epoch_length,
        "shardLayoutStatic": epoch_manager
            .get_epoch_config_from_protocol_version(config.protocol_version)
            .static_shard_layout()
            .is_some(),
        "minGasPrice": config.min_gas_price.as_yoctonear().to_string(),
        "maxGasPrice": config.max_gas_price.as_yoctonear().to_string(),
        "gasPriceAdjustmentRateNumer": rate.numer(),
        "gasPriceAdjustmentRateDenom": rate.denom(),
        "gasLimit": config.gas_limit.as_gas(),
        "totalSupply": config.total_supply.as_yoctonear().to_string(),
        "transactionValidityPeriod": config.transaction_validity_period,
        "variants": count,
        "variantKinds": kinds_seen.iter().collect::<Vec<_>>(),
        "baseHeights": bases.iter().map(|i| blocks[*i].header().height()).collect::<Vec<_>>(),
        "epochs": epoch_ids.len(),
        "zeroHashBlockInfo": epoch_manager
            .get_block_info(&CryptoHash::default())
            .ok()
            .map(|info| hex(&borsh_bytes(&*info).expect("block info"))),
    });
    std::fs::write(args.out.join("meta.json"), serde_json::to_vec_pretty(&meta)?)?;
    println!("exported {} blocks, {} epochs, {} variants", blocks.len(), epoch_ids.len(), count);
    Ok(())
}
