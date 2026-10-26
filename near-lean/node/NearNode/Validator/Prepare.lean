import NearNode.Validator.State
import NearNode.Validator.Pool

/-!
# Which transactions go into a chunk

`RpcHandlerActor::process_tx_internal` (`chain/client/src/rpc_handler.rs`), `Chain::check_transaction_validity_period`
(`chain/chain/src/store/utils.rs`), `validate_transaction` and `can_verify_and_charge_tx`
(`runtime/runtime/src/verifier.rs`) and `NightshadeRuntime::prepare_transactions_extra`
(`chain/chain/src/runtime/mod.rs`) over the node's state:

* `checkValidityPeriod`: the block the transaction names is known, no more than the validity period
  behind the block the chunk is built on, and an ancestor of it (or it);
* `validate`: the checks that need no state: the transaction version, its size, its actions, its signature;
* `Prepare.admit`: what `verify_and_charge_tx_ephemeral` decides on the signer's account and key as the
  earlier transactions of the same chunk left them (kept in an overlay), with the cost of the model's
  `convertTransaction` (the function the chunk's application runs);
* `prepareChunk`: the limits (`process_tx_limit` of the shard's congestion, the combined size limit of the
  witness configuration), the congestion check on the receiving shard, and `Pool.prepare`.

A gas-key transaction is refused (the model has no gas keys).
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Apply Near.Node.Borsh Near.Node.Trie

/-- `witness_config.combined_transactions_size_limit` (runtime configuration 69 and later). -/
def combinedTransactionsSizeLimit : Nat :=
  4_194_304

/-- Why a transaction is refused (`InvalidTxError`, as far as the runtime model tells). -/
inductive TxReject where
  | expired
  | invalidChain
  | invalidSignature
  | invalidVersion
  | sizeExceeded (size limit : Nat)
  | actions (why : String)
  | congested (why : String)
  | runtime (e : Near.RuntimeError)
  | unsupported (why : String)
  | state (why : String)
  deriving Inhabited

def TxReject.describe : TxReject → String
  | .expired => "Expired"
  | .invalidChain => "InvalidChain"
  | .invalidSignature => "InvalidSignature"
  | .invalidVersion => "InvalidTransactionVersion"
  | .sizeExceeded s l => s!"TransactionSizeExceeded {s} > {l}"
  | .actions w => s!"ActionsValidation {w}"
  | .congested w => w
  | .runtime e => e.message
  | .unsupported w => w
  | .state w => w

/-- The key handle of an access key in the trie, for the key types the model supports. -/
def handleOf : PublicKey → Option PublicKeyHandle
  | .ed25519 k => some (.ed25519 k)
  | .secp256k1 k => some (.secp256k1 k)
  | .mldsa65 _ => none

/-- The checks of `validate_transaction` that need no state, and the signature. -/
def validateStateless (cfg : Wasm.Near.RuntimeConfig) (t : SignedTransaction) :
    Except TxReject Unit := do
  if t.transaction.nonceIndex.isSome then
    throw (.unsupported "gas key transactions are not supported")
  if t.transaction.isStrict && !cfg.strictNonceEnabled then
    throw .invalidVersion
  let size := t.wireSize
  if size > cfg.wasm.limits.maxTransactionSize then
    throw (.sizeExceeded size cfg.wasm.limits.maxTransactionSize)
  let model ← (Apply.transaction t |>.run {}).map (·.1.1) |>.mapError TxReject.unsupported
  match Near.validateTransactionActions cfg model.actions with
  | .error e =>
    throw (.actions (repr e).pretty)
  | .ok () =>
    pure ()
  unless Chain.verifySignature t.signature t.hash.bytes t.transaction.publicKey do
    throw .invalidSignature

/-- `check_transaction_validity_period` relative to the block `prev` (the chunk will be in a block
built on it). -/
def checkValidityPeriod (st : CS) (prev : BlockRec) (period : Nat) (t : SignedTransaction) :
    Except TxReject Unit := do
  let base ←
    match st.block t.transaction.blockHash with
    | .ok b =>
      pure b
    | .error _ =>
      throw .expired
  if prev.view.height.toNat > base.view.height.toNat + period then
    throw .expired
  if base.view.height > prev.view.height then
    throw .invalidChain
  match ancestorAt st prev.hash base.view.height with
  | .ok b =>
    if b.hash == base.hash then
      pure ()
    else
      throw .invalidChain
  | .error _ =>
    throw .invalidChain

/-- The congestion control of a shard as the block before the chunk saw it
(`Block::block_congestion_info`). -/
def congestionControlOf (cfg : Near.Congestion.Config) (prev : BlockRec) (shard : ShardId)
    (layout : ShardLayout) : Option Near.Congestion.Control := do
  let i ← layout.getShardIndex shard
  let header ← prev.chunks[i]?
  let info ← Apply.congestionOf header
  let model ← (Near.Congestion.Info.ofBorsh (Codec.encode info).toList).toOption
  pure
      { config := cfg, info := model,
        missedChunks := (prev.view.height - header.heightIncluded).toNat }

/-- The context a chunk's transactions are checked in. -/
structure Context where
  st : CS
  pr : Progress
  params : Params
  /-- The block the chunk is built on, applied. -/
  prev : BlockRec
  layout : ShardLayout
  shard : ShardId
  /-- The state root of the shard after `prev`. -/
  root : CryptoHash
  validityPeriod : Nat

/-- The signer's account and access key as the model has them, from the trie. -/
def Context.load (c : Context) (a : AccountId) (pk : PublicKey) :
    Except String (Option (Near.Account × Near.AccessKey)) := do
  let some h := handleOf pk | return none
  let src := c.pr.tables.nodeSource (shardKey c.layout c.shard)
  let (acc, _) ← Trie.get src c.root (TrieKey.toVec (.account a))
  let (key, _) ← Trie.get src c.root (TrieKey.toVec (.accessKey a h))
  match acc, key with
  | some av, some kv =>
    let account ← (Codec.decodeAll (α := Account) av).mapError fun e => s!"account: {repr e}"
    let key ← (Codec.decodeAll (α := AccessKey) kv).mapError fun e => s!"access key: {repr e}"
    let base (amount locked : Balance) (usage : StorageUsage) : Near.Account :=
      { amount := amount.val, locked := locked.val, storageUsage := usage.toNat }
    let model : Near.Account :=
      match account with
      | .v1 amount locked _ usage => base amount locked usage
      | .v2 amount locked usage .none | .v2 amount locked usage (.local _) =>
        { base amount locked usage with versionTwo := true }
      | .v2 amount locked usage (.global h) =>
        { base amount locked usage with
          global := some (.codeHash h.bytes.toList), versionTwo := true }
      | .v2 amount locked usage (.globalByAccount id) =>
        { base amount locked usage with
          global := some (.accountId id.val.toUTF8.toList), versionTwo := true }
    pure (some (model, Apply.accessKey key))
  | _, _ =>
    pure none

/-- Whether the account is in the state. -/
def Context.accountExists (c : Context) (a : AccountId) : Except String Bool := do
  let src := c.pr.tables.nodeSource (shardKey c.layout c.shard)
  let (acc, _) ← Trie.get src c.root (TrieKey.toVec (.account a))
  pure acc.isSome

/-- The accounts and keys earlier transactions of the chunk changed. -/
abbrev Overlay :=
  Std.HashMap ByteArray (Near.Account × Near.AccessKey)

def overlayKey (a : AccountId) (pk : PublicKey) : ByteArray :=
  a.val.toUTF8 ++ ⟨#[0xff]⟩ ++ Codec.encode pk

def Context.signer (c : Context) (o : Overlay) (t : SignedTransaction) :
    Except TxReject (Near.Account × Near.AccessKey) := do
  let a := t.transaction.signerId
  let pk := t.transaction.publicKey
  match o[overlayKey a pk]? with
  | some x =>
    pure x
  | none =>
    match ← (c.load a pk).mapError TxReject.state with
    | some x =>
      pure x
    | none =>
      -- the signer account, then its key
      let found ← (c.accountExists a).mapError TxReject.state
      throw
          (.runtime
            (if found then .accessKeyNotFound a.val (Apply.keyBytes pk) else .invalidSigner a.val))

/-- `ApplyState` of the chunk being prepared: the next block's height and gas price. -/
def Context.applyState (c : Context) : Near.ApplyState :=
  { blockHeight := c.prev.view.height.toNat + 1, gasPrice := c.prev.view.nextGasPrice.val }

/-- The verdict on one transaction (`prepare_transactions_extra` for one transaction taken out of the pool). -/
def Context.admitR (c : Context) (o : Overlay) (t : SignedTransaction) :
    Except TxReject (Overlay × Nat) := do
  let cfg := c.params.cfg
  -- the receiving shard accepts transactions
  if let some toShard := c.layout.accountIdToShardId t.transaction.receiverId then
    if let some control := congestionControlOf c.params.congestion c.prev toShard c.layout then
      if (control.shardAcceptsTransactions).isSome then
        throw (.congested "the receiving shard is congested")
  checkValidityPeriod c.st c.prev c.validityPeriod t
  let (account, key) ← c.signer o t
  let model ← (Apply.transaction t |>.run {}).map (·.1.1) |>.mapError TxReject.unsupported
  let signer := model.signerId
  let kb := (Apply.keyBytes t.transaction.publicKey)
  let mini : Near.ChainState :=
    { accounts := [(signer, account)], accessKeys := [((signer, kb), key)] }
  match Near.convertTransaction cfg c.applyState mini model with
  | .error e =>
    throw (.runtime e)
  | .ok (st', _, cost) =>
    let some account' := st'.account? signer | throw (.state "signer lost")
    let some key' := st'.accessKey? signer kb | throw (.state "key lost")
    pure
        (o.insert (overlayKey t.transaction.signerId t.transaction.publicKey) (account', key'),
          cost.gasBurnt)

def Context.admit (c : Context) (o : Overlay) (t : SignedTransaction) :
    Except String (Overlay × Nat) :=
  (c.admitR o t).mapError TxReject.describe

/-- The nonce the key of `t` has now, for the nonce gap check of strict-nonce transactions. -/
def Context.peekNonce (c : Context) (o : Overlay) (t : SignedTransaction) : Option Nat :=
  match c.signer o t with
  | .ok (_, key) => some key.nonce
  | .error _ => none

/-- `Chain::check_transaction_validity_period` as the TTL test of a transaction waiting for a nonce. -/
def Context.ttl (c : Context) (t : SignedTransaction) : Bool :=
  (checkValidityPeriod c.st c.prev c.validityPeriod t).toOption.isSome

/-- `prepare_transactions` of the shard's pool on top of `prev`. -/
def prepareChunk (c : Context) (pool : Pool) : Pool.Prepared :=
  let own := congestionControlOf c.params.congestion c.prev c.shard c.layout
  let gasLimit :=
    match own with
    | some control => control.processTxLimit
    | none =>
      ({ config := c.params.congestion, info := {}, missedChunks := 0 } :
          Near.Congestion.Control).processTxLimit
  pool.prepare (({} : Overlay)) gasLimit combinedTransactionsSizeLimit SignedTransaction.wireSize
    c.peekNonce c.ttl c.admit

/-- A transaction offered to the pool (`process_tx_internal` for a shard the node tracks): the
stateless checks, the validity period against the head, and the signer's state at the head. The
validity period comes first (`process_tx_internal` checks it before anything else). -/
def Context.checkForPool (c : Context) (t : SignedTransaction) : Except TxReject Unit := do
  checkValidityPeriod c.st c.prev c.validityPeriod t
  validateStateless c.params.cfg t
  let _ ← c.admitR ({} : Overlay) t
  pure ()

/-- What `process_tx` answers (`ProcessTxResponse`). -/
inductive TxVerdict where
  | valid
  | invalid (reason : TxReject)
  | routed
  | noResponse
  deriving Inhabited

end Near.Node.Validator
