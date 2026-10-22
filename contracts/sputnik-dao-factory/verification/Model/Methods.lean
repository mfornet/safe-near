import Model.Collections

namespace SputnikFactory

def getOwner (current : Account) : Tx Account := do
  let bytes := (← load ownerKey).getD current.toUTF8.data.toList
  let owner ← expect (String.fromUTF8? ⟨bytes.toArray⟩) .invalidOwner
  require (validAccount owner) .invalidOwner
  pure owner

def assertOwner (env : Env) : Tx Unit := do
  let owner ← getOwner env.current
  require (owner == env.predecessor) .owner

def loadDefault : Tx Hash := do
  let bytes ← expect (← load defaultKey) .defaultMissing
  expect (Borsh.hash bytes) .defaultMissing

def loadMap : Tx MapHeader := do
  let bytes ← expect (← load metadataKey) .metadataMissing
  expect (Borsh.exact Borsh.mapHeader bytes) .invalidMetadata

def loadFactory : Tx SetHeader := do
  let bytes ← expect (← load stateKey) .uninitialized
  expect (Borsh.exact Borsh.setHeader bytes) .invalidState

def callbackSuccess (env : Env) : Tx Bool :=
  match env.results with
  | [.successful _] => pure true
  | [.failed] => pure false
  | [.notReady] => .fail .notReady
  | _ => .fail .callbackArity

def deletionMetadata (env : Env) (hash : Hash) : Tx Unit := do
  assertOwner env
  let header ← loadMap
  let updated ← mapRemove header hash
  save metadataKey (Borsh.encodeMap updated)

def usage (cfg : Config) (raw : Raw) : Nat :=
  (raw.map fun entry => entry.1.length + entry.2.length + cfg.recordOverhead).sum

def saturatingMul (left right : Nat) : Nat := min (left * right) maxAmount

def storeCost (cfg : Config) (before after : Raw) : Nat :=
  saturatingMul (saturatingMul cfg.storageByteCost (usage cfg after - usage cfg before)) 11

def done (header : SetHeader) (result : Return := .unit) (receipts : List Receipt := []) : Tx Effects :=
  pure ⟨header, receipts, result⟩

/-- Bodies execute after wrapper checks and the first source assert_owner for
owner-only methods. Shared raw storage is used for every lookup and mutation. -/
def body (cfg : Config) (header : SetHeader) (env : Env) : Call → Tx Effects
  | .new => done header
  | .setOwner owner => do
    save ownerKey owner.toUTF8.data.toList
    done header
  | .setDefault hash => do
    require (← load hash.val).isSome .codeMissing
    save defaultKey hash.val
    done header
  | .deleteContract hash => do
    let defaultHash ← loadDefault
    require (defaultHash != hash) .defaultProtected
    erase hash.val
    deletionMetadata env hash
    done header
  | .create name args => do
    let account := name ++ "." ++ env.current
    require (validAccount account) .invalidAccount
    let hash ← loadDefault
    require (env.deposit ≥ 10 ^ 22) .insufficientDeposit
    require (← load hash.val).isSome .codeMissing
    done header (.promise 0)
      [⟨account, [.createAccount, .transfer env.deposit, .useGlobal hash,
        .functionCall "new" args 0 (40 * 10 ^ 12) 0], none⟩,
       ⟨env.current, [.onCreate account env.deposit env.predecessor (10 * 10 ^ 12)], some 0⟩]
  | .onCreate account amount predecessor => do
    let success ← callbackSuccess env
    if success then
      let updated ← setInsert header account
      done updated (.boolean true)
    else
      done header (.boolean false) [⟨predecessor, [.transfer amount], none⟩]
  | .update account hash => do
    let owner ← getOwner env.current
    require (env.predecessor == owner || env.predecessor == account) .updateAuthority
    require (← setContains header account) .daoMissing
    let code ← expect (← load hash.val) .codeMissing
    done header (.promise 0)
      [⟨account, [.functionCall "update" code 0 0 1], none⟩]
  | .daoList => do
    let accounts ← accountsAt header.elements (List.range header.elements.length)
    done header (.accounts accounts)
  | .daoCount => done header (.count header.elements.length)
  | .daos fromIndex limit => do
    require (fromIndex + limit < u64Bound) .overflow
    let upper := min (fromIndex + limit) header.elements.length
    let accounts ← accountsAt header.elements
      ((List.range (upper - fromIndex)).map (fromIndex + ·))
    done header (.accounts accounts)
  | .getOwner => do
    done header (.account (← getOwner env.current))
  | .defaultHash => do
    done header (.hash (← loadDefault))
  | .defaultVersion => do
    let metadata ← loadMap
    let hash ← loadDefault
    let value ← expect (← mapGet metadata hash) .metadataMissing
    done header (.version value.major value.minor)
  | .store => do
    let before ← snapshot
    let bytes ← expect env.input .noInput
    let hash := cfg.sha256 bytes
    require (!(← load hash.val).isSome) .alreadyExists
    save hash.val bytes
    let after ← snapshot
    require (storeCost cfg before after ≤ env.deposit) .insufficientDeposit
    done header (.hash hash) [⟨env.current, [.deployGlobal bytes], none⟩]
  | .getCode hash => do
    done header (.bytes (← expect (← load hash.val) .codeMissing))
  | .storeMetadata hash metadata setDefault => do
    require (← load hash.val).isSome .codeMissing
    let previous ← load metadataKey
    let existing ← match previous with
      | none => pure initialMap
      | some bytes => expect (Borsh.exact Borsh.mapHeader bytes) .invalidMetadata
    let updated ← mapInsert existing hash metadata
    save metadataKey (Borsh.encodeMap updated)
    if setDefault then save defaultKey hash.val
    done header
  | .deleteMetadata hash => do
    let metadata ← loadMap
    let updated ← mapRemove metadata hash
    save metadataKey (Borsh.encodeMap updated)
    done header
  | .getMetadata => do
    let metadata ← loadMap
    let count ← mapLength metadata
    let entries ← metadataAt metadata (List.range count)
    done header (.metadata entries)

/-- SDK 5.24.1 wrapper ordering: privacy, deposit, decoded arguments, state.
Only mutating-self methods serialize STATE after a successful body. -/
def entry (cfg : Config) (env : Env) (call : Call) : Tx Effects := do
  require (!call.private || env.predecessor == env.current) .privateCall
  require (!call.rejectDeposit || env.deposit == 0) .deposit
  if call.isNew then
    require (!(← load stateKey).isSome) .initialized
    save stateKey (Borsh.encodeSet initialSet)
    done initialSet
  else
    let header ← loadFactory
    if call.ownerOnly then assertOwner env
    let effects ← body cfg header env call
    if call.saveHeader then save stateKey (Borsh.encodeSet effects.header)
    pure effects

/-- Pure atomic model transaction. Failure has no committed state or receipts;
proving the runtime implements that rollback remains an explicit obligation. -/
def step (cfg : Config) (raw : Raw) (env : Env) (call : Call) : Except Panic Outcome :=
  match (entry cfg env call).run raw with
  | .error panic => .error panic
  | .ok (effects, updated) => .ok ⟨updated, effects.receipts, effects.result⟩

end SputnikFactory
