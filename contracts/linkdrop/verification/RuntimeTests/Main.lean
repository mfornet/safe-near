import Spec.Contract
import NearRuntime.Boundary

/-!
# Adapter regressions: the binary against the model, on the boundary

Every execution below runs `contract.wasm` through `Near.Boundary.execOn`
(the near-lean `RuntimeInterface`) and compares it with `contractStep`, the
step of the `linkdrop` contract model, exactly as `Refines` does:
`matchesCheck` is `Matches` as a boolean, and with the model's gas bound
attached the execution must use at most that much gas. Inputs that are no
call must fail with no effects.
-/

open Linkdrop.Boundary NearInterface Wasm Wasm.Near

def check (name : String) (condition : Bool) (detail : String := "") : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name} {detail}")
  IO.println s!"ok: {name}"

def bytes (s : String) : List UInt8 := s.toUTF8.toList

def acct (s : String) : NearInterface.AccountId :=
  if h : validAccountIdBytes s.toUTF8.toList = true then ⟨s, h⟩ else ⟨"near", by decide +kernel⟩

def keyData (s : String) : List UInt8 := ((publicKeyOfString s).map (·.val)).getD []

/-- `Matches` as a boolean. -/
def matchesCheck (ctx : Context) (raw : RawStorage) (r : Observation) : StepResult → Bool
  | .ok o =>
    let receipts := encodeReceipts (ctx.prepaidGas - r.usedGas) o.promises
    (match r.outcome with | .ok d => d == encodeRet o.ret | .error _ => false) &&
    decide (r.storage = encode o.state) &&
    r.balance == ctx.balance + ctx.attached - receiptDeposits receipts &&
    r.storageUsage == ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (encode o.state) &&
    r.logs == o.logs && r.receipts == receipts
  | .error f =>
    (match r.outcome with
      | .error e => decide (e = ContractModel.ModelFailure.toFailure linkdrop f.failure)
      | .ok _ => false) &&
    decide (r.storage = raw) && r.balance == ctx.balance && r.storageUsage == ctx.storageUsage &&
    r.logs == f.logs && r.receipts.isEmpty

def rolledBack (ctx : Context) (raw : RawStorage) (r : Observation) : Bool :=
  (match r.outcome with | .error _ => true | .ok _ => false) && decide (r.storage = raw) &&
    r.balance == ctx.balance && r.storageUsage == ctx.storageUsage && r.receipts.isEmpty

def outOfGas (r : Observation) : Bool :=
  match r.outcome with
  | .error .outOfGas => true
  | _ => false

def describe (r : Observation) : String :=
  let outcome := match r.outcome with
    | .ok _ => "ok"
    | .error e => s!"{repr e}"
  s!"outcome={outcome} used={r.usedGas} receipts={r.receipts.length}"

def contract : NearInterface.AccountId := acct "near"

structure Call' where
  predecessor : String := "alice.near"
  method : String
  args : String := "{}"
  deposit : Nat := 0
  gas : Nat := 300 * 10 ^ 12
  results : List Wasm.PromiseResult := []
  balance : Nat := 100 * 10 ^ 24
  signerPk : List UInt8 := 0 :: List.replicate 32 9

structure Snapshot where
  storage : List (List UInt8 × List UInt8)
  state : Option State
  usage : Nat

def contextOf (protocol : RuntimeConfig) (snap : Snapshot) (c : Call') : IO Context := do
  let entries := snap.storage.map fun (k, v) => (_root_.Near.TrieOverlay.contractKey contract.bytes k, v)
  let trie ← match _root_.Near.TrieOverlay.start entries with
    | .ok trie => pure trie
    | .error e => throw (IO.userError s!"trie: {e}")
  pure {
    method := c.method, args := bytes c.args
    current := contract, predecessor := acct c.predecessor, signer := acct c.predecessor
    signerPk := c.signerPk, attached := c.deposit, prepaidGas := c.gas, promiseResults := c.results
    outputDataReceivers := [], balance := c.balance, locked := 0, storageUsage := snap.usage
    blockHeight := 1, timestamp := 0, epochHeight := 1, randomSeed := List.replicate 32 0
    trie, protocol }

/-- Run one call on the binary and on the model and compare. Returns the
snapshot after the call, by the binary. -/
def compare (name : String) (protocol : RuntimeConfig) (code : Near.Boundary.Code)
    (snap : Snapshot) (c : Call') : IO (Snapshot × Observation) := do
  let ctx ← contextOf protocol snap c
  let raw := snap.storage.toFinset
  let r := Near.Boundary.execOn code snap.storage ctx
  check s!"{name}: no execution issue"
    (match r.outcome with | .error (.executionIssue _) => false | _ => true) (describe r)
  match Call.decode c.method ctx.args with
  | none =>
    check s!"{name}: input that is no call fails with no effects" (rolledBack ctx raw r) (describe r)
    pure (snap, r)
  | some call =>
    let res := contractStep ctx snap.state call
    let bound := gasBound ctx snap.state call
    if bound ≤ ctx.gasLimit then
      check s!"{name}: matches the model" (matchesCheck ctx raw r res) (describe r)
      check s!"{name}: used gas {r.usedGas} within the bound {bound}" (r.usedGas ≤ bound)
    else
      check s!"{name}: matches the model or fails for gas with no effects"
        (matchesCheck ctx raw r res || (outOfGas r && rolledBack ctx raw r && r.logs.isPrefixOf res.logs))
        (describe r)
    match res, r.outcome with
    | .ok o, .ok _ =>
      let vm := run protocol code.code.module code.code.size c.method (Near.Boundary.toVMContext ctx)
        snap.storage
      pure ({ storage := vm.storage, state := some o.state, usage := r.storageUsage }, r)
    | _, _ => pure (snap, r)

def pk1 := "ed25519:qSq3LoufLvTCTNGC3LJePMDGrok8dHMQ5A1YD9psbiz"
def pk2 := "ed25519:3tysLvy7KGoE8pznUgXvSHa4vYyGvrDZFcT8jgb8PEQ6"
def pk3 := "ed25519:6E8sCci9badyRkXb3JoRpBj5p8C6Tw41ELDZoiihKEtp"
def secp := "secp256k1:qMoRgcoXai4mBPsdbHi1wfyxF9TdbPCF4qSDQTRP3TfescSRoUdSx6nmeQoN3aiwGzwMyGXAb1gUjBTv5AY8DXj"

def keyArg (field key : String) : String := "{\"" ++ field ++ "\":\"" ++ key ++ "\"}"

def advanced (options : String) : String := "{\"new_account_id\":\"bob.near\",\"options\":" ++ options ++ "}"

def main : IO Unit := do
  -- Decoders, against the crates' documented behaviour.
  check "base58: leading ones are zero bytes" (base58Decode "111" == some [0, 0, 0])
  check "base58: a known key" ((base58Decode "6E8sCci9badyRkXb3JoRpBj5p8C6Tw41ELDZoiihKEtp").map List.length == some 32)
  check "base58: 0, O, I and l are not digits" ((base58Decode "0").isNone && (base58Decode "O").isNone &&
    (base58Decode "I").isNone && (base58Decode "l").isNone)
  check "base64: canonical padding" (base64Decode "AQID" == some [1, 2, 3] && base64Decode "AQ==" == some [1] &&
    base64Decode "AQI=" == some [1, 2] && base64Decode "" == some [])
  check "base64: missing or extra padding, trailing bits" ((base64Decode "AQI").isNone &&
    (base64Decode "AQ=").isNone && (base64Decode "AR==").isNone && (base64Decode "A===").isNone &&
    (base64Decode "AQ==AQ==").isNone)
  check "public keys: curve prefix is ASCII case-insensitive, ed25519 by default"
    ((publicKeyOfString ("ED25519:" ++ (pk1.drop 8).toString)).map (·.val) == (publicKeyOfString pk1).map (·.val) &&
     (publicKeyOfString (pk1.drop 8).toString).map (·.val) == (publicKeyOfString pk1).map (·.val) &&
     ((publicKeyOfString secp).map (·.val.length)) == some 65 &&
     (publicKeyOfString "ed25519:111").isNone && (publicKeyOfString "rsa:111").isNone)

  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let contractBytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode contractBytes with
    | .ok m => pure m
    | .error error => throw (IO.userError error.message)
  let code : Near.Boundary.Code :=
    { code := { module, size := contractBytes.size, hash := "" },
      codeOf := fun bytes => { module := default, size := bytes.length, hash := "" } }
  let cmp := fun name snap c => compare name protocol code snap c
  let empty : Snapshot := { storage := [], state := none, usage := 100000 }

  -- Initialisation and the SDK guards.
  let _ ← cmp "send before new" empty { method := "send", args := keyArg "public_key" pk1, deposit := 1 }
  let _ ← cmp "get_key_balance before new" empty { method := "get_key_balance", args := keyArg "key" pk1 }
  let _ ← cmp "new with a deposit" empty { method := "new", deposit := 1 }
  let _ ← cmp "new ignores its input" empty { method := "new", args := "garbage", deposit := 1 }
  let (s, _) ← cmp "new" empty { method := "new" }
  let _ ← cmp "new twice" s { method := "new" }
  let _ ← cmp "new twice with a deposit" s { method := "new", deposit := 1 }
  let _ ← cmp "unknown method" s { method := "nope" }
  let _ ← cmp "bad JSON" s { method := "send", args := "{", deposit := 1 }

  -- The `cargo near` metadata exports: any input, deposit and state.
  for (name, snap) in [("before new", empty), ("after new", s)] do
    let _ ← cmp s!"contract_source_metadata {name}" snap
      { method := "contract_source_metadata", args := "garbage", deposit := 5 }
    let _ ← cmp s!"__contract_abi {name}" snap { method := "__contract_abi", deposit := 1 }

  -- send
  let _ ← cmp "send without a deposit" s { method := "send", args := keyArg "public_key" pk1 }
  let (s, _) ← cmp "send" s { method := "send", args := keyArg "public_key" pk1, deposit := 10 ^ 24 }
  let (s, _) ← cmp "send again accumulates" s { method := "send", args := keyArg "public_key" pk1, deposit := 7 }
  let (s, _) ← cmp "send a second key" s { method := "send", args := keyArg "public_key" pk2, deposit := 5 }
  let (s, _) ← cmp "send a key without prefix" s
    { method := "send", args := keyArg "public_key" (pk3.drop 8).toString, deposit := 3 }
  let (s, _) ← cmp "send a secp256k1 key" s { method := "send", args := keyArg "public_key" secp, deposit := 2 }
  let _ ← cmp "send an invalid key" s { method := "send", args := keyArg "public_key" "ed25519:111", deposit := 1 }
  let _ ← cmp "send, array form" s { method := "send", args := "[\"" ++ pk2 ++ "\"]", deposit := 1 }
  let _ ← cmp "send, duplicate field" s
    { method := "send", args := "{\"public_key\":\"" ++ pk2 ++ "\",\"public_key\":\"" ++ pk2 ++ "\"}", deposit := 1 }

  -- views
  let _ ← cmp "get_key_balance" s { method := "get_key_balance", args := keyArg "key" pk1 }
  let _ ← cmp "get_key_balance with a deposit" s { method := "get_key_balance", args := keyArg "key" pk1, deposit := 1 }
  let _ ← cmp "get_key_balance missing" s
    { method := "get_key_balance", args := keyArg "key" "ed25519:11111111111111111111111111111111" }
  let _ ← cmp "get_key_information" s { method := "get_key_information", args := keyArg "key" secp }
  let _ ← cmp "get_key_information missing" s
    { method := "get_key_information", args := keyArg "key" "ed25519:11111111111111111111111111111111" }

  -- claim and create_account_and_claim
  let claimArgs := "{\"account_id\":\"bob.near\"}"
  let _ ← cmp "claim from another account" s { method := "claim", args := claimArgs, signerPk := keyData pk1 }
  let _ ← cmp "claim with a deposit" s
    { predecessor := "near", method := "claim", args := claimArgs, deposit := 1, signerPk := keyData pk1 }
  let _ ← cmp "claim with an unknown key" s { predecessor := "near", method := "claim", args := claimArgs }
  let _ ← cmp "claim with an unparsable signer key" s
    { predecessor := "near", method := "claim", args := claimArgs, signerPk := [7, 7] }
  let _ ← cmp "claim more than the balance" s
    { predecessor := "near", method := "claim", args := claimArgs, signerPk := keyData pk1, balance := 1000 }
  let (s, _) ← cmp "claim the first entry (swap remove)" s
    { predecessor := "near", method := "claim", args := claimArgs, signerPk := keyData pk1 }
  let createClaim := "{\"new_account_id\":\"carol.near\",\"new_public_key\":\"" ++ pk1 ++ "\"}"
  let _ ← cmp "create_account_and_claim with an unknown key" s
    { predecessor := "near", method := "create_account_and_claim", args := createClaim, signerPk := keyData pk1 }
  let (s, _) ← cmp "create_account_and_claim the last entry" s
    { predecessor := "near", method := "create_account_and_claim", args := createClaim, signerPk := keyData pk2 }
  let _ ← cmp "create_account_and_claim from another account" s
    { method := "create_account_and_claim", args := createClaim, signerPk := keyData pk3 }

  -- callbacks
  let created := "{\"predecessor_account_id\":\"alice.near\",\"amount\":\"5\"}"
  for (name, results) in [("no result", []), ("success", [Wasm.PromiseResult.successful []]),
      ("failure", [.failed]), ("not ready", [.notReady]), ("two results", [.failed, .failed])] do
    let _ ← cmp s!"on_account_created, {name}" s
      { predecessor := "near", method := "on_account_created", args := created, results }
    let _ ← cmp s!"on_account_created_and_claimed, {name}" s
      { predecessor := "near", method := "on_account_created_and_claimed", args := "{\"amount\":\"5\"}",
        results, signerPk := keyData pk1 }
  let _ ← cmp "on_account_created from another account" s
    { method := "on_account_created", args := created, results := [.failed] }
  let _ ← cmp "on_account_created refunding more than the balance" s
    { predecessor := "near", method := "on_account_created", results := [.failed], balance := 1000,
      args := "{\"predecessor_account_id\":\"alice.near\",\"amount\":\"1000000\"}" }
  let _ ← cmp "on_account_created with a numeric amount" s
    { predecessor := "near", method := "on_account_created", results := [.failed],
      args := "{\"predecessor_account_id\":\"alice.near\",\"amount\":5}" }
  let _ ← cmp "on_account_created_and_claimed failure, unparsable signer" s
    { predecessor := "near", method := "on_account_created_and_claimed", args := "{\"amount\":\"5\"}",
      results := [.failed], signerPk := [] }
  let (s, _) ← cmp "on_account_created_and_claimed failure puts the amount back" s
    { predecessor := "near", method := "on_account_created_and_claimed", args := "{\"amount\":\"9\"}",
      results := [.failed], signerPk := keyData pk1 }

  -- account creation
  let _ ← cmp "create_account" s
    { method := "create_account", deposit := 10 ^ 22,
      args := "{\"new_account_id\":\"bob.near\",\"new_public_key\":\"" ++ pk2 ++ "\"}" }
  let _ ← cmp "create_account with an invalid account id" s
    { method := "create_account", deposit := 1,
      args := "{\"new_account_id\":\"XYZ\",\"new_public_key\":\"" ++ pk2 ++ "\"}" }
  let _ ← cmp "create_account with little gas" s
    { method := "create_account", deposit := 1, gas := 14 * 10 ^ 12,
      args := "{\"new_account_id\":\"bob.near\",\"new_public_key\":\"" ++ pk2 ++ "\"}" }
  let limited := "{\"public_key\":\"" ++ pk2 ++ "\",\"allowance\":\"0\",\"receiver_id\":\"c.near\",\"method_names\":\"a,b\"}"
  let limited9 := "{\"public_key\":\"" ++ pk1 ++ "\",\"allowance\":\"9\",\"receiver_id\":\"c.near\",\"method_names\":\"\"}"
  for (name, options) in [
      ("no options", "{}"), ("null options", "{\"full_access_keys\":null,\"contract_bytes\":null}"),
      ("empty key list", "{\"full_access_keys\":[]}"),
      ("unknown option", "{\"full_access_keys\":[],\"zzz\":1}"),
      ("keys", "{\"full_access_keys\":[\"" ++ pk1 ++ "\",\"" ++ secp ++ "\"],\"limited_access_keys\":[" ++ limited ++ "," ++ limited9 ++ "]}"),
      ("contract bytes", "{\"contract_bytes\":[0,1,255]}"),
      ("contract bytes out of range", "{\"contract_bytes\":[256]}"),
      ("contract bytes -0", "{\"contract_bytes\":[-0]}"),
      ("contract bytes 1.0", "{\"contract_bytes\":[1.0]}"),
      ("base64", "{\"contract_bytes_base64\":\"AQID\"}"),
      ("base64 without padding", "{\"contract_bytes_base64\":\"AQI\"}"),
      ("global hash", "{\"use_global_contract_hash\":\"6E8sCci9badyRkXb3JoRpBj5p8C6Tw41ELDZoiihKEtp\"}"),
      ("global hash too short", "{\"use_global_contract_hash\":\"111\"}"),
      ("global account", "{\"use_global_contract_account_id\":\"x.near\"}"),
      ("two deployments", "{\"contract_bytes\":[1],\"use_global_contract_account_id\":\"x.near\"}"),
      ("array form", "[[\"" ++ pk1 ++ "\"],null,null,null,null,null]")] do
    let _ ← cmp s!"create_account_advanced, {name}" s
      { method := "create_account_advanced", deposit := 3, args := advanced options }

  -- Gas on long arguments.
  let manyBytes := ",".intercalate ((List.range 20000).map fun i => toString (i % 256))
  let _ ← cmp "create_account_advanced, 20 KB of contract bytes" s
    { method := "create_account_advanced", args := advanced ("{\"contract_bytes\":[" ++ manyBytes ++ "]}") }
  let b64 := String.join (List.replicate 10000 "AAEC")
  let _ ← cmp "create_account_advanced, 30 KB of base64" s
    { method := "create_account_advanced", args := advanced ("{\"contract_bytes_base64\":\"" ++ b64 ++ "\"}") }
  let keys := ",".intercalate (List.replicate 50 ("\"" ++ pk1 ++ "\""))
  let _ ← cmp "create_account_advanced, 50 keys" s
    { method := "create_account_advanced", args := advanced ("{\"full_access_keys\":[" ++ keys ++ "]}") }
  let methods := String.join (List.replicate 1000 "m,")
  let _ ← cmp "create_account_advanced, long method names" s
    { method := "create_account_advanced",
      args := advanced ("{\"limited_access_keys\":[{\"public_key\":\"" ++ pk1 ++
        "\",\"allowance\":\"1\",\"receiver_id\":\"c.near\",\"method_names\":\"" ++ methods ++ "m\"}]}") }

  -- Gas on an adversarial trie: stored keys that share ever longer prefixes
  -- with the keys a claim touches, so every trie path is as deep as it gets.
  let base := keyData pk1
  let near := (List.range base.length).flatMap fun i =>
    [1, 128].filterMap fun d =>
      PublicKey.ofData? (base.set i (if i == 0 then 0 else UInt8.ofNat ((base[i]!).toNat + d)))
  let some k1 := PublicKey.ofData? base | throw (IO.userError "key")
  let entries := (k1, 10 ^ 24) :: (near.filter (·.val != base)).map fun k => (k, 1)
  let deep : Map := ⟨entries⟩
  let deepSnap : Snapshot := { storage := records deep, state := some (some deep), usage := 100000 }
  let _ ← cmp "claim on an adversarial trie" deepSnap
    { predecessor := "near", method := "claim", args := claimArgs, signerPk := base }
  let _ ← cmp "send on an adversarial trie" deepSnap
    { method := "send", args := keyArg "public_key" pk1, deposit := 1 }
  let _ ← cmp "get_key_balance on an adversarial trie" deepSnap
    { method := "get_key_balance", args := keyArg "key" pk1 }
  pure ()
