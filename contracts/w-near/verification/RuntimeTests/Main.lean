import Spec.Contract
import Spec.Exports
import Binary.Bytes
import NearRuntime.Boundary
import Wasm.Binary

/-!
# Adapter regressions: the binary against the model, on the boundary

Every execution below runs `contract.wasm` through `Near.Boundary.execOn`
(the near-lean `RuntimeInterface`) and compares it with `contractStep`, the
step of the `wnear` contract model, exactly as `Refines` does: `matchesCheck`
is `Matches` as a boolean, and with the model's gas bound attached the
execution must use at most that much gas. Inputs that are no call must fail
with no effects.
-/

open WNear NearInterface Wasm Wasm.Near

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")
  IO.println s!"ok: {name}"

def bytes (s : String) : List UInt8 := s.toUTF8.toList

def failureOf (cfg : WNear.Config) (f : NearInterface.ModelFailure Panic) : Failure :=
  ContractModel.ModelFailure.toFailure (wnear cfg) f

/-- `Matches` as a boolean. -/
def matchesCheck (cfg : WNear.Config) (ctx : Context) (raw : NearInterface.RawStorage) (r : Observation) :
    WNear.Result → Bool
  | .ok o =>
    let receipts := encodeReceipts o.promises
    (match r.outcome with | .ok d => d == encodeRet o.ret | .error _ => false) &&
    decide (r.storage = encode o.state) &&
    r.balance == ctx.balance + ctx.attached - receiptDeposits receipts &&
    r.storageUsage == ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (encode o.state) &&
    r.logs == o.logs && r.receipts == receipts
  | .error f =>
    (match r.outcome with | .error e => decide (e = failureOf cfg f.failure) | .ok _ => false) &&
    decide (r.storage = raw) && r.balance == ctx.balance && r.storageUsage == ctx.storageUsage &&
    r.logs == f.logs && r.receipts.isEmpty

def rolledBack (ctx : Context) (raw : NearInterface.RawStorage) (r : Observation) : Bool :=
  (match r.outcome with | .error _ => true | .ok _ => false) && decide (r.storage = raw) &&
    r.balance == ctx.balance && r.storageUsage == ctx.storageUsage && r.receipts.isEmpty

def outOfGas (r : Observation) : Bool :=
  match r.outcome with
  | .error .outOfGas => true
  | _ => false

/-- Register `a` with balance `b`. -/
def addAccount (st : State) (a : WNear.AccountId) (b : Nat) : State :=
  let st := st.register a
  { st with balance := Function.update st.balance a b, totalSupply := st.totalSupply + b }

/-- Valid account ids that differ from `a` in one character, in either nibble. -/
def neighbours (a : WNear.AccountId) : List WNear.AccountId :=
  (List.range a.val.length).flatMap fun i =>
    ['0', 'q', 'z'].filterMap fun c =>
      let id := String.ofList (a.val.toList.set i c)
      if h : isValidAccountId id = true then
        if id == a.val then none else some (⟨id, h⟩ : WNear.AccountId)
      else none

def wrapId : WNear.AccountId := ⟨"wrap.near", by decide⟩
def alice : WNear.AccountId := ⟨"alice.near", by decide⟩
def bob : WNear.AccountId := ⟨"bob.near", by decide⟩

/-- Everything a test call varies; the rest of the context is fixed. -/
structure Call' where
  predecessor : WNear.AccountId := alice
  method : String
  args : String := "{}"
  deposit : Nat := 0
  gas : Nat := 300 * 10 ^ 12
  results : List Wasm.PromiseResult := []
  balance : Nat := 100 * 10 ^ 24

structure Snapshot where
  storage : List (List UInt8 × List UInt8)
  state : Option State
  usage : Nat

def contextOf (protocol : RuntimeConfig) (snap : Snapshot) (c : Call') : IO Context := do
  let entries := snap.storage.map fun (k, v) =>
    (_root_.Near.TrieOverlay.contractKey wrapId.bytes k, v)
  let trie ← match _root_.Near.TrieOverlay.start entries with
    | .ok trie => pure trie
    | .error e => throw (IO.userError s!"trie: {e}")
  pure {
    method := c.method, args := bytes c.args
    current := wrapId.toNear, predecessor := c.predecessor.toNear, signer := c.predecessor.toNear
    signerPk := [], attached := c.deposit, prepaidGas := c.gas, promiseResults := c.results
    outputDataReceivers := [], balance := c.balance, locked := 0, storageUsage := snap.usage
    blockHeight := 1, timestamp := 0, epochHeight := 1, randomSeed := List.replicate 32 0
    trie, protocol }

/-- Run one call on the binary and on the model and compare. Returns the
snapshot after the call, by the binary. -/
def compare (name : String) (cfg : WNear.Config) (protocol : RuntimeConfig) (code : Near.Boundary.Code)
    (snap : Snapshot) (c : Call') : IO (Snapshot × Observation) := do
  let ctx ← contextOf protocol snap c
  let raw := snap.storage.toFinset
  let r := Near.Boundary.execOn code snap.storage ctx
  check s!"{name}: no execution issue"
    (match r.outcome with | .error (.executionIssue _) => false | _ => true)
  match Call.decode c.method ctx.args with
  | none =>
    check s!"{name}: input that is no call fails with no effects" (rolledBack ctx raw r)
    pure (snap, r)
  | some call =>
    let res := contractStep ctx snap.state call
    let bound := gasBound ctx call
    if bound ≤ ctx.gasLimit then
      check s!"{name}: matches the model" (matchesCheck cfg ctx raw r res)
      check s!"{name}: used gas {r.usedGas} within the bound {bound}" (r.usedGas ≤ bound)
    else
      check s!"{name}: matches the model or fails for gas with no effects"
        (matchesCheck cfg ctx raw r res ||
          (outOfGas r && rolledBack ctx raw r && r.logs.isPrefixOf res.logs))
    match res, r.outcome with
    | .ok o, .ok _ =>
      let vm := run protocol code.code.module code.code.size c.method (Near.Boundary.toVMContext ctx)
        snap.storage
      pure ({ storage := vm.storage, state := some o.state, usage := r.storageUsage }, r)
    | _, _ => pure (snap, r)

def main : IO Unit := do
  -- JSON layer: serde_json's acceptance, as observed on contract.wasm.
  let parses (s : String) := (Json.parse (bytes s)).isSome
  for (text, expected) in [("{\"a\":1}", true), (" [1, 2.5e-3, -0, true, null, \"x\"] ", true),
      ("{\"a\":1,}", false), ("01", false), ("\"\\ud800\"", false), ("\"\\udc00\"", false),
      ("\"\\ud83d\\ude00\"", true), ("{\"a\":1} x", false), ("", false), ("1e999999", true),
      ("\"a\u0001\"", false), ("{\"x\":1,\"x\":2}", true), ("-", false), ("1.", false)] do
    check s!"JSON acceptance: {text}" (parses text == expected)
  for (body, expected) in [
      ("\"0\"", some 0), ("  \"42\" \n", some 42), ("\"+001\"", some 1), ("\"0007\"", some 7),
      ("\"340282366920938463463374607431768211455\"", some (2^128 - 1)),
      ("\"340282366920938463463374607431768211456\"", none),
      ("42", none), ("null", none), ("\"\"", none), ("\"+\"", none), ("\"-0\"", none),
      ("\" 1\"", none), ("\"1 \"", none), ("\"1.0\"", none), ("\"1\" trailing", none),
      ("\"１２\"", none), ("\"\\u0037\"", some 7), ("\"\\u002B\\u0030\\u0037\"", some 7)] do
    check s!"callback U128: {body}" (parseU128Result (bytes body) == expected)
  check "invalid UTF-8 is a malformed successful callback"
    (callbackResultOf [.successful [255]] == some (.successful none))
  check "serde string escapes" (Json.quote "a\"b\\c\n\x01é" == "\"a\\\"b\\\\c\\n\\u0001é\"")
  check "argument decoding: array form, escaped keys, null options"
    (Call.decode "ft_transfer" (bytes "[\"bob.near\",\"1\",null]") == some (.ftTransfer bob 1 none) &&
     Call.decode "ft_balance_of" (bytes "{\"\\u0061ccount_id\":\"bob.near\"}") == some (.ftBalanceOf bob) &&
     Call.decode "ft_balance_of" (bytes "{\"account_id\":\"bob.near\",\"account_id\":\"bob.near\"}") == none &&
     Call.decode "ft_transfer" (bytes "[\"bob.near\",\"1\"]") == none &&
     Call.decode "ft_total_supply" (bytes "garbage") == some .ftTotalSupply)

  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let cfg := WNear.Config.ofRuntime protocol
  -- Feasibility evidence for the concrete pinned configuration. These executable
  -- checks do not replace the five kernel-checked protocol obligations.
  let costs := protocol.wasm.extCosts.cost
  for (name, actual, bound) in [
      ("regular_op", protocol.wasm.regularOpCost, 822756),
      ("linear_base", protocol.wasm.linearOpBaseCost, 26328192),
      ("linear_unit", protocol.wasm.linearOpUnitCost, 822756),
      ("base", costs "base", 264768111),
      ("loading_base", costs "contract_loading_base", 35445963),
      ("loading_bytes", costs "contract_loading_bytes", 1089295),
      ("read_memory_base", costs "read_memory_base", 2609863200),
      ("read_memory_byte", costs "read_memory_byte", 3801333),
      ("write_memory_base", costs "write_memory_base", 2803794861),
      ("write_memory_byte", costs "write_memory_byte", 2723772),
      ("read_register_base", costs "read_register_base", 2517165186),
      ("read_register_byte", costs "read_register_byte", 98562),
      ("write_register_base", costs "write_register_base", 2865522486),
      ("write_register_byte", costs "write_register_byte", 3801564),
      ("storage_read_base", costs "storage_read_base", 56356845749),
      ("storage_read_key_byte", costs "storage_read_key_byte", 30952533),
      ("storage_read_value_byte", costs "storage_read_value_byte", 5611004),
      ("utf8_decoding_base", costs "utf8_decoding_base", 3111779061),
      ("utf8_decoding_byte", costs "utf8_decoding_byte", 291580479),
      ("storage_has_key_base", costs "storage_has_key_base", 54039896625),
      ("storage_has_key_byte", costs "storage_has_key_byte", 30790845),
      ("storage_write_base", costs "storage_write_base", 64196736000),
      ("storage_write_key_byte", costs "storage_write_key_byte", 70482867),
      ("storage_write_value_byte", costs "storage_write_value_byte", 31018539),
      ("storage_remove_base", costs "storage_remove_base", 53473030500),
      ("storage_remove_key_byte", costs "storage_remove_key_byte", 38220384),
      ("storage_remove_ret_value_byte", costs "storage_remove_ret_value_byte", 11531556),
      ("storage_write_evicted_byte", costs "storage_write_evicted_byte", 32117307),
      ("log_base", costs "log_base", 3543313050),
      ("log_byte", costs "log_byte", 13198791)] do
    check s!"protocol cost {name}: {actual} ≤ {bound}" (actual ≤ bound)
  let limits := protocol.wasm.limits
  for (name, required, actual) in [
      ("storage key", 2048, limits.maxLengthStorageKey),
      ("register", 104857600, limits.maxRegisterSize),
      ("returned data", 4194304, limits.maxLengthReturnedData),
      ("total log", 16384, limits.maxTotalLogLength),
      ("storage value", 29, limits.maxLengthStorageValue),
      ("log count", 1, limits.maxNumberLogs),
      ("usage room", 85 + protocol.fees.numExtraBytesRecord, limits.maxGasBurnt)] do
    check s!"protocol limit {name}: {required} ≤ {actual}" (required ≤ actual)
  check "incoming argument limit fits input register"
    (limits.maxArgumentsLength ≤ limits.maxRegisterSize)
  for length in [limits.maxArgumentsLength - 1, limits.maxArgumentsLength,
      limits.maxArgumentsLength + 1] do
    let args := List.replicate length (32 : UInt8)
    let result := Near.validateActions limits [.functionCall "ft_balance_of" args (300 * 10 ^ 12) 0]
    if length ≤ limits.maxArgumentsLength then
      check s!"incoming validation accepts {length} argument bytes"
        (match result with | .ok () => true | _ => false)
    else
      check s!"incoming validation rejects {length} argument bytes"
        (match result with
        | .error (.functionCallArgumentsLengthExceeded actual bound) =>
          actual == length && bound == limits.maxArgumentsLength
        | _ => false)
  check "protocol initial memory pages" (limits.initialMemoryPages == 1024)
  check "protocol maximum memory pages" (limits.maxMemoryPages == 2048)
  for version in [29, 48, 49, 84, RuntimeConfig.latestVersion] do
    let pinned ← RuntimeConfig.load "../../../near-lean/vm/configs" version
    check s!"protocol {version}: every instruction costs gas (fuel sufficiency premise)"
      (0 < pinned.wasm.regularOpCost && 0 < pinned.wasm.linearOpBaseCost)
  let contractBytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode contractBytes with
    | .ok m => pure m
    | .error error => throw (IO.userError error.message)
  check "protocol prepares deployed module" (prepareLimitError limits module).isNone
  -- `refines_wnear` is about `Binary.wNearBytes`, which `Binary/Bytes.lean` reads from the
  -- file when it is elaborated: check that it holds the file's bytes.
  check "the embedded binary is contract.wasm" (WNear.Binary.wNearBytes == contractBytes)
  let code : Near.Boundary.Code :=
    { code := { module, size := contractBytes.size, hash := "" }, codeOf := fun _ => default }
  let cmp := fun name snap c => compare name cfg protocol code snap c
  let empty : Snapshot := { storage := [], state := none, usage := 1000 }

  -- A life cycle.
  let (s, _) ← cmp "new with a deposit" empty { method := "new", deposit := 1 }
  let (s, _) ← cmp "near_deposit before new" s { method := "near_deposit", deposit := 10 ^ 24 }
  let (s, _) ← cmp "new" s { method := "new" }
  let (_, _) ← cmp "new twice" s { method := "new" }
  let (s, _) ← cmp "near_deposit registers" s { method := "near_deposit", deposit := 10 ^ 24 }
  let (s, _) ← cmp "near_deposit again" s { method := "near_deposit", deposit := 5 * 10 ^ 23 }
  let (_, _) ← cmp "near_deposit too small" s
    { predecessor := bob, method := "near_deposit", deposit := 1 }
  let (s, _) ← cmp "storage_deposit for bob" s
    { method := "storage_deposit", args := "{\"account_id\":\"bob.near\"}", deposit := 10 ^ 22 }
  let (_, _) ← cmp "storage_deposit already registered" s
    { method := "storage_deposit", deposit := 10 ^ 22 }
  let (s, _) ← cmp "ft_transfer with memo" s
    { method := "ft_transfer", deposit := 1,
      args := "{\"receiver_id\":\"bob.near\",\"amount\":\"1000\",\"memo\":\"thanks \\\"x\\\" é\"}" }
  let (_, _) ← cmp "ft_transfer without one yocto" s
    { method := "ft_transfer", args := "{\"receiver_id\":\"bob.near\",\"amount\":\"1\"}" }
  let (_, _) ← cmp "ft_transfer to self" s
    { method := "ft_transfer", deposit := 1, args := "{\"receiver_id\":\"alice.near\",\"amount\":\"1\"}" }
  let (_, _) ← cmp "ft_transfer of zero" s
    { method := "ft_transfer", deposit := 1, args := "{\"receiver_id\":\"bob.near\",\"amount\":\"0\"}" }
  let (_, _) ← cmp "ft_transfer, array form and non-canonical amount" s
    { method := "ft_transfer", deposit := 1, args := " [\"bob.near\", \"+007\", null] " }
  let (s, _) ← cmp "ft_transfer_call" s
    { method := "ft_transfer_call", deposit := 1,
      args := "{\"receiver_id\":\"bob.near\",\"amount\":\"10\",\"msg\":\"hi\\u0001\"}" }
  let (_, _) ← cmp "ft_transfer_call with too little gas for its promises" s
    { method := "ft_transfer_call", deposit := 1, gas := 29 * 10 ^ 12,
      args := "{\"receiver_id\":\"bob.near\",\"amount\":\"10\",\"msg\":\"\"}" }
  let resolve := "{\"sender_id\":\"alice.near\",\"receiver_id\":\"bob.near\",\"amount\":\"10\"}"
  for (name, results) in [
      ("missing", []), ("not ready", [.notReady]), ("failed", [.failed]),
      ("zero", [.successful (bytes "\"0\"")]), ("partial", [.successful (bytes "\"7\"")]),
      ("noncanonical", [.successful (bytes " \"+0007\"\n")]),
      ("escaped", [.successful (bytes "\"\\u0037\"")]),
      ("overflow", [.successful (bytes "\"340282366920938463463374607431768211456\"")]),
      ("invalid UTF8", [.successful [255]]), ("numeric JSON", [.successful (bytes "7")]),
      ("additional results", [.successful (bytes "\"7\""), .failed])] do
    let (_, _) ← cmp s!"ft_resolve_transfer: {name}" s
      { predecessor := wrapId, method := "ft_resolve_transfer", args := resolve, results }
  let (_, _) ← cmp "ft_resolve_transfer is private" s
    { method := "ft_resolve_transfer", args := resolve, results := [.failed] }
  let (_, _) ← cmp "ft_resolve_transfer rejects a deposit" s
    { predecessor := wrapId, method := "ft_resolve_transfer", args := resolve, deposit := 1 }
  let (s, _) ← cmp "near_withdraw" s
    { method := "near_withdraw", deposit := 1, args := "{\"amount\":\"1000\"}" }
  let (_, _) ← cmp "near_withdraw more than the balance" s
    { method := "near_withdraw", deposit := 1, args := "{\"amount\":\"10000000000000000000000000\"}" }
  let (_, _) ← cmp "near_withdraw by an unregistered account" s
    { predecessor := bob, method := "near_withdraw", deposit := 1, args := "{\"amount\":\"1\"}" }
  for (method, args) in [("ft_total_supply", "{}"), ("ft_balance_of", "{\"account_id\":\"alice.near\"}"),
      ("ft_metadata", "garbage"), ("storage_balance_bounds", ""),
      ("storage_balance_of", "{\"account_id\":\"bob.near\"}"), ("storage_minimum_balance", "{}")] do
    let (_, _) ← cmp s!"view {method}" s { method, args }
  let (_, _) ← cmp "storage_withdraw of zero" s
    { method := "storage_withdraw", deposit := 1, args := "{\"amount\":\"0\"}" }
  let (_, _) ← cmp "storage_withdraw of one" s
    { method := "storage_withdraw", deposit := 1, args := "{\"amount\":\"1\"}" }
  let (_, _) ← cmp "storage_unregister with a balance" s
    { method := "storage_unregister", deposit := 1, args := "{}" }

  -- Probe the exact model allowance and the JSON nesting boundary. Comparisons
  -- use the same deployed binary, rollback checks and output observations as above.
  let balanceArgs := "{\"account_id\":\"alice.near\"}"
  let balanceCtx ← contextOf protocol s { method := "ft_balance_of", args := balanceArgs }
  let balanceBound := gasBound balanceCtx (.ftBalanceOf alice)
  let (_, measured) ← cmp "ft_balance_of gas measurement" s
    { method := "ft_balance_of", args := balanceArgs }
  for gas in [0, measured.usedGas - 1, measured.usedGas, measured.usedGas + 1,
      balanceBound - 1, balanceBound, balanceBound + 1] do
    let (_, _) ← cmp s!"ft_balance_of gas boundary {gas}" s
      { method := "ft_balance_of", args := balanceArgs, gas }
  for depth in [1, 32, 126, 127, 128, 129, 256, 512, 1024, 2048, 4096] do
    let nested := String.join (List.replicate depth "[") ++ "0" ++ String.join (List.replicate depth "]")
    let args := "{\"account_id\":\"alice.near\",\"ignored\":" ++ nested ++ "}"
    let (_, _) ← cmp s!"ft_balance_of ignored nesting {depth}" s { method := "ft_balance_of", args }

  for count in [64, 1024, 4096, 16384] do
    let escaped := String.join (List.replicate count "\\n")
    let args := "{\"account_id\":\"alice.near\",\"ignored\":\"" ++ escaped ++ "\"}"
    let (_, _) ← cmp s!"ft_balance_of ignored escapes {count}" s { method := "ft_balance_of", args }
  for args in ["{\"account_id\":\"alice.near\",\"ignored\":[[0]}",
      "{\"account_id\":\"alice.near\",\"ignored\":\"\\ud800\"}",
      "{\"account_id\":\"alice.near\",\"ignored\":[1,]}"] do
    let (_, _) ← cmp "ft_balance_of malformed ignored value" s { method := "ft_balance_of", args }

  -- Adversarial configuration experiment, not a claim about protocol 86:
  -- Receipt-valid arguments still require the protocol argument/register limit
  -- relation. This deliberately violates that relation to reach the host trap.
  let smallProtocol := { protocol with wasm := { protocol.wasm with limits :=
    { protocol.wasm.limits with maxRegisterSize := 16 } } }
  let smallArgs := "{\"account_id\":\"alice.near\"}"
  let smallCtx ← contextOf smallProtocol s { method := "ft_balance_of", args := smallArgs }
  let smallRaw := s.storage.toFinset
  let smallResult := Near.Boundary.execOn code s.storage smallCtx
  IO.println s!"reduced register-limit experiment: {repr smallResult.outcome}"
  check "reduced register-limit input parses" (Call.decode "ft_balance_of" (bytes smallArgs) == some (.ftBalanceOf alice))
  check "reduced register-limit is a non-resource rollback"
    (rolledBack smallCtx smallRaw smallResult && !outOfGas smallResult &&
      match smallResult.outcome with | .error .storageProofExceeded => false | _ => true)
  check "reduced register-limit result differs from the model"
    (!matchesCheck cfg smallCtx smallRaw smallResult (contractStep smallCtx s.state (.ftBalanceOf alice)))

  -- Inputs that are no call.
  for (method, args) in [("near_withdraw", "{\"amount\":1}"), ("near_withdraw", "{}"),
      ("ft_balance_of", "{\"account_id\":\"A\"}"), ("ft_transfer", "[\"bob.near\",\"1\"]"),
      ("ft_balance_of", "{\"account_id\":\"bob.near\",\"account_id\":\"bob.near\"}"),
      ("storage_unregister", ""), ("nope", "{}"), ("", "{}")] do
    let (_, _) ← cmp s!"no call: {method} {args}" s { method, args, deposit := 1 }

  -- Resource failures the model predicts exactly.
  let (_, _) ← cmp "balance exceeded by a withdrawal" s
    { method := "near_withdraw", deposit := 1, args := "{\"amount\":\"1000\"}", balance := 0 }
  let (_, _) ← cmp "lack of balance for state after registering" s
    { predecessor := ⟨"carol.near", by decide⟩, method := "near_deposit", deposit := 10 ^ 22,
      balance := 0 }

  -- Below the bound: the model's behaviour or an out-of-gas failure with no effects.
  for gas in [10 ^ 9, 10 ^ 11, 3 * 10 ^ 11, 5 * 10 ^ 11] do
    let (_, r) ← cmp s!"ft_transfer with {gas} gas" s
      { method := "ft_transfer", deposit := 1, gas,
        args := "{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"memo\":\"m\"}" }
    check s!"ft_transfer with {gas} gas runs out" (outOfGas r)

  -- Adversarial trie: registered accounts whose keys share ever longer
  -- prefixes with alice's and bob's (one differing in each nibble of each
  -- character), so the paths to the keys a transfer touches are as deep as
  -- the trie allows.
  let crowd : List WNear.AccountId := (neighbours alice ++ neighbours bob).eraseDups
  let base : State := ⟨∅, fun _ => 0, 0, cfg.measuredAccountStorageUsage⟩
  let balances : List (WNear.AccountId × Nat) := [(alice, 10 ^ 24), (bob, 10 ^ 24)] ++ crowd.map (·, 0)
  let crafted : State := balances.foldl (fun st (a, b) => addAccount st a b) base
  let craftedStorage := (stateKey, header crafted) ::
    balances.map fun (a, b) => (accountKey a, Borsh.u128 b)
  let usage := storageUsageOf protocol craftedStorage.toFinset + 1000
  let adversarial : Snapshot := { storage := craftedStorage, state := some crafted, usage }
  check s!"adversarial state has {crowd.length} neighbouring accounts" (crowd.length > 20)
  let (_, _) ← cmp "ft_transfer on an adversarial trie" adversarial
    { method := "ft_transfer", deposit := 1,
      args := "{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"memo\":\"m\"}" }
  let (_, _) ← cmp "ft_transfer_call on an adversarial trie" adversarial
    { method := "ft_transfer_call", deposit := 1,
      args := "{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"msg\":\"\"}" }
  let (_, _) ← cmp "near_withdraw on an adversarial trie" adversarial
    { method := "near_withdraw", deposit := 1, args := "{\"amount\":\"1\"}" }
  let (_, _) ← cmp "storage_unregister on an adversarial trie" adversarial
    { predecessor := crowd.headD alice, method := "storage_unregister", deposit := 1, args := "{}" }
  pure ()
