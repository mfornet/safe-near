import NearVM
import tests.TrieStorage
import Wasm.Wat

/-!
# VM scenario tests: the real wNEAR binary under `NearVM.run`

`lake exe vm-tests [wat-path] [configs-dir]`. Exit code 1 on any failure.
-/

open Wasm Wasm.Near

def bytesOf (s : String) : List UInt8 := s.toUTF8.toList
def strOf (b : List UInt8) : String := (String.fromUTF8? ⟨b.toArray⟩).getD "<bad utf8>"

def oneNear : Nat := 10 ^ 24
/-- 125 bytes × 10^19: the registration fee wNEAR charges. -/
def registrationFee : Nat := 125 * 10 ^ 19
def wrap := bytesOf "wrap.near"
def alice := bytesOf "alice.near"
def bob := bytesOf "bob.near"

def ctx (predecessor : List UInt8) (method : String) (input : String) (deposit : Nat)
    (gas : Nat := 300 * 10 ^ 12) : VMContext :=
  let _ := method
  { currentAccountId := wrap, signerAccountId := predecessor, signerAccountPk := List.replicate 33 1
    predecessorAccountId := predecessor, input := bytesOf input, attachedDeposit := deposit
    prepaidGas := gas, accountBalance := 100 * oneNear, storageUsage := 150_000 }

structure Harness where
  cfg : RuntimeConfig
  code : Module
  codeSize : Nat

def Harness.call (h : Harness) (storage : List (List UInt8 × List UInt8)) (predecessor : List UInt8)
    (method : String) (input : String) (deposit : Nat) (gas : Nat := 300 * 10 ^ 12)
    (view : Bool := false) : VMOutcome :=
  let c := ctx predecessor method input deposit gas
  let c := if view then { c with viewConfig := some { maxGasBurnt := h.cfg.wasm.limits.maxGasBurnt } } else c
  run h.cfg h.code h.codeSize method c storage

structure Report where
  failed : Nat := 0
  passed : Nat := 0

def check (r : IO.Ref Report) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    r.modify fun s => { s with passed := s.passed + 1 }
    IO.println s!"ok: {name}"
  else
    r.modify fun s => { s with failed := s.failed + 1 }
    IO.println s!"FAIL: {name}{if detail.isEmpty then "" else s!" — {detail}"}"

def describe (o : VMOutcome) : String :=
  s!"aborted={repr o.aborted} burnt={o.burntGas} used={o.usedGas} logs={o.logs} receipts={o.receipts.length}"

/-- The single function-call action of a receipt: (method, deposit, gas). -/
def fcOf : List PromiseAction → Option (String × Nat × UInt64)
  | [.functionCall m _ amount gas] => some (strOf m, amount, gas)
  | _ => none

def returnString (o : VMOutcome) : Option String :=
  match o.returnData with
  | .value b => some (strOf b)
  | _ => none

namespace StorageCosts

private def code (keyLen valueLen valuePtr register : Nat) : IO Module := do
  let text := "(module\n" ++
    "(import \"env\" \"storage_write\" (func $write (param i64 i64 i64 i64 i64) (result i64)))\n" ++
    "(import \"env\" \"storage_remove\" (func $remove (param i64 i64 i64) (result i64)))\n" ++
    "(memory 1) (data (i32.const 0) \"k\") (data (i32.const 8) \"v\")\n" ++
    s!"(func (export \"write\") i64.const {keyLen} i64.const 0 i64.const {valueLen} " ++
    s!"i64.const {valuePtr} i64.const {register} call $write drop)\n" ++
    s!"(func (export \"remove\") i64.const {keyLen} i64.const 0 i64.const {register} call $remove drop))"
  match ← Wat.compile text with
  | .ok module => pure module
  | .error error => throw (IO.userError s!"storage-cost fixture: {error}")

private def context (runtime : Bool) : VMContext :=
  { currentAccountId := "storage.near".toUTF8.toList
    signerAccountId := "alice.near".toUTF8.toList
    signerAccountPk := 0 :: List.replicate 32 1
    predecessorAccountId := "alice.near".toUTF8.toList
    input := [], prepaidGas := 100 * 10 ^ 12, storageUsage := 10000
    chargeStorageValueAccess := runtime }

private def cost (outcome : VMOutcome) (name : String) : Nat :=
  ((outcome.gasProfile.ext.find? (·.1 == name)).map (·.2)).getD 0

/-- Execute Wasm, rather than testing a copy of the charge-list implementation.
The standalone oracle and real runtime intentionally use different adapters. -/
def check (cfg : RuntimeConfig) (check : String → Bool → IO Unit) : IO Unit := do
  let module ← code 1 1 8 0
  for old in ([none, some [], some [42], some (List.replicate 5 42), some (List.replicate 17 42)] :
      List (Option (List UInt8))) do
    let storage := old.toList.map fun value => ([107], value)
    for (method, charge) in [("write", "storage_write_evicted_byte"), ("remove", "storage_remove_ret_value_byte")] do
      let mock := run cfg module 0 method (context false) storage
      let runtime := run cfg module 0 method (context true) storage
      let expected := (old.map List.length).getD 0 * cfg.wasm.extCosts.cost charge
      check s!"{method}: runtime old-value bytes {repr old}"
        (mock.succeeded && runtime.succeeded && runtime.storage == mock.storage &&
          runtime.burntGas == mock.burntGas + expected && cost runtime charge == expected && cost mock charge == 0)
  let storage : List (List UInt8 × List UInt8) := [([107], List.replicate 5 42)]
  let restricted := { cfg with wasm := { cfg.wasm with limits := { cfg.wasm.limits with maxRegisterSize := 2 } } }
  for (method, charge) in [("write", "storage_write_evicted_byte"), ("remove", "storage_remove_ret_value_byte")] do
    let failed := run restricted module 0 method (context true) storage
    check s!"{method}: old-value access precedes output-register failure"
      (failed.aborted.isSome && failed.storage == storage && cost failed charge == 5 * cfg.wasm.extCosts.cost charge)
    let costly := { cfg with wasm := { cfg.wasm with extCosts := {
      lookup := fun name => if name == charge then 10 ^ 12 else cfg.wasm.extCosts.cost name } } }
    let full := run costly module 0 method (context true) storage
    let prepaid := full.burntGas - cost full charge / 2
    let exhausted := run costly module 0 method { context true with prepaidGas := prepaid } storage
    check s!"{method}: exhaustion at old-value charge rolls back storage"
      (exhausted.aborted == some (.hostError .gasExceeded) && exhausted.storage == storage &&
        exhausted.burntGas == prepaid && cost exhausted charge > 0 && cost exhausted charge < cost full charge)
    let view := run cfg module 0 method { context true with viewConfig := some { maxGasBurnt := 10 ^ 14 } } storage
    check s!"{method}: view rejection precedes storage access"
      (view.aborted == some (.hostError (.prohibitedInView ("storage_" ++ method))) && cost view charge == 0)
  let badValue ← code 1 1 (2 ^ 32) 0
  let noKeys := { cfg with wasm := { cfg.wasm with limits := { cfg.wasm.limits with maxLengthStorageKey := 0 } } }
  let rejected := run noKeys badValue 0 "write" (context true) storage
  check "storage key limit precedes inaccessible value and byte fees"
    (rejected.aborted == some (.hostError (.keyLengthExceeded 1 0)) &&
      cost rejected "storage_write_key_byte" == 0 && cost rejected "storage_write_value_byte" == 0 &&
      cost rejected "storage_write_evicted_byte" == 0)
  let noValues := { cfg with wasm := { cfg.wasm with limits := { cfg.wasm.limits with maxLengthStorageValue := 0 } } }
  let rejected := run noValues module 0 "write" (context true) storage
  check "storage value limit precedes byte fees and old-value access"
    (rejected.aborted == some (.hostError (.valueLengthExceeded 1 0)) &&
      cost rejected "storage_write_value_byte" == 0 && cost rejected "storage_write_evicted_byte" == 0)
  let missingRegister ← code 1 (2 ^ 64 - 1) 99 0
  let rejected := run cfg missingRegister 0 "write" (context true) storage
  check "missing value register retains its id before storage access"
    (rejected.aborted == some (.hostError (.invalidRegisterId 99)) && cost rejected "storage_write_evicted_byte" == 0)
  let discarded ← code 1 1 8 (2 ^ 64 - 1)
  let outcome := run cfg discarded 0 "write" (context true) storage
  check "discarding the old-value register still charges storage access"
    (outcome.succeeded && cost outcome "storage_write_evicted_byte" == 5 * cfg.wasm.extCosts.cost "storage_write_evicted_byte")

end StorageCosts

def main (args : List String) : IO UInt32 := do
  let wat := args[0]?.getD "tests/fixtures/w_near.wat"
  let configs := args[1]?.getD "configs"
  let r ← IO.mkRef ({} : Report)
  let cfg ← RuntimeConfig.load configs RuntimeConfig.latestVersion
  let text ← IO.FS.readFile wat
  let code ← match ← Wat.compile text with
    | .ok m => pure m
    | .error e => do IO.println s!"decode error: {e}"; return 1
  let h : Harness := { cfg, code, codeSize := 200_000 }

  let root : ReceiptSpec := { receiverId := alice, actions := [.transfer 1] }
  let joined : VMOutcome := { (default : VMOutcome) with
    receipts := [root, root, { root with dependencies := [0, 0, 1] }]
    returnData := .receiptIndex 2 }
  check r "backward dependencies allow joins and repeated input positions" joined.receiptsValid
  let cycle : VMOutcome := { joined with receipts := [{ root with dependencies := [0] }] }
  check r "self dependencies cannot be accepted as a receipt graph" (!cycle.receiptsValid)
  check r "forward dependencies cannot be accepted as a receipt graph"
    (!({ joined with receipts := [{ root with dependencies := [1] }, root] }.receiptsValid))
  check r "a returned receipt must exist"
    (!({ joined with returnData := .receiptIndex 3 }.receiptsValid))
  let observed := cycle.checkReceipts 99 123 [(alice, [7])]
  check r "invalid receipt graphs are explicit model issues"
    (observed.issue? == some (.interpreterError "invalid receipt dependency graph"))
  check r "invalid graph rejection restores funds, storage and usage"
    (observed.balance == 99 && observed.storageUsage == 123 && observed.storage == [(alice, [7])] &&
      observed.receipts.isEmpty)
  let cyclicJoin : List NearPromise := [.and [0]]
  check r "raw join cycles cannot disappear through bounded flattening"
    ((joined.checkPromises 99 123 [] cyclicJoin).issue?.isSome)
  check r "unsupported yielded handles cannot disappear during conversion"
    ((joined.checkPromises 99 123 [] [.yielded [] [] 0 0 []]).issue?.isSome)

  let nestedHandles : List NearPromise := [
    .batch alice [.transfer 1], .and [0], .callback 1 bob [.transfer 2],
    .and [0, 2, 0], .callback 3 wrap [.transfer 3]]
  match convertPromises nestedHandles with
  | none => check r "valid nested joins convert" false
  | some graph =>
    check r "conversion preserves exact nested join order and duplicate positions"
      (graph.receipts.map (·.dependencies) == [[], [0], [0, 1, 0]])
    check r "conversion preserves receipt actions and receivers"
      (graph.receipts.map (·.receiverId) == [alice, bob, wrap] &&
        graph.receipts.map (·.actions) == [[.transfer 1], [.transfer 2], [.transfer 3]])
    check r "only receipt handles can be returned, including singleton joints"
      (graph.returnedReceipt? 0 == some 0 && (graph.returnedReceipt? 1).isNone &&
        graph.returnedReceipt? 2 == some 1 && graph.returnedReceipt? 4 == some 2)
  check r "conversion rejects unresolved and forward references"
    ((convertPromises [.and [0]]).isNone &&
      (convertPromises [.callback 0 alice []]).isNone &&
      (convertPromises [.and [99]]).isNone)
  check r "conversion does not silently drop unsupported yielded promises"
    ((convertPromises [.yielded [] [] 0 0 []]).isNone)

  let exhausted := run cfg code h.codeSize "new" (ctx alice "new" "{}" 0) [] 0
  check r "fuel exhaustion is explicitly incomplete"
    (exhausted.issue? == some .fuelExhausted)
  check r "interpreter fuel exhaustion is not protocol gas exhaustion"
    (!(exhausted.aborted.map (·.isOutOfGas)).getD false)
  check r "incomplete execution preserves input storage and emits no receipts"
    (exhausted.storage.isEmpty && exhausted.receipts.isEmpty && !exhausted.succeeded)

  let emptyCode ← match ← Wat.compile "(module (func (export \"empty\")))" with
    | .ok m => pure m
    | .error e => throw (IO.userError e)
  let exactBudget := run cfg emptyCode 0 "empty" (ctx alice "empty" "{}" 0) [] 1
  check r "completion on the last interpreter step is not fuel exhaustion" exactBudget.succeeded

  -- Execute unsupported operations, rather than checking the host registry.
  -- Imports alone must remain usable for contracts with unreachable crypto code.
  for (name, params, arguments, results) in
      [("sha256", "i64 i64 i64", "i64.const 0 i64.const 0 i64.const 0", ""),
       ("validator_total_stake", "i64", "i64.const 0", ""),
       ("promise_yield_resume", "i64 i64 i64 i64",
        "i64.const 0 i64.const 0 i64.const 0 i64.const 0", "(result i64)"),
       ("promise_batch_action_deploy_global_contract", "i64 i64 i64",
        "i64.const 0 i64.const 0 i64.const 0", ""),
       ("promise_batch_action_deploy_global_contract_by_account_id", "i64 i64 i64",
        "i64.const 0 i64.const 0 i64.const 0", ""),
       ("promise_batch_action_use_global_contract", "i64 i64 i64",
        "i64.const 0 i64.const 0 i64.const 0", ""),
       ("promise_batch_action_use_global_contract_by_account_id", "i64 i64 i64",
        "i64.const 0 i64.const 0 i64.const 0", "")] do
    let wat := s!"(module (import \"env\" \"{name}\" (func $unsupported (param {params}) {results}))
      (memory 1) (func (export \"test\") {arguments} call $unsupported {if results.isEmpty then "" else "drop"})
      (func (export \"unused\")))"
    let testCode ← match ← Wat.compile wat with
      | .ok m => pure m
      | .error e => throw (IO.userError s!"unsupported-host fixture: {e}")
    let outcome := run cfg testCode 0 "test" (ctx alice "test" "{}" 0) []
    check r s!"{name}: unsupported execution is explicit"
      (outcome.issue? == some (.unsupportedHost name)) (describe outcome)
    check r s!"{name}: unsupported semantics never emit receipts" outcome.receipts.isEmpty
    let unused := run cfg testCode 0 "unused" (ctx alice "unused" "{}" 0) []
    check r s!"{name}: importing an unused operation is allowed" unused.succeeded

  -- Weighted function calls (nearcore `distribute_gas`): the unused prepaid gas
  -- goes to weights 1 and 2 in proportion, the remainder to the last weighted
  -- call; an unweighted call keeps its static gas.
  let weightedCode ← match ← Wat.compile "(module
      (import \"env\" \"promise_batch_create\" (func $batch (param i64 i64) (result i64)))
      (import \"env\" \"promise_batch_action_function_call_weight\"
        (func $weighted (param i64 i64 i64 i64 i64 i64 i64 i64)))
      (import \"env\" \"promise_batch_action_function_call\"
        (func $call (param i64 i64 i64 i64 i64 i64 i64)))
      (memory 1) (data (i32.const 0) \"alice.near\") (data (i32.const 16) \"m\")
      (func (export \"test\") (local i64)
        i64.const 10 i64.const 0 call $batch local.set 0
        local.get 0 i64.const 1 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 1000 i64.const 1
        call $weighted
        local.get 0 i64.const 1 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 i64.const 2
        call $weighted
        local.get 0 i64.const 1 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 5
        call $call)
      (func (export \"zero\") (local i64)
        i64.const 10 i64.const 0 call $batch local.set 0
        local.get 0 i64.const 1 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 7 i64.const 0
        call $weighted))" with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"weighted fixture: {e}")
  let weighted := run cfg weightedCode 0 "test" (ctx alice "test" "{}" 0) []
  match (weighted.receipts.map (·.actions) : List (List PromiseAction)) with
  | [[.functionCall _ _ _ g1, .functionCall _ _ _ g2, .functionCall _ _ _ g3]] =>
    let unused := (g1.toNat - 1000) + g2.toNat
    check r "weighted calls share the unused gas by weight"
      (g1.toNat ≥ 1000 && unused > 0 && g1.toNat - 1000 == unused * 1 / 3 &&
        g2.toNat == unused * 2 / 3 + (unused - unused * 1 / 3 - unused * 2 / 3) && g3 == 5)
      (describe weighted)
    check r "weighted distribution uses all prepaid gas" (weighted.usedGas == 300 * 10 ^ 12)
      (describe weighted)
  | _ => check r "weighted calls share the unused gas by weight" false (describe weighted)
  let zeroWeight := run cfg weightedCode 0 "zero" (ctx alice "zero" "{}" 0) []
  check r "weight zero is a plain function call"
    (zeroWeight.receipts.map (·.actions) == [[.functionCall (bytesOf "m") [] 0 7]] &&
      zeroWeight.usedGas < 300 * 10 ^ 12) (describe zeroWeight)

  -- config sanity
  check r "config: regular_op_cost loaded" (cfg.wasm.regularOpCost = 822756)
  check r "config: storage price loaded" (cfg.storageAmountPerByte = 10 ^ 19)
  check r "config: ext cost 'base' loaded" (cfg.wasm.extCosts.cost "base" > 0)
  let missing := run cfg code h.codeSize "does_not_exist" (ctx alice "" "{}" 0) []
  check r "legacy method-resolution failure discards loading gas"
    (missing.burntGas == 0 && missing.usedGas == 0)
  let empty := run cfg code h.codeSize "" (ctx alice "" "{}" 0 (gas := 0)) []
  check r "empty method takes precedence over loading gas exhaustion"
    (empty.aborted == some (.methodResolveError .methodEmptyName) && empty.burntGas == 0)
  let loadingFailure := run cfg code h.codeSize "does_not_exist" (ctx alice "" "{}" 0 (gas := 1)) []
  check r "loading exhaustion takes precedence over a missing export"
    (loadingFailure.aborted == some (.hostError .gasExceeded))
  let fixedCfg := { cfg with wasm := { cfg.wasm with fixContractLoadingCost := true } }
  let fixedMissing := run fixedCfg code h.codeSize "does_not_exist" (ctx alice "" "{}" 0) []
  check r "loading-fix feature retains loading gas on method-resolution failure"
    (fixedMissing.burntGas > 0 && fixedMissing.aborted == some (.methodResolveError .methodNotFound))

  -- new
  let o1 := h.call [] alice "new" "{}" 0
  check r "new succeeds" o1.succeeded (describe o1)
  check r "new writes STATE" (o1.storage.any fun kv => kv.1 == bytesOf "STATE") (describe o1)
  check r "new burns gas within limits" (0 < o1.burntGas && o1.burntGas ≤ o1.usedGas && o1.usedGas ≤ 300 * 10 ^ 12)
  check r "new grows storage usage by the STATE record" (o1.storageUsage = 150_000 + 5 + 29 + 40) s!"{o1.storageUsage}"
  check r "new twice panics" (match (h.call o1.storage alice "new" "{}" 0).aborted with
    | some (.hostError (.guestPanic m)) => (m.splitOn "already been initialized").length > 1
    | _ => false)

  -- near_deposit
  let o2 := h.call o1.storage alice "near_deposit" "{}" oneNear
  check r "near_deposit succeeds" o2.succeeded (describe o2)
  check r "near_deposit logs the minted amount"
    (o2.logs == [s!"Deposit {oneNear - registrationFee} NEAR to alice.near"]) s!"{o2.logs}"
  check r "near_deposit creates no receipts" (o2.receipts.isEmpty)
  -- every call starts from the harness's fixed `storageUsage`; STATE is rewritten at the same
  -- size and the record for the 10-byte id `alice.near` is (1 + 4 + 10) + 16 + 40 bytes.
  check r "near_deposit adds the account record (71 bytes for alice.near)" (o2.storageUsage = 150_000 + 71)
    s!"{o1.storageUsage} -> {o2.storageUsage}"
  let bal := h.call o2.storage bob "ft_balance_of" "{\"account_id\":\"alice.near\"}" 0 (view := true)
  check r "ft_balance_of reports deposit minus fee"
    (returnString bal == some s!"\"{oneNear - registrationFee}\"") s!"{returnString bal}"
  check r "view call changes nothing" (bal.storage == o2.storage && bal.receipts.isEmpty)
  let ts := h.call o2.storage bob "ft_total_supply" "{}" 0 (view := true)
  check r "ft_total_supply equals the single balance" (returnString ts == returnString bal)

  -- near_withdraw
  let amount := 3 * 10 ^ 23
  let o3 := h.call o2.storage alice "near_withdraw" s!"\{\"amount\":\"{amount}\"}" 1
  check r "near_withdraw succeeds" o3.succeeded (describe o3)
  check r "near_withdraw transfers amount + 1 back"
    (o3.receipts == [{ receiverId := alice, actions := [.transfer (amount + 1)] }])
  check r "near_withdraw used gas covers the transfer fee" (o3.usedGas > o3.burntGas)
  -- the balance the contract sees includes the attached 1 yocto, then the transfer leaves
  check r "near_withdraw deducts the transfer from the contract balance"
    (o3.balance = 100 * oneNear + 1 - (amount + 1)) s!"{o3.balance}"
  let bal3 := h.call o3.storage bob "ft_balance_of" "{\"account_id\":\"alice.near\"}" 0 (view := true)
  check r "balance drops by the withdrawn amount"
    (returnString bal3 == some s!"\"{oneNear - registrationFee - amount}\"")
  let o3b := h.call o2.storage alice "near_withdraw" s!"\{\"amount\":\"{amount}\"}" 0
  check r "near_withdraw without 1 yocto panics with the SDK message"
    (match o3b.aborted with
      | some (.hostError (.guestPanic m)) => (m.splitOn "Requires attached deposit of exactly 1 yoctoNEAR").length > 1
      | _ => false) (describe o3b)
  check r "a panicking call leaves storage untouched" (o3b.storage == o2.storage)
  check r "a panicking call still burns gas" (o3b.burntGas > 0)
  let o3c := h.call o2.storage alice "near_withdraw" s!"\{\"amount\":\"{2 * oneNear}\"}" 1
  check r "overdraft panics" (match o3c.aborted with
      | some (.hostError (.guestPanic m)) => (m.splitOn "doesn't have enough balance").length > 1
      | _ => false) (describe o3c)

  -- ft_transfer_call: bob must be registered first
  let o4 := h.call o3.storage bob "storage_deposit" "{}" (2 * registrationFee)
  check r "storage_deposit registers bob and refunds the excess" (o4.succeeded ∧
    o4.receipts == [{ receiverId := bob, actions := [.transfer registrationFee] }]) (describe o4)
  let o5 := h.call o4.storage alice "ft_transfer_call"
    "{\"receiver_id\":\"bob.near\",\"amount\":\"1000\",\"msg\":\"hi\"}" 1
  check r "ft_transfer_call succeeds" o5.succeeded (describe o5)
  let (r1, r2) := match o5.receipts with
    | [r1, r2] => (some r1, some r2)
    | _ => (none, none)
  check r "ft_transfer_call schedules ft_on_transfer then ft_resolve_transfer"
    ((r1.map (·.receiverId)) == some bob && (r2.map (·.receiverId)) == some wrap &&
     (r2.map (·.dependencies)) == some [0] &&
     (r1.bind (fcOf ·.actions)).map (·.1) == some "ft_on_transfer" &&
     (r2.bind (fcOf ·.actions)) == some ("ft_resolve_transfer", 0, UInt64.ofNat (5 * 10 ^ 12))) (describe o5)
  check r "ft_transfer_call returns the callback's receipt" (o5.returnData == .receiptIndex 1)
  check r "ft_transfer_call attaches the remaining gas"
    ((r1.bind (fcOf ·.actions)).map (·.2.2) == some (UInt64.ofNat (300 * 10 ^ 12 - 30 * 10 ^ 12)))

  -- the callback, with a failed ft_on_transfer: everything refunded
  let cbCtx : VMContext := { ctx wrap "ft_resolve_transfer" "" 0 with
    promiseResults := [.failed] }
  let o6 := run cfg code 200_000 "ft_resolve_transfer" { cbCtx with
      input := bytesOf "{\"sender_id\":\"alice.near\",\"receiver_id\":\"bob.near\",\"amount\":\"1000\"}" }
    o5.storage
  check r "ft_resolve_transfer after a failed call refunds the sender" (o6.succeeded ∧
    o6.logs == ["Refund 1000 from bob.near to alice.near"] && returnString o6 == some "\"0\"") (describe o6)
  let o6b := run cfg code 200_000 "ft_resolve_transfer" { ctx alice "ft_resolve_transfer" "" 0 with
      input := bytesOf "{\"sender_id\":\"alice.near\",\"receiver_id\":\"bob.near\",\"amount\":\"1000\"}" }
    o5.storage
  check r "ft_resolve_transfer is private" (match o6b.aborted with
      | some (.hostError (.guestPanic m)) => (m.splitOn "is private").length > 1
      | _ => false) (describe o6b)

  -- errors
  let o7 := h.call o2.storage alice "near_deposit" "{}" oneNear (gas := 10 ^ 11)
  check r "too little gas fails with GasExceeded"
    (o7.aborted == some (.hostError .gasExceeded) && o7.storage == o2.storage) (describe o7)
  check r "out-of-gas burns at most the prepaid gas" (o7.burntGas ≤ 10 ^ 11 && o7.burntGas > 0)
  let o8 := h.call o2.storage alice "no_such_method" "{}" 0
  check r "unknown method is a MethodResolveError"
    (o8.aborted == some (.methodResolveError .methodNotFound))
  let o9 := h.call o2.storage alice "near_deposit" "{}" 0
  check r "near_deposit without deposit panics" (match o9.aborted with
      | some (.hostError (.guestPanic m)) => (m.splitOn "Requires positive attached deposit").length > 1
      | _ => false) (describe o9)

  TrieStorage.check cfg (fun name ok => check r name ok)
  StorageCosts.check cfg (fun name ok => check r name ok)
  let s ← r.get
  IO.println s!"{s.passed} passed, {s.failed} failed"
  return (if s.failed = 0 then 0 else 1)
