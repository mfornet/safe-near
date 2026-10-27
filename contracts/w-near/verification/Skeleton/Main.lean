import Skeleton.Model

/-!
# Executable M2 validation

`lake exe wnear-skeleton` executes the walking module through the actual
receipt boundary, with a canonical trie, on creation, replacement and arbitrary
binary inputs. For each successful run it repeats at the exact measured burn
budget and at one unit below it, keeping `prepaid_gas` unchanged. These checks
validate the proposed M2 statements; they are not a universal `Refines` proof.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near NearInterface

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAIL: {label}")

private def account : IO NearInterface.AccountId :=
  if h : validAccountIdBytes "skeleton.near".toUTF8.toList = true then pure ⟨"skeleton.near", h⟩
  else throw (IO.userError "invalid skeleton account")

private def context (cfg : RuntimeConfig) (storage : List (Near.Bytes × Near.Bytes))
    (args : Near.Bytes) : IO Context := do
  let account ← account
  let trie ← match Near.TrieOverlay.start (storage.map fun (k, v) =>
      (Near.TrieOverlay.contractKey account.bytes k, v)) with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"trie: {e}")
  pure {
    method := "save", args, current := account, predecessor := account, signer := account,
    signerPk := [], attached := 0, prepaidGas := 300 * 10^12,
    promiseResults := [], outputDataReceivers := [], balance := 100 * 10^24,
    locked := 0, storageUsage := 1000 + storageUsageOf cfg storage.toFinset,
    blockHeight := 1, timestamp := 0, epochHeight := 1, randomSeed := List.replicate 32 0,
    trie, protocol := cfg }

private def withBudget (ctx : Context) (budget : Nat) : Context :=
  { ctx with protocol := { ctx.protocol with wasm := { ctx.protocol.wasm with
      limits := { ctx.protocol.wasm.limits with maxGasBurnt := budget } } } }

private def rolledBack (ctx : Context) (storage : List (Near.Bytes × Near.Bytes))
    (r : Observation) : Bool :=
  decide (r.storage = storage.toFinset) && r.balance == ctx.balance &&
  r.storageUsage == ctx.storageUsage && r.receipts.isEmpty && r.trie.prospective.isEmpty

/-- Compare the independent resource-aware model with the runtime outcome. -/
private def modelCheck (ctx : Context) (storage : Storage) (r : Observation) : Bool :=
  match modelStep ctx (some storage) () with
  | .ok _ => matchesCheck ctx storage r
  | .error failed =>
    (match r.outcome with
      | .error actual => decide (actual = ContractModel.ModelFailure.toFailure
          (model fun _ _ _ => 0) failed.failure)
      | .ok _ => false) && rolledBack ctx storage r && r.logs == failed.logs

private def gasFailure (r : Observation) : Bool :=
  match r.outcome with | .error .outOfGas => true | _ => false

private def validate (cfg : RuntimeConfig) (label : String)
    (storage : List (Near.Bytes × Near.Bytes)) (args : Near.Bytes) : IO Unit := do
  let ctx ← context cfg storage args
  let full := Near.Boundary.execOn code storage ctx
  check s!"{label}: successful model result ({repr full.outcome})" (modelCheck ctx storage full)
  check s!"{label}: no gas reservation" (full.burntGas == full.usedGas)
  let exactCtx := withBudget ctx full.burntGas
  let exact := Near.Boundary.execOn code storage exactCtx
  check s!"{label}: exact budget model result" (modelCheck exactCtx storage exact)
  check s!"{label}: exact cost" (exact.burntGas == full.burntGas)
  let budgets := [0, full.burntGas / 4, full.burntGas / 2, full.burntGas - 1]
  for budget in budgets do
    let lowCtx := withBudget ctx budget
    let low := Near.Boundary.execOn code storage lowCtx
    check s!"{label}: gas failure at {budget} ({repr low.outcome})" (gasFailure low)
    check s!"{label}: rollback at {budget}" (rolledBack lowCtx storage low)
    check s!"{label}: log prefix at {budget}" (low.logs.isPrefixOf full.logs)
    check s!"{label}: budget respected at {budget}" (low.burntGas <= budget)
    check s!"{label}: prepaid gas fixed" (lowCtx.prepaidGas == ctx.prepaidGas)
  -- The actual Refines clauses fix the protocol and vary prepaid gas.
  let exactPrepaidCtx := { ctx with prepaidGas := full.burntGas }
  let exactPrepaid := Near.Boundary.execOn code storage exactPrepaidCtx
  check s!"{label}: exact prepaid gas" (modelCheck exactPrepaidCtx storage exactPrepaid)
  check s!"{label}: exact prepaid cost" (exactPrepaid.burntGas == full.burntGas)
  for prepaid in [0, full.burntGas / 2, full.burntGas - 1] do
    let lowCtx := { ctx with prepaidGas := prepaid }
    let low := Near.Boundary.execOn code storage lowCtx
    check s!"{label}: low prepaid out of gas at {prepaid}" (gasFailure low)
    check s!"{label}: low prepaid rollback at {prepaid}" (rolledBack lowCtx storage low)
    check s!"{label}: low prepaid log prefix at {prepaid}" (low.logs.isPrefixOf full.logs)
    check s!"{label}: low prepaid budget at {prepaid}" (low.burntGas <= prepaid)
  -- A late failure: the VM has written storage, emitted its log and returned,
  -- but the receipt cannot fund storage. All effects except the log roll back.
  let poorCtx := { ctx with balance := 0 }
  let poor := Near.Boundary.execOn code storage poorCtx
  check s!"{label}: storage-stake rollback ({repr poor.outcome}, usage {poor.storageUsage}, balance {poor.balance}, prospective {poor.trie.prospective.length})" (rolledBack poorCtx storage poor)
  check s!"{label}: storage-stake log survives" (poor.logs == ["saved"])
  check s!"{label}: independent model stake failure" (modelCheck poorCtx storage poor)
  check s!"{label}: storage-stake failure" (match poor.outcome with
    | .error (.lackBalanceForState _) => true | _ => false)
  for method in ["", "unknown"] do
    let invalidCtx := { ctx with method }
    let invalid := Near.Boundary.execOn code storage invalidCtx
    check s!"{label}: invalid method rollback" (rolledBack invalidCtx storage invalid)
    check s!"{label}: invalid method not execution issue" (match invalid.outcome with
      | .error (.executionIssue _) => false | .error _ => true | _ => false)
  IO.println s!"ok: {label}: {args.length} input bytes, exact cost {full.burntGas}, 4 smaller burn budgets, 3 smaller prepaid budgets and storage-stake rollback"

/-- Deterministic host-limit failures before and after observable effects. -/
private def validateLimits (cfg : RuntimeConfig) : IO Unit := do
  let storage := [("other".toUTF8.toList, "retained".toUTF8.toList)]
  let ctx ← context cfg storage "hello".toUTF8.toList
  let cases : List (String × LimitConfig × List String) := [
    ("register size", { cfg.wasm.limits with maxRegisterSize := 0 }, []),
    ("log count", { cfg.wasm.limits with maxNumberLogs := 0 }, []),
    ("log bytes", { cfg.wasm.limits with maxTotalLogLength := 4 }, []),
    ("storage key", { cfg.wasm.limits with maxLengthStorageKey := 0 }, []),
    ("storage value", { cfg.wasm.limits with maxLengthStorageValue := 4 }, []),
    ("return bytes", { cfg.wasm.limits with maxLengthReturnedData := 4 }, ["saved"])]
  for (label, limits, logs) in cases do
    let limited := { ctx with protocol := { cfg with wasm := { cfg.wasm with limits } } }
    let r := Near.Boundary.execOn code storage limited
    check s!"{label}: independent model" (modelCheck limited storage r)
    check s!"{label}: rollback" (rolledBack limited storage r)
    check s!"{label}: expected log prefix" (r.logs == logs)
    IO.println s!"ok: forced {label} limit: {repr r.outcome}"

/-- This pins an observed interpreter limitation, not a nearcore behavior. -/
private def validateKnownLimitGap (cfg : RuntimeConfig) : IO Unit := do
  let limited := { cfg with wasm := { cfg.wasm with
    limits := { cfg.wasm.limits with maxNumberRegisters := 0 } } }
  let ctx ← context limited [] "hello".toUTF8.toList
  let r := Near.Boundary.execOn code [] ctx
  check "runtime-known-limit-gap: maxNumberRegisters is currently unenforced" (matchesCheck ctx [] r)
  IO.println "ok: runtime-known-limit-gap: maxNumberRegisters=0 currently succeeds (not nearcore validated)"
  let smallCtx := { ctx with balance := 0, storageUsage := 0 }
  let small := Near.Boundary.execOn code [] smallCtx
  check "zero-balance account exemption below 770 bytes" (matchesCheck smallCtx [] small)
  IO.println "ok: zero-balance account exemption below 770 bytes"

end WNear.Skeleton

def main : IO Unit := do
  let cfg ← Wasm.Near.RuntimeConfig.load "../../../near-lean/vm/configs"
    Wasm.Near.RuntimeConfig.latestVersion
  let b := fun (s : String) => s.toUTF8.toList
  WNear.Skeleton.validate cfg "create/empty" [] []
  WNear.Skeleton.validate cfg "create/text" [] (b "hello")
  WNear.Skeleton.validate cfg "create/binary" [] [0, 255, 128, 192]
  WNear.Skeleton.validate cfg "create/long" [] (List.replicate 4096 97)
  WNear.Skeleton.validate cfg "replace/shrink" [(b "k", b "old value"), (b "other", b "retained")] (b "x")
  WNear.Skeleton.validate cfg "replace/grow" [(b "k", b "x"), (b "other", b "retained")] (b "a longer value")

  WNear.Skeleton.validateLimits cfg

  WNear.Skeleton.validateKnownLimitGap cfg
