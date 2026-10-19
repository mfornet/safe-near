import NearChain
import Interpreter.Wasm.Decoder.Wat

/-!
# Chain tests: isolation, completion, reachability, and measured gas on wNEAR.
-/

open Wasm Wasm.Near Near

def oneNear : Nat := 10 ^ 24
def tgas (n : Nat) : Nat := n * 10 ^ 12
def pkOf (seed : UInt8) : PublicKey := 0 :: List.replicate 32 seed
def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

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

def main (args : List String) : IO UInt32 := do
  let wat := args[0]?.getD "../vm/tests/fixtures/w_near.wat"
  let configs := args[1]?.getD "../vm/configs"
  let r ← IO.mkRef ({} : Report)
  let cfg ← RuntimeConfig.load configs RuntimeConfig.latestVersion
  let text ← IO.FS.readFile wat
  let module ← match Decoder.Wat.decode text with
    | .ok m => pure m
    | .error e => do IO.println s!"decode error: {e}"; return 1
  let code : ContractCode := { module, size := 200_000, hash := "w_near" }
  let codeOf : CodeTable := fun _ => code
  let ap : ApplyState := { gasPrice := 100_000_000 }
  let fullAccess : AccessKey := { nonce := 0, permission := .fullAccess }
  let state : ChainState :=
    { accounts := [("alice.near", { amount := 100 * oneNear, storageUsage := 182 }),
                   ("wrap.near", { amount := 10 * oneNear, storageUsage := 182, code := some code })]
      accessKeys := [(("alice.near", pkOf 1), fullAccess), (("wrap.near", pkOf 3), fullAccess)] }
  let genesis : Snapshot := { state }
  let initTx : Transaction :=
    { signerId := "wrap.near", publicKey := pkOf 3, nonce := 1, receiverId := "wrap.near"
      actions := [.functionCall "new" (bytesOf "{}") (tgas 50) 0] }
  let initRun := runIsolated cfg codeOf ap genesis [initTx]
  let s1 := initRun.snapshot
  let rs1 := initRun.applies
  check r "runIsolated reports quiescence" (initRun.stop == .quiescent)
  check r "runIsolated settles" s1.quiescent
  check r "runIsolated reports one apply per round" (rs1.length ≥ 2) s!"{rs1.length}"
  check r "step is what runIsolated starts with" ((step cfg codeOf genesis { ap, txs := [initTx] }).1.state.nextId
    = (rs1.head?.map (·.state.nextId)).getD 0)

  -- a deposit in isolation
  let depTx : Transaction :=
    { signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near"
      actions := [.functionCall "near_deposit" (bytesOf "{}") (tgas 30) oneNear] }
  let depositRun := runIsolated cfg codeOf ap s1 [depTx]
  let s2 := depositRun.snapshot
  let rs2 := depositRun.applies
  check r "deposit in isolation settles" s2.quiescent
  check r "deposit touched alice and wrap.near only"
    ((rs2.flatMap (·.outgoing)).all fun rc => rc.touches "alice.near" || rc.touches "wrap.near")
  check r "no receipt upgrades wrap.near" ((rs2.flatMap (·.outgoing)).all fun rc => !rc.upgrades "wrap.near")
  check r "a deploy transaction upgrades"
    (Transaction.upgrades "wrap.near" { depTx with actions := [.deployContract code] })
  let foreign : Block := { ap, txs := [{ depTx with signerId := "carol.near" }] }
  check r "independence: a block from carol touches carol, not bob"
    (Block.independentOf foreign s2 "wrap.near" "carol.near" == false
      && Block.independentOf foreign s2 "wrap.near" "bob.near")
  check r "independence: a deploy block is not independent of wrap.near"
    (Block.independentOf { ap, txs := [{ depTx with signerId := "carol.near", actions := [.deployContract code] }] }
      s2 "wrap.near" "bob.near" == false)

  -- This measurement happens to suffice for this deposit fixture. It is not
  -- a theorem about minimum prepaid gas, especially for promise-producing calls.
  let measured := measureCallGasBurnt cfg codeOf ap s1 "alice.near" "wrap.near" (pkOf 1) 1 "near_deposit" (bytesOf "{}") oneNear
  check r "successful settled call yields a gas measurement" measured.isSome
  let needed := measured.getD 0
  check r "measured burnt gas is positive and below the limit" (0 < needed && needed < cfg.wasm.limits.maxTotalPrepaidGas) s!"{needed}"
  let withGas (g : Nat) : Transaction := { depTx with actions := [.functionCall "near_deposit" (bytesOf "{}") g oneNear] }
  let okRun := (runIsolated cfg codeOf ap s1 [withGas needed]).applies
  let allOk := okRun.all fun res => res.outcomes.all fun (_, o) => o.status.isSuccess
  check r "paying measured gas succeeds for this deposit" allOk
  let lessRun := (runIsolated cfg codeOf ap s1 [withGas (10 ^ 11)]).applies
  check r "paying far less fails" (!(lessRun.all fun res => res.outcomes.all fun (_, o) => o.status.isSuccess))

  let noBudget := runIsolated cfg codeOf ap genesis [initTx] 0
  check r "zero settlement budget reports unfinished receipts" (noBudget.stop == .fuelExhausted)
  check r "zero budget on an already quiet state reports quiescence"
    ((settle cfg codeOf ap s1 0).stop == .quiescent)
  check r "an unfinished run has no completed gas measurement"
    ((measureCallGasBurnt cfg codeOf ap s1 "alice.near" "wrap.near" (pkOf 1) 1
      "near_deposit" (bytesOf "{}") oneNear 0).isNone)
  check r "a failed transaction has no successful gas measurement"
    ((measureCallGasBurnt cfg codeOf ap s1 "alice.near" "wrap.near" (pkOf 1) 0
      "near_deposit" (bytesOf "{}") oneNear).isNone)

  let pending : Receipt := {
    predecessorId := "carol.near"
    receiverId := "bob.near"
    receiptId := 100
    receipt := .action {
      signerId := "carol.near"
      signerPublicKey := pkOf 4
      gasPrice := ap.gasPrice
      actions := [.transfer 1] } }
  let emptyBlock : Block := { ap, txs := [] }
  check r "independence includes delayed receipts"
    (!(emptyBlock.independentOf { s1 with state := { s1.state with delayed := [pending] } } "wrap.near" "bob.near"))
  check r "independence includes postponed receipts"
    (!(emptyBlock.independentOf { s1 with state := { s1.state with postponed := [(100, pending)] } } "wrap.near" "bob.near"))
  check r "a callback missing its data does not report completion"
    ((settle cfg codeOf ap { s1 with state := { s1.state with postponed := [(100, pending)] } } 1).stop == .fuelExhausted)

  let issueState := s1.state.setAccount "wrap.near"
    { amount := 10 * oneNear, locked := oneNear, storageUsage := 182 }
  let issueSnapshot : Snapshot := { state := issueState, pending := [pending] }
  let unsupportedTx : Transaction := {
    signerId := "wrap.near", publicKey := pkOf 3, nonce := 2, receiverId := "wrap.near"
    actions := [.stake 0 (pkOf 3)] }
  let issueRun := runIsolated cfg codeOf ap issueSnapshot [unsupportedTx]
  check r "model issues stop isolated execution immediately"
    (issueRun.applies.length == 1 && match issueRun.stop with
      | .executionIssue _ (.unsupportedAction _) => true
      | _ => false)
  check r "a stopped chain attempt retains incoming receipts"
    (issueRun.snapshot.pending.map (·.receiptId) == [pending.receiptId])
  check r "a stopped chain attempt does not charge the signer"
    ((issueRun.snapshot.state.account? "wrap.near").map (·.amount) == some (10 * oneNear))

  -- Reachable is inhabited by what runIsolated computes
  have : (step cfg codeOf genesis { ap, txs := [initTx] }).2.issue = none →
      Reachable cfg codeOf genesis (step cfg codeOf genesis { ap, txs := [initTx] }).1 :=
    fun h => Reachable.step _ h Reachable.refl
  check r "Reachable.step requires a supported execution" (rs1.all fun a => a.issue.isNone)

  let s ← r.get
  IO.println s!"{s.passed} passed, {s.failed} failed"
  return (if s.failed = 0 then 0 else 1)
