import NearChain
import Interpreter.Wasm.Decoder.Wat

/-!
# Chain tests: isolation, completion, reachability, and measured gas on wNEAR.
-/

open Wasm Wasm.Near Near

def oneNear : Nat :=
  10 ^ 24

def tgas (n : Nat) : Nat :=
  n * 10 ^ 12

def pkOf (seed : UInt8) : PublicKey :=
  0 :: List.replicate 32 seed

def bytesOf (s : String) : List UInt8 :=
  s.toUTF8.toList

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

def checkSchedules (r : IO.Ref Report) (cfg : RuntimeConfig) (codeOf : CodeTable)
    (ap : ApplyState) : IO Unit := do
  let transfer (id amount : Nat) : Receipt :=
    { predecessorId := "carol.near", receiverId := "bob.near", receiptId := id
      receipt :=
        .action
          { signerId := "carol.near", signerPublicKey := pkOf 4, gasPrice := 0
            actions := [.transfer amount] } }
  let queued : Snapshot :=
    { state :=
        { accounts := [("bob.near", { amount := oneNear, storageUsage := 182 })]
          accessKeys := [(("bob.near", pkOf 4), { nonce := 0, permission := .fullAccess })]
          nextId := 1000 }
      pending := [transfer 101 1, transfer 102 10, transfer 103 100] }
  let scheduled (s : Snapshot) (positions : List Nat) : RunResult :=
    runBlocks cfg codeOf s [{ ap, txs := [], receipts := .indices positions }]
  let ids (s : Snapshot) := s.pending.map (·.receiptId)
  let bobAmount (s : Snapshot) := (s.state.account? "bob.near").map (·.amount)
  let ordered := scheduled queued [2, 0]
  check r "ordered delivery uses original queue positions"
      ((ordered.applies.flatMap (·.outcomes)).map Prod.fst == [103, 101] &&
        bobAmount ordered.snapshot == some (oneNear + 101))
  check r "unselected receipts remain pending"
      (ids ordered.snapshot == [102] && ordered.stop == .fuelExhausted)
  let reverse := scheduled queued [2, 1, 0]
  check r "a full reverse delivery can finish in one block"
      (reverse.stop == .quiescent && bobAmount reverse.snapshot == some (oneNear + 111) &&
        (reverse.applies.flatMap (·.outcomes)).map Prod.fst == [103, 102, 101])
  let idle := scheduled queued []
  check r "an explicit empty delivery preserves pending work"
      (idle.applies.length == 1 && ids idle.snapshot == [101, 102, 103] &&
        bobAmount idle.snapshot == some oneNear &&
        idle.stop == .fuelExhausted)
  let duplicate := scheduled queued [0, 0]
  check r "duplicate delivery positions reject the whole block"
      (duplicate.stop == .invalidSchedule (.unavailableIndex 0) && duplicate.applies.isEmpty &&
        ids duplicate.snapshot == [101, 102, 103] &&
        bobAmount duplicate.snapshot == some oneNear)
  let queuedTx : Transaction :=
    { signerId := "bob.near", publicKey := pkOf 4, nonce := 1
      receiverId := "bob.near", actions := [.transfer 1] }
  let invalid :=
    runBlocks cfg codeOf queued [{ ap, txs := [queuedTx], receipts := .indices [0, 3] }]
  check r "out-of-range delivery rejects transactions before applying them"
      (invalid.stop == .invalidSchedule (.unavailableIndex 3) && invalid.applies.isEmpty &&
        ids invalid.snapshot == [101, 102, 103] &&
        invalid.snapshot.state.nextId == 1000)
  let stopped :=
    runBlocks cfg codeOf queued
      [{ ap, txs := [], receipts := .indices [2] }, { ap, txs := [], receipts := .indices [5] },
        { ap, txs := [], receipts := .all }]
  check r "a rejected later block preserves earlier commits and skips later blocks"
      (stopped.applies.length == 1 && stopped.stop == .invalidSchedule (.unavailableIndex 5) &&
        ids stopped.snapshot == [101, 102] &&
        bobAmount stopped.snapshot == some (oneNear + 100))
  check r "positions distinguish receipts even when receipt ids repeat"
      (match ReceiptSchedule.resolve [transfer 9 1, transfer 9 10] (.indices [1]) with
      | .error _ => false
      | .ok (selected, deferred) =>
        selected.flatMap (·.actions.map Action.deposit) == [10] &&
          deferred.flatMap (·.actions.map Action.deposit) == [1])
  -- Exhaust every sequence of up to four positions for a three-receipt queue,
  -- including duplicates and unknown positions, against an independent index view.
  let sequences (length : Nat) : List (List Nat) :=
    (List.range length).foldl
      (fun lists _ => lists.flatMap fun xs => (List.range 4).map fun i => xs ++ [i]) [[]]
  let schedules := (List.range 5).flatMap sequences
  check r "341 delivery schedules match the independent index specification"
      (schedules.length == 341 &&
        schedules.all fun positions =>
          match ReceiptSchedule.resolve queued.pending (.indices positions) with
          | .error _ => !(positions.Nodup && positions.all (· < 3))
          | .ok (selected, deferred) =>
            positions.Nodup && positions.all (· < 3) &&
              selected.map (·.receiptId) == positions.map (· + 101) &&
              deferred.map (·.receiptId) ==
                ((List.range 3).filter fun i => !positions.contains i).map (· + 101))
  let limited :=
    runBlocks cfg codeOf queued
      [{ ap := { ap with gasLimit := some 0 }, txs := [], receipts := .indices [2, 0] }]
  check r "runtime gas delays and scheduler deferrals stay in distinct queues"
      (ids limited.snapshot == [102] && limited.snapshot.state.delayed.map (·.receiptId) == [101] &&
        bobAmount limited.snapshot == some (oneNear + 100))
  let drainedDelayed := scheduled limited.snapshot []
  check r "empty incoming delivery still processes runtime-delayed receipts"
      (ids drainedDelayed.snapshot == [102] && drainedDelayed.snapshot.state.delayed.isEmpty &&
        bobAmount drainedDelayed.snapshot == some (oneNear + 101))
  let callback : Receipt :=
    { (transfer 201 2) with
      receipt :=
        .action
          { signerId := "carol.near", signerPublicKey := pkOf 4, gasPrice := 0
            inputDataIds := [500], actions := [.transfer 2] } }
  let data : Receipt :=
    { predecessorId := "carol.near", receiverId := "bob.near", receiptId := 202
      receipt := .data { dataId := 500, data := some [] } }
  let waiting := scheduled { queued with pending := [callback, data] } [0]
  check r "a callback can be delivered before its data without completing"
      (waiting.stop == .fuelExhausted && ids waiting.snapshot == [202] &&
        waiting.snapshot.state.postponed.map Prod.fst == [201] &&
        bobAmount waiting.snapshot == some oneNear)
  let resumed := scheduled waiting.snapshot [0]
  check r "delivering data in a later block resumes the postponed callback"
      (resumed.stop == .quiescent && bobAmount resumed.snapshot == some (oneNear + 2) &&
        (resumed.applies.flatMap (·.outcomes)).map Prod.fst == [201])

def checkWithdrawalSchedule (r : IO.Ref Report) (cfg : RuntimeConfig) (codeOf : CodeTable)
    (ap : ApplyState) (s2 : Snapshot) (depTx : Transaction) : IO Unit := do
  -- Real wNEAR emits transfer and refund receipts. Run those one at a time,
  -- with a distinct block context and an intentional idle block between deliveries.
  let withdrawTx : Transaction :=
    { depTx with
      nonce := 2
      actions :=
        [.functionCall "near_withdraw" (bytesOf "{\"amount\":\"100000000000000000000000\"}")
            (tgas 30) 1] }
  let ordinary := runIsolated cfg codeOf ap s2 [withdrawTx]
  let withdrawal :=
    runBlocks cfg codeOf s2
      [{ ap := { ap with blockHeight := 10 }, txs := [withdrawTx], receipts := .indices [] }]
  check r "a cross-account withdrawal waits for delivery before touching contract storage"
      (withdrawal.stop == .fuelExhausted && withdrawal.snapshot.pending.length == 1 &&
        withdrawal.snapshot.state.storage == s2.state.storage &&
        (withdrawal.applies.flatMap (·.outcomes)).map (·.2.executorId) == ["alice.near"])
  let idle :=
    runBlocks cfg codeOf withdrawal.snapshot
      [{ ap := { ap with blockHeight := 11 }, txs := [], receipts := .indices [] }]
  check r "an idle block does not execute the pending withdrawal call"
      (idle.snapshot.state.storage == s2.state.storage &&
        idle.snapshot.pending.map (·.receiptId) == withdrawal.snapshot.pending.map (·.receiptId))
  let called :=
    runBlocks cfg codeOf idle.snapshot
      [{ ap := { ap with blockHeight := 12 }, txs := [], receipts := .indices [0] }]
  check r "delivering the withdrawal call creates its transfer and refund receipts"
      (called.stop == .fuelExhausted && called.snapshot.pending.length ≥ 2 &&
        called.snapshot.state.storage != s2.state.storage &&
        (called.applies.flatMap (·.outcomes)).any
          (fun (_, outcome) => outcome.executorId == "wrap.near" && outcome.status.isSuccess))
  let earlier : Receipt :=
    { predecessorId := "alice.near", receiverId := "wrap.near", receiptId := 9000
      receipt :=
        .action
          { signerId := "alice.near", signerPublicKey := pkOf 1
            gasPrice := ap.gasPrice, actions := [.transfer 7] } }
  let retained :=
    runBlocks cfg codeOf { s2 with pending := [earlier] }
      [{ ap := { ap with blockHeight := 10 }, txs := [withdrawTx], receipts := .indices [] }]
  check r "deferred incoming work precedes newly emitted transaction receipts"
      (retained.snapshot.pending.map (·.receiptId) ==
        9000 :: withdrawal.snapshot.pending.map (·.receiptId))
  let mut custom := { called with applies := withdrawal.applies ++ idle.applies ++ called.applies }
  for height in List.range 20 do
    if !custom.snapshot.quiescent then
      let next :=
        runBlocks cfg codeOf custom.snapshot
          [{ ap := { ap with blockHeight := 13 + 2 * height }, txs := [], receipts := .indices [] },
            { ap := { ap with blockHeight := 14 + 2 * height }, txs := [],
              receipts := .indices [0] }]
      custom := { next with applies := custom.applies ++ next.applies }
  let balances (s : Snapshot) :=
    s.state.accounts.map fun (id, a) => (id, a.amount, a.locked, a.storageUsage)
  check r "one-receipt custom blocks settle the real wNEAR withdrawal"
      (custom.stop == .quiescent && custom.snapshot.quiescent)
  check r "custom withdrawal scheduling preserves balances and storage"
      (ordinary.stop == .quiescent && balances custom.snapshot == balances ordinary.snapshot &&
        custom.snapshot.state.storage == ordinary.snapshot.state.storage &&
        custom.snapshot.state.accessKeys == ordinary.snapshot.state.accessKeys &&
        custom.snapshot.state.nextId == ordinary.snapshot.state.nextId)
  check r "custom withdrawal scheduling preserves total burnt tokens"
      ((custom.applies.map (·.tokensBurnt)).sum == (ordinary.applies.map (·.tokensBurnt)).sum)

def main (args : List String) : IO UInt32 := do
  let wat := args[0]?.getD "../vm/tests/fixtures/w_near.wat"
  let configs := args[1]?.getD "../vm/configs"
  let r ← IO.mkRef ({} : Report)
  let cfg ← RuntimeConfig.load configs RuntimeConfig.latestVersion
  let text ← IO.FS.readFile wat
  let module ←
    match Decoder.Wat.decode text with
    | .ok m =>
      pure m
    | .error e =>
      do
        IO.println s!"decode error: {e}";
        return 1
  let code : ContractCode := { module, size := 200_000, hash := "w_near" }
  let codeOf : CodeTable := fun _ => code
  let ap : ApplyState := { gasPrice := 100_000_000 }
  let fullAccess : AccessKey := { nonce := 0, permission := .fullAccess }
  let state : ChainState :=
    { accounts :=
        [("alice.near", { amount := 100 * oneNear, storageUsage := 182 }),
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
  check r "step is what runIsolated starts with"
      (match step cfg codeOf genesis { ap, txs := [initTx] } with
      | .error _ => false
      | .ok (next, _) => next.state.nextId == (rs1.head?.map (·.state.nextId)).getD 0)
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
  check r "no receipt upgrades wrap.near"
      ((rs2.flatMap (·.outgoing)).all fun rc => !rc.upgrades "wrap.near")
  check r "a deploy transaction upgrades"
      (Transaction.upgrades "wrap.near" { depTx with actions := [.deployContract code] })
  let foreign : Block := { ap, txs := [{ depTx with signerId := "carol.near" }] }
  check r "independence: a block from carol touches carol, not bob"
      (Block.independentOf foreign s2 "wrap.near" "carol.near" == false &&
        Block.independentOf foreign s2 "wrap.near" "bob.near")
  check r "independence: a deploy block is not independent of wrap.near"
      (Block.independentOf
          { ap,
            txs :=
              [{ depTx with
                  signerId := "carol.near", actions := [.deployContract code] }] }
          s2 "wrap.near" "bob.near" ==
        false)
  -- This measurement happens to suffice for this deposit fixture. It is not
  -- a theorem about minimum prepaid gas, especially for promise-producing calls.
  let measured :=
    measureCallGasBurnt cfg codeOf ap s1 "alice.near" "wrap.near" (pkOf 1) 1 "near_deposit"
      (bytesOf "{}") oneNear
  check r "successful settled call yields a gas measurement" measured.isSome
  let needed := measured.getD 0
  check r "measured burnt gas is positive and below the limit"
      (0 < needed && needed < cfg.wasm.limits.maxTotalPrepaidGas) s!"{needed}"
  let withGas (g : Nat) : Transaction :=
    { depTx with actions := [.functionCall "near_deposit" (bytesOf "{}") g oneNear] }
  let okRun := (runIsolated cfg codeOf ap s1 [withGas needed]).applies
  let allOk := okRun.all fun res => res.outcomes.all fun (_, o) => o.status.isSuccess
  check r "paying measured gas succeeds for this deposit" allOk
  let lessRun := (runIsolated cfg codeOf ap s1 [withGas (10 ^ 11)]).applies
  check r "paying far less fails"
      (!(lessRun.all fun res => res.outcomes.all fun (_, o) => o.status.isSuccess))
  let noBudget := runIsolated cfg codeOf ap genesis [initTx] 0
  check r "zero settlement budget reports unfinished receipts" (noBudget.stop == .fuelExhausted)
  check r "zero budget on an already quiet state reports quiescence"
      ((settle cfg codeOf ap s1 0).stop == .quiescent)
  check r "an unfinished run has no completed gas measurement"
      ((measureCallGasBurnt cfg codeOf ap s1 "alice.near" "wrap.near" (pkOf 1) 1 "near_deposit"
          (bytesOf "{}") oneNear 0).isNone)
  check r "a failed transaction has no successful gas measurement"
      ((measureCallGasBurnt cfg codeOf ap s1 "alice.near" "wrap.near" (pkOf 1) 0 "near_deposit"
          (bytesOf "{}") oneNear).isNone)
  let pending : Receipt :=
    { predecessorId := "carol.near"
      receiverId := "bob.near"
      receiptId := 100
      receipt :=
        .action
          { signerId := "carol.near"
            signerPublicKey := pkOf 4
            gasPrice := ap.gasPrice
            actions := [.transfer 1] } }
  let emptyBlock : Block := { ap, txs := [] }
  check r "independence includes delayed receipts"
      (!(emptyBlock.independentOf { s1 with state := { s1.state with delayed := [pending] } }
          "wrap.near" "bob.near"))
  check r "independence includes postponed receipts"
      (!(emptyBlock.independentOf
          { s1 with state := { s1.state with postponed := [(100, pending)] } } "wrap.near"
          "bob.near"))
  check r "a callback missing its data does not report completion"
      ((settle cfg codeOf ap { s1 with state := { s1.state with postponed := [(100, pending)] } }
            1).stop ==
        .fuelExhausted)
  let issueState :=
    s1.state.setAccount "wrap.near"
      { amount := 10 * oneNear, locked := oneNear, storageUsage := 182 }
  let issueSnapshot : Snapshot := { state := issueState, pending := [pending] }
  let unsupportedTx : Transaction :=
    { signerId := "wrap.near", publicKey := pkOf 3, nonce := 2, receiverId := "wrap.near"
      actions := [.stake 0 (pkOf 3)] }
  let issueRun := runIsolated cfg codeOf ap issueSnapshot [unsupportedTx]
  check r "model issues stop isolated execution immediately"
      (issueRun.applies.length == 1 &&
        match issueRun.stop with
        | .executionIssue _ (.unsupportedAction _) => true
        | _ => false)
  check r "a stopped chain attempt retains incoming receipts"
      (issueRun.snapshot.pending.map (·.receiptId) == [pending.receiptId])
  check r "a stopped chain attempt does not charge the signer"
      ((issueRun.snapshot.state.account? "wrap.near").map (·.amount) == some (10 * oneNear))
  -- The scripted executor's actual result is covered by the public reachability relation.
  have :
    Reachable cfg codeOf genesis
      (runBlocks cfg codeOf genesis [{ ap, txs := [initTx] }]).snapshot :=
    runBlocks_reachable cfg codeOf genesis genesis _ Reachable.refl
  check r "Reachable.step requires a supported execution" (rs1.all fun a => a.issue.isNone)
  checkSchedules r cfg codeOf ap
  let scheduledIssue :=
    { issueSnapshot with pending := [pending, { pending with receiptId := 101 }] }
  let unsupportedScheduled :=
    runBlocks cfg codeOf scheduledIssue
      [{ ap, txs := [unsupportedTx], receipts := .indices [1] },
        { ap, txs := [], receipts := .all }]
  check r "a scripted model issue preserves selected and deferred receipts"
      (unsupportedScheduled.applies.length == 1 &&
        unsupportedScheduled.snapshot.pending.map (·.receiptId) == [100, 101] &&
        match unsupportedScheduled.stop with
        | .executionIssue _ (.unsupportedAction _) => true
        | _ => false)
  checkWithdrawalSchedule r cfg codeOf ap s2 depTx
  let s ← r.get
  IO.println s!"{s.passed} passed, {s.failed} failed"
  return (if s.failed = 0 then 0 else 1)
