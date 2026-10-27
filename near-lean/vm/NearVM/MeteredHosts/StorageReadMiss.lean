import NearVM.MeteredHosts.StorageReadResult

/-! Complete absent-key storage reads through the actual metered wrapper. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered StorageOverlay
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

theorem finish_miss (extra : Nat) (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key : List UInt8)
    (hk : getMemOrReg before keyPtr keyLen = some key) (hs : before.host.storage key = none) :
    finishMeteredCall extra "storage_read" before (args keyLen keyPtr register) (.Return [.i64 0] before) =
      .Return [.i64 0] before := by
  simp only [finishMeteredCall, chargesAfter, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ, hk, hs, applyCharges]
  simp [deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
    usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

theorem metered_miss (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr register : UInt64) (key : List UInt8) (paid phasePaid : NearState) (trie : State)
    (hc : applyCharges before.host (chargesBefore "storage_read" before (args keyLen keyPtr register)) = (paid, none))
    (hk : getMemOrReg (Output.paidStore before paid) keyPtr keyLen = some key)
    (hl : withinLimit paid.config.maxStorageKeyLen key.length = true)
    (hs : paid.storage key = none)
    (hp : prepareStorageCall "storage_read" (Output.paidStore before paid) (args keyLen keyPtr register) =
      (prepared (Output.paidStore before paid) phasePaid trie, none)) :
    (metered extra "storage_read" storageReadFn).invoke before (args keyLen keyPtr register) =
      .Return [.i64 0] (prepared (Output.paidStore before paid) phasePaid trie) := by
  simp only [metered, show deprecatedRuntimeHost "storage_read" = false by decide,
    show viewRestrictedHost "storage_read" = false by decide, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hc]
  change (match preInvokeError "storage_read" (Output.paidStore before paid) (args keyLen keyPtr register) with
    | some error => trapWith (Output.paidStore before paid) error
    | none => invokeStorageCall extra "storage_read" storageReadFn (Output.paidStore before paid) (args keyLen keyPtr register)) = _
  rw [pre_error]
  simp only [invokeStorageCall, hp]
  rw [raw_miss (prepared (Output.paidStore before paid) phasePaid trie) keyLen keyPtr register key hk hl hs]
  exact finish_miss extra _ keyLen keyPtr register key hk hs

def missResult (before : HostStore NearState) (keyLen keyPtr register : UInt64) (initial : State) (p : ReadPlan) :=
  p.result (beforeTrie before keyLen keyPtr register) initial

/-- Absence is derived from the original canonical/raw representation. The
actual metered call returns zero and performs no raw register mutation. -/
theorem canonical_miss (extra : Nat) (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hstorage : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (keyLen keyPtr register : UInt64) (key : List UInt8) (rest : Nat)
    (ha : before.host.storageAccounting = some ctx.trie)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hs : before.host.storage key = none)
    (hp : recordedStorageError before.host
      (readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).looked = none)
    (hc : before.host.gas.Credits (burnSum before.host.extCosts (preCharges before keyLen keyPtr register) +
      (burnSum before.host.extCosts
        ((readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).charges ctx.trie) + rest))) :
    let p := readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie
    (metered extra "storage_read" storageReadFn).invoke before (args keyLen keyPtr register) =
      .Return [.i64 0] (missResult before keyLen keyPtr register ctx.trie p) ∧
    (missResult before keyLen keyPtr register ctx.trie p).host.gas.burnt = before.host.gas.burnt +
      burnSum before.host.extCosts (preCharges before keyLen keyPtr register) + burnSum before.host.extCosts (p.charges ctx.trie) ∧
    (missResult before keyLen keyPtr register ctx.trie p).host.gas.promises = before.host.gas.promises ∧
    (missResult before keyLen keyPtr register ctx.trie p).host.gas.Credits rest := by
  let charges := preCharges before keyLen keyPtr register
  let paid := prePaid before keyLen keyPtr register
  let b := beforeTrie before keyLen keyPtr register
  let p := readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie
  have hb := beforeCharges_burnsOnly before keyLen keyPtr register
  have frame := applyCharges_frame before.host charges hb
  have current : paid.context.currentAccountId = before.host.context.currentAccountId := by
    have h := congrArg (fun ns : NearState => ns.context.currentAccountId) frame
    exact h
  have store : paid.storage = before.host.storage := by
    have h := congrArg NearState.storage frame
    exact h
  have config : paid.config = before.host.config := by
    have h := congrArg NearState.config frame
    exact h
  have accounting : paid.storageAccounting = before.host.storageAccounting := by
    have h := congrArg NearState.storageAccounting frame
    exact h
  have mode : paid.storageReadsFromTrie = before.host.storageReadsFromTrie := by
    have h := congrArg NearState.storageReadsFromTrie frame
    exact h
  have ext : paid.extCosts = before.host.extCosts := by
    have h := congrArg NearState.extCosts frame
    exact h
  have cr := applyCharges_credits before.host charges (burnSum before.host.extCosts (p.charges ctx.trie) + rest) hb hc
  have reps : Represents b.host ctx storage := ⟨current.trans hr.1, fun k => (congrFun store k).trans (hr.2 k)⟩
  have keyRead : getMemOrReg b keyPtr keyLen = some key := (Output.paidStore_read before charges keyLen keyPtr hb).trans hk
  have planEq : readPlan ctx.trie (contractKey b.host.context.currentAccountId key) b.host.storageReadsFromTrie = p := by
    change readPlan ctx.trie (contractKey paid.context.currentAccountId key) paid.storageReadsFromTrie = p
    rw [current, mode]
  have proof : recordedStorageError b.host p.looked = none := by
    have pp := recordedStorageError_charges before charges p.looked hb
    simpa only [b, beforeTrie, prePaid, Output.paidStore, recordedStorageError] using pp.trans hp
  have limit : withinLimit paid.config.maxStorageKeyLen key.length = true := by rw [config]; exact hl
  have limall : ∀ lim, b.host.config.maxStorageKeyLen = some lim → key.length ≤ lim := by
    intro lim he
    change paid.config.maxStorageKeyLen = some lim at he
    simp only [withinLimit, he, decide_eq_true_eq] at limit
    exact limit
  have cp : b.host.gas.Credits (burnSum b.host.extCosts (p.charges ctx.trie) + rest) := by
    change paid.gas.Credits (burnSum paid.extCosts (p.charges ctx.trie) + rest)
    rw [ext]; exact cr.2.2.2.2
  have prep := prepare_canonical_credits b ctx raw hwf storage hstorage reps hnodes keyLen keyPtr register key rest
    (by change paid.storageAccounting = _; rw [accounting, ha]) keyRead limall
    (by simpa only [planEq] using cp) (by simpa only [planEq] using proof)
  rw [planEq] at prep
  have inv := metered_miss extra before keyLen keyPtr register key paid (p.paid b ctx.trie) p.fetched
    (Prod.ext rfl cr.1) keyRead limit (by rw [store]; exact hs) prep.1
  refine ⟨inv, ?_, ?_, prep.2.2⟩
  · have phaseBurn : (p.result b ctx.trie).host.gas.burnt = paid.gas.burnt + burnSum paid.extCosts (p.charges ctx.trie) := prep.2.1
    have paidBurn : paid.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts charges := cr.2.1
    change (p.result b ctx.trie).host.gas.burnt = _
    rw [phaseBurn, paidBurn, ext]
  · exact cr.2.2.1

/-- Missing reads frame original memory and every register, for all register IDs. -/
theorem missResult_frame (before : HostStore NearState) (keyLen keyPtr register : UInt64)
    (initial : State) (p : ReadPlan) :
    (missResult before keyLen keyPtr register initial p).mem = before.mem ∧
    (missResult before keyLen keyPtr register initial p).host.registers = before.host.registers := by
  have r := congrArg NearState.registers (applyCharges_frame before.host (preCharges before keyLen keyPtr register)
    (beforeCharges_burnsOnly before keyLen keyPtr register))
  exact ⟨rfl, r⟩

end Wasm.Near.MeteredHosts.StorageRead
