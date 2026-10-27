import NearVM.MeteredHosts.StorageReadCanonical
import NearVM.MeteredHosts.StorageReadMetered

/-! Successful metered canonical storage reads from original host resources. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered StorageOverlay
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

theorem beforeCharges_burnsOnly (before : HostStore NearState) (keyLen keyPtr register : UInt64) :
    ∀ c ∈ chargesBefore "storage_read" before (args keyLen keyPtr register), BurnsOnly c := by
  simp only [chargesBefore, storageMutationPlan?, creationAccountArgs, chargesBeforeUnvalidated,
    args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ]
  by_cases h : keyLen = u64Max
  · cases hm : before.host.registers keyPtr.toNat <;> simp [readSpan, h, hm, BurnsOnly]
  · simp [readSpan, h, BurnsOnly]

theorem writeReg_burnsOnly (length : Nat) : ∀ c ∈ writeReg length, BurnsOnly c := by
  simp [writeReg, BurnsOnly]

def preCharges (before : HostStore NearState) (keyLen keyPtr register : UInt64) :=
  chargesBefore "storage_read" before (args keyLen keyPtr register)
def prePaid (before : HostStore NearState) (keyLen keyPtr register : UInt64) :=
  (applyCharges before.host (preCharges before keyLen keyPtr register)).1
def beforeTrie (before : HostStore NearState) (keyLen keyPtr register : UInt64) :=
  Output.paidStore before (prePaid before keyLen keyPtr register)
def result (before : HostStore NearState) (keyLen keyPtr register : UInt64)
    (initial : State) (p : ReadPlan) (value : List UInt8) : HostStore NearState :=
  let phase := p.result (beforeTrie before keyLen keyPtr register) initial
  let raw := written phase register value
  {raw with host := (applyCharges raw.host (writeReg value.length)).1}

/-- The actual successful read, with all billing equations discharged by
credits and all trie success discharged by original canonical WF. The guest
context, storage map and original register limits are not replaced. -/
theorem canonical_contract (extra : Nat) (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hstorage : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (ha : before.host.storageAccounting = some ctx.trie)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hs : before.host.storage key = some value)
    (hreg : register = u64Max ∨ withinLimit before.host.config.maxRegisterLen value.length = true)
    (hp : recordedStorageError before.host
      (readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).looked = none)
    (hc : before.host.gas.Credits
      (burnSum before.host.extCosts (preCharges before keyLen keyPtr register) +
        (burnSum before.host.extCosts
          ((readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).charges ctx.trie) +
          (burnSum before.host.extCosts (writeReg value.length) + rest)))) :
    let p := readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie
    (metered extra "storage_read" storageReadFn).invoke before (args keyLen keyPtr register) =
      .Return [.i64 1] (result before keyLen keyPtr register ctx.trie p value) ∧
    (result before keyLen keyPtr register ctx.trie p value).host.gas.burnt = before.host.gas.burnt +
      burnSum before.host.extCosts (preCharges before keyLen keyPtr register) +
      burnSum before.host.extCosts (p.charges ctx.trie) + burnSum before.host.extCosts (writeReg value.length) ∧
    (result before keyLen keyPtr register ctx.trie p value).host.gas.promises = before.host.gas.promises ∧
    (result before keyLen keyPtr register ctx.trie p value).host.gas.Credits rest := by
  let charges := preCharges before keyLen keyPtr register
  let paid := prePaid before keyLen keyPtr register
  let b := beforeTrie before keyLen keyPtr register
  let p := readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie
  let phase := p.result b ctx.trie
  let output := written phase register value
  have hb : ∀ c ∈ charges, BurnsOnly c := beforeCharges_burnsOnly before keyLen keyPtr register
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
  have cr := applyCharges_credits before.host charges
    (burnSum before.host.extCosts (p.charges ctx.trie) + (burnSum before.host.extCosts (writeReg value.length) + rest)) hb hc
  have reps : Represents b.host ctx storage := ⟨current.trans hr.1, fun k => (congrFun store k).trans (hr.2 k)⟩
  have keyRead : getMemOrReg b keyPtr keyLen = some key := by
    exact (Output.paidStore_read before charges keyLen keyPtr hb).trans hk
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
  have cp : b.host.gas.Credits (burnSum b.host.extCosts (p.charges ctx.trie) +
      (burnSum before.host.extCosts (writeReg value.length) + rest)) := by
    change paid.gas.Credits (burnSum paid.extCosts (p.charges ctx.trie) + _)
    rw [ext]
    exact cr.2.2.2.2
  have prep := prepare_canonical_credits b ctx raw hwf storage hstorage reps hnodes keyLen keyPtr register key
    (burnSum before.host.extCosts (writeReg value.length) + rest) (by change paid.storageAccounting = _; rw [accounting, ha])
    keyRead limall (by simpa only [planEq] using cp)
    (by simpa only [planEq] using proof)
  rw [planEq] at prep
  have outputGas : output.host.gas = phase.host.gas := by
    dsimp only [output, written]
    split <;> rfl
  have outputExt : output.host.extCosts = before.host.extCosts := by
    dsimp only [output, written]
    split <;> simpa only [phase, ReadPlan.result, prepared, b, beforeTrie, Output.paidStore, ext, NearState.setRegister]
  have postc : output.host.gas.Credits (burnSum output.host.extCosts (writeReg value.length) + rest) := by
    rw [outputExt]
    dsimp only [output, written]
    split <;> exact prep.2.2
  have pc := applyCharges_credits output.host (writeReg value.length) rest (writeReg_burnsOnly value.length) postc
  have inv := metered_hit extra before keyLen keyPtr register key value paid (p.paid b ctx.trie)
    (applyCharges output.host (writeReg value.length)).1 p.fetched (Prod.ext rfl cr.1) keyRead limit
    (by rw [store]; exact hs) (by rcases hreg with h | h; exact Or.inl h; exact Or.inr (by rw [config]; exact h))
    prep.1 (Prod.ext rfl pc.1)
  have phaseBurn : phase.host.gas.burnt = paid.gas.burnt + burnSum paid.extCosts (p.charges ctx.trie) := prep.2.1
  have paidBurn : paid.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts charges := cr.2.1
  have phasePromises : phase.host.gas.promises = paid.gas.promises := rfl
  refine ⟨inv, ?_, ?_, pc.2.2.2.2⟩
  · change (applyCharges output.host (writeReg value.length)).1.gas.burnt = _
    rw [pc.2.1, outputGas, phaseBurn, paidBurn, ext, outputExt]
  · change (applyCharges output.host (writeReg value.length)).1.gas.promises = _
    rw [pc.2.2.1, outputGas, phasePromises]
    exact cr.2.2.1

theorem canonical_hit (extra : Nat) (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hstorage : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (ha : before.host.storageAccounting = some ctx.trie)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hs : before.host.storage key = some value)
    (hreg : register = u64Max ∨ withinLimit before.host.config.maxRegisterLen value.length = true)
    (hp : recordedStorageError before.host
      (readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).looked = none)
    (hc : before.host.gas.Credits
      (burnSum before.host.extCosts (preCharges before keyLen keyPtr register) +
        (burnSum before.host.extCosts
          ((readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).charges ctx.trie) +
          (burnSum before.host.extCosts (writeReg value.length) + rest)))) :
    let p := readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie
    (metered extra "storage_read" storageReadFn).invoke before (args keyLen keyPtr register) =
      .Return [.i64 1] (result before keyLen keyPtr register ctx.trie p value) ∧
    (result before keyLen keyPtr register ctx.trie p value).host.gas.Credits rest := by
  have h := canonical_contract extra before ctx raw hwf storage hstorage hr hnodes keyLen keyPtr register key value rest ha hk hl hs hreg hp hc
  exact ⟨h.1, h.2.2.2⟩

end Wasm.Near.MeteredHosts.StorageRead
