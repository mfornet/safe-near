import NearVM.MeteredHosts.StorageMetered

/-!
# Resource frames for storage writes

The restoration equality exposes every field except the explicit effects of
storage mutation, trie accounting, gas/profiles, the usage log, and the two
runtime-maintained context counters. It holds even if a burn charge fails;
gas promise reservations are deliberately excluded in that case.
-/
namespace Wasm.Near.MeteredHosts.StorageFrame
open StorageMetered

/-- Mask exactly the fields touched by storage wrappers and burn charges. -/
def restore (before after : NearState) : NearState :=
  { after with
    storage := before.storage
    storageKeys := before.storageKeys
    iterators := before.iterators
    storageAccounting := before.storageAccounting
    storageLog := before.storageLog
    gas := before.gas
    gasProfile := before.gasProfile
    actionProfile := before.actionProfile
    context := { after.context with
      storageUsage := before.context.storageUsage
      usedGas := before.context.usedGas } }

/-- Memory and all host resources outside the stated storage/gas effects. -/
def Frame (before after : HostStore NearState) : Prop :=
  after.mem = before.mem ∧ restore before.host after.host = before.host

theorem Frame.refl (before : HostStore NearState) : Frame before before := ⟨rfl, rfl⟩

theorem Frame.trans {before middle after : HostStore NearState}
    (hfirst : Frame before middle) (hsecond : Frame middle after) : Frame before after := by
  refine ⟨hsecond.1.trans hfirst.1, ?_⟩
  calc
    restore before.host after.host = restore before.host (restore middle.host after.host) := rfl
    _ = restore before.host middle.host := congrArg (restore before.host) hsecond.2
    _ = before.host := hfirst.2

/-- Burn-list resource preservation includes failure prefixes. -/
theorem charges_restore (before : NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    restore before (applyCharges before charges).1 = before := by
  have h := congrArg (restore before) (applyCharges_frame before charges hburn)
  exact h

/-- Prepayment's used-gas refresh preserves the remaining context and host. -/
theorem prepayment_frame (before : HostStore NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    Frame before (Output.paidStore before (applyCharges before.host charges).1) := by
  exact ⟨rfl, charges_restore before.host charges hburn⟩

/-- The trie phase splice changes only accounting and burnt gas/profile. -/
theorem prepared_frame (before : HostStore NearState) (paid : NearState)
    (trie : _root_.Near.TrieOverlay.State) : Frame before (prepared before paid trie) := ⟨rfl, rfl⟩

/-- Raw discard-output writes preserve every remaining resource. -/
theorem written_frame (before : HostStore NearState) (key value : List UInt8) :
    Frame before (written before key value) := ⟨rfl, rfl⟩

/-- Usage accounting changes only storageUsage and the write log. -/
theorem updateStorageUsage_restore (extra : Nat) (name : String)
    (before after : HostStore NearState) (args : List Value) :
    restore before.host (updateStorageUsage extra name before after args).host =
      restore before.host after.host := by
  simp only [updateStorageUsage]
  repeat' split
  all_goals rfl

/-- The computed post-call store preserves resources without requiring gas
success, memory-read validity, or a complete host-execution premise. -/
theorem finished_frame (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) :
    let paid := (applyCharges (written before key value).host (postCharges before key)).1
    Frame before (finished extra before keyLen keyPtr valueLen valuePtr key value paid) := by
  let paid := (applyCharges (written before key value).host (postCharges before key)).1
  refine ⟨?_, ?_⟩
  · simp only [finished, updateStorageUsage]
    split
    · split <;> rfl
    · rfl
  · rw [finished, updateStorageUsage_restore]
    have hf := applyCharges_frame (written before key value).host (postCharges before key)
      (postCharges_burnsOnly before key)
    have h := congrArg (restore before.host) hf
    exact h

theorem Frame.registers {before after : HostStore NearState} (h : Frame before after) :
    after.host.registers = before.host.registers := by
  have hx := congrArg NearState.registers h.2
  exact hx

theorem Frame.logs {before after : HostStore NearState} (h : Frame before after) :
    after.host.logs = before.host.logs := by
  have hx := congrArg NearState.logs h.2
  exact hx

theorem Frame.config {before after : HostStore NearState} (h : Frame before after) :
    after.host.config = before.host.config := by
  have hx := congrArg NearState.config h.2
  exact hx

theorem Frame.extCosts {before after : HostStore NearState} (h : Frame before after) :
    after.host.extCosts = before.host.extCosts := by
  have hx := congrArg NearState.extCosts h.2
  exact hx

theorem Frame.promises {before after : HostStore NearState} (h : Frame before after) :
    after.host.promises = before.host.promises := by
  have hx := congrArg NearState.promises h.2
  exact hx

theorem Frame.returnData {before after : HostStore NearState} (h : Frame before after) :
    after.host.returnData = before.host.returnData := by
  have hx := congrArg NearState.returnData h.2
  exact hx

theorem Frame.returnedPromise {before after : HostStore NearState} (h : Frame before after) :
    after.host.returnedPromise = before.host.returnedPromise := by
  have hx := congrArg NearState.returnedPromise h.2
  exact hx

theorem Frame.lastError {before after : HostStore NearState} (h : Frame before after) :
    after.host.lastError = before.host.lastError := by
  have hx := congrArg NearState.lastError h.2
  exact hx

theorem Frame.lastExecutionIssue {before after : HostStore NearState} (h : Frame before after) :
    after.host.lastExecutionIssue = before.host.lastExecutionIssue := by
  have hx := congrArg NearState.lastExecutionIssue h.2
  exact hx

theorem Frame.storageProofSize {before after : HostStore NearState} (h : Frame before after) :
    after.host.storageProofSize = before.host.storageProofSize := by
  have hx := congrArg NearState.storageProofSize h.2
  exact hx

theorem Frame.promiseResults {before after : HostStore NearState} (h : Frame before after) :
    after.host.promiseResults = before.host.promiseResults := by
  have hx := congrArg NearState.promiseResults h.2
  exact hx

theorem Frame.fees {before after : HostStore NearState} (h : Frame before after) :
    after.host.fees = before.host.fees := by
  have hx := congrArg NearState.fees h.2
  exact hx

theorem Frame.registerWrite {before after : HostStore NearState} (h : Frame before after) :
    after.host.registerWrite = before.host.registerWrite := by
  have hx := congrArg NearState.registerWrite h.2
  exact hx

theorem Frame.nextIteratorId {before after : HostStore NearState} (h : Frame before after) :
    after.host.nextIteratorId = before.host.nextIteratorId := by
  have hx := congrArg NearState.nextIteratorId h.2
  exact hx

theorem Frame.input {before after : HostStore NearState} (h : Frame before after) :
    after.host.context.input = before.host.context.input := by
  have hx := congrArg (fun ns : NearState => ns.context.input) h.2
  exact hx

theorem Frame.currentAccountId {before after : HostStore NearState} (h : Frame before after) :
    after.host.context.currentAccountId = before.host.context.currentAccountId := by
  have hx := congrArg (fun ns : NearState => ns.context.currentAccountId) h.2
  exact hx

theorem Frame.isView {before after : HostStore NearState} (h : Frame before after) :
    after.host.context.isView = before.host.context.isView := by
  have hx := congrArg (fun ns : NearState => ns.context.isView) h.2
  exact hx

/-- Reads of future key/value spans can reuse their pre-call resource proof. -/
theorem Frame.getMemOrReg {before after : HostStore NearState} (h : Frame before after)
    (ptr len : UInt64) : getMemOrReg after ptr len = getMemOrReg before ptr len := by
  unfold Wasm.getMemOrReg
  rw [h.1, h.registers]

/-- Resource frame for the complete computed store expression used by the
overlay/empty write contracts. Phase gas and accounting can be arbitrary. -/
theorem composed_frame (extra : Nat) (before : HostStore NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge)
    (phasePaid : NearState) (trie : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) :
    let prePaid := (applyCharges before.host charges).1
    let phase := prepared (Output.paidStore before prePaid) phasePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    Frame before (finished extra phase keyLen keyPtr valueLen valuePtr key value paid) := by
  exact (prepayment_frame before charges hburn).trans
    ((prepared_frame _ phasePaid trie).trans
      (finished_frame extra _ keyLen keyPtr valueLen valuePtr key value))

end Wasm.Near.MeteredHosts.StorageFrame
