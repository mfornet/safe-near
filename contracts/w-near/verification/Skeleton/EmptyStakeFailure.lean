import Skeleton.EmptySuccess
import Skeleton.SuccessExecution

/-!
# Empty-base storage-stake rejection after normal VM completion

All VM-side size and log checks accept the save body. The receipt boundary may
still reject its increased storage usage. That check runs after the derived
normal outcome and both empty receipt validations, preserves the saved log,
and rolls back the receipt's effects.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts

/-- The model's post-save storage deficit, computed from original data. -/
def saveStakeDeficit (ctx : Context) (storage : Storage) : Nat :=
  stakeDeficit ctx.protocol
    (ctx.storageUsage - storageUsageOf ctx.protocol storage.toFinset +
      storageUsageOf ctx.protocol (savedStorage storage ctx.args).toFinset)
    (ctx.balance + ctx.attached) ctx.locked

/-- After all VM checks accept, positive stake deficit is the independent
model's final failure, retaining the log emitted before the return. -/
theorem modelStep_save_stakeFailure (ctx : Context) (st : Option Storage)
    (h : ModelSaveLimits ctx) (hdeficit : 0 < saveStakeDeficit ctx (st.getD [])) :
    modelStep ctx st () =
      .error ⟨.panic (.lackBalanceForState (saveStakeDeficit ctx (st.getD []))), ["saved"]⟩ := by
  have hz : ctx.protocol.wasm.limits.maxNumberLogs ≠ 0 := Nat.ne_of_gt h.logs
  simp only [saveStakeDeficit] at hdeficit ⊢
  simp [modelStep, Nat.not_lt.mpr h.input, Nat.not_lt.mpr h.key,
    Nat.not_lt.mpr h.value, hz, Nat.not_lt.mpr h.logBytes, Nat.not_lt.mpr h.returned, hdeficit]

/-- Actual empty-base execution matches the model's positive-stake failure.
The VM's successful completion, exact deficit, empty receipt checks and retained
log are derived; no execution equation or zero-stake premise is assumed. -/
theorem execOn_empty_matches_stakeFailure
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (storage : Storage) (st : Option Storage) (rest : Nat)
    (hwf : ctx.WF storage.toFinset)
    (hrepresented : (model gasBound).Represents storage.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) storage
        (emptyAfter ctx storage) (emptyCost ctx storage) rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none)
    (hdeficit : 0 < saveStakeDeficit ctx storage) :
    Matches (model gasBound) ctx storage.toFinset (Near.Boundary.execOn code storage ctx)
      ((model gasBound).step ctx st ()) := by
  have hr := emptyAfter_resources ctx storage rest hwf hp hm hread hentries hselected hcredits hproof
  have hu := emptyAfter_usage ctx storage rest hwf hp hm hentries hselected hroom hcredits hproof
  have hstate := represented_storage_getD gasBound storage st hrepresented
  have hupdated : (savedStorage (st.getD []) ctx.args).toFinset =
      (savedStorage storage ctx.args).toFinset := by
    simp only [savedStorage, rawWrite_toFinset, hstate]
  have hmodelDeficit : saveStakeDeficit ctx (st.getD []) = saveStakeDeficit ctx storage := by
    simp only [saveStakeDeficit, hstate, hupdated]
  change Matches (model gasBound) ctx storage.toFinset (Near.Boundary.execOn code storage ctx)
    (modelStep ctx st ())
  rw [modelStep_save_stakeFailure ctx st hm (by rw [hmodelDeficit]; exact hdeficit), hmodelDeficit]
  have hrun := run_save_success_public ctx.protocol (Near.Boundary.toVMContext ctx) storage
    (emptyAfter ctx storage) (emptyCost ctx storage) rest 0 hp hr (emptyAfter_promises ctx storage)
  obtain ⟨habort, _, _, husage, hbalance, hlogs, hreceipts, _⟩ := executionOutcome_fields ctx.protocol
    (Near.Boundary.toVMContext ctx) storage (emptyAfter ctx storage) _
    (emptyAfter_representation ctx storage hwf) (emptyAfter_promises ctx storage) (emptyAfter_logs ctx storage)
  have hactualDeficit :
      stakeDeficit ctx.protocol
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) storage
          (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) storage (emptyAfter ctx storage))) none).storageUsage
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) storage
          (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) storage (emptyAfter ctx storage))) none).balance
        ctx.locked = saveStakeDeficit ctx storage := by
    rw [husage, hbalance, hu, emptyAfter_balance]
    rfl
  have hobserve := Near.Boundary.observe_matches_stakeFailure (M := model gasBound) (ctx := ctx)
    (storage := storage) (issue := none) (receiptError := none) habort rfl rfl
    (by rw [hactualDeficit]; exact hdeficit) hlogs
  rw [hactualDeficit] at hobserve
  unfold Near.Boundary.execOn
  simp only [code]
  change Matches (model gasBound) ctx storage.toFinset
    (Near.Boundary.observe ctx storage
      (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) storage) _ _) _
  rw [hmethod, hrun]
  simp only [hreceipts, Near.Boundary.actionsIssue?, List.findSome?_nil]
  simp only [Near.checkVMReceipts, List.zipIdx_nil, List.forIn_nil, pure, Except.pure]
  exact hobserve

/-- All accepted VM-side save checks now match the model for the empty-base
slice, whether the final storage-stake check accepts or rejects the receipt. -/
theorem execOn_empty_matches_modelStep_allStake
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (storage : Storage) (st : Option Storage) (rest : Nat)
    (hwf : ctx.WF storage.toFinset)
    (hrepresented : (model gasBound).Represents storage.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) storage
        (emptyAfter ctx storage) (emptyCost ctx storage) rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx storage.toFinset (Near.Boundary.execOn code storage ctx)
      ((model gasBound).step ctx st ()) := by
  by_cases hz : saveStakeDeficit ctx storage = 0
  · exact execOn_empty_matches_modelStep gasBound ctx storage st rest hwf hrepresented hmethod hp hm
      hread hentries hselected hroom hz hcredits hproof
  · exact execOn_empty_matches_stakeFailure gasBound ctx storage st rest hwf hrepresented hmethod hp hm
      hread hentries hselected hroom hcredits hproof (Nat.pos_of_ne_zero hz)

end WNear.Skeleton
