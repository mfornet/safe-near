import Skeleton.FundedEmpty
import Skeleton.StartupSimulation
import NearRuntime.BudgetObservation

/-! Checked observations of the actual funded reference, with original
VMContext and explicit protocol arithmetic room. -/
namespace WNear.Skeleton.FundedObservation
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation FundedEmpty
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- Once storage has committed its host and memory, the suffix is independent
of the initial counter. Only the original input is used to select the return. -/
theorem final_eq (ctx : Context) (raw : Storage) (host : NearState)
    (storage : HostStore NearState) (hinput : host.context.input = ctx.args) :
    (successResults ctx.protocol (bodyStore ctx host) storage).finalStore ctx.protocol.wasm (bodyStore ctx host) =
      executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw storage := by
  have hb : successReturnBefore ctx.protocol (bodyStore ctx host) storage =
      successReturnBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) storage := by
    unfold successReturnBefore successLogBefore successStorageBefore successInputBefore successInputAfter
      successLogAfter bodyStore executionStore
    rfl
  simp only [HostResults.finalStore, successResults_beforeReturn, successResults_returned,
    executionFinal, hb]
  have hi : (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw).host.context.input = ctx.args :=
    executionActive_input _ _ _
  simp only [bodyStore, initialized_host, hinput, hi]

/-- Original raw representation is retained at arbitrary framed storage entry. -/
theorem before_represents (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset) :
    StorageRepresentation.Represents (FundedEmpty.before ctx host).host raw.toFinset := by
  have hb := (before_resources ctx raw host hhost).1.fields
  have hr := StorageRepresentation.toNearState_represents ctx.protocol (Near.Boundary.toVMContext ctx)
    raw raw.toFinset rfl hwf.raw_keys_unique
  have hk := congrArg NearState.storageKeys hb
  change (FundedEmpty.before ctx host).host.storageKeys = (origin ctx raw).storageKeys at hk
  constructor
  · intro key value
    rw [hb.storage]
    exact hr.lookup key value
  · intro key value hm
    rw [hk]
    exact hr.coverage key value hm

private theorem finished_rep (extra : Nat) (b : HostStore NearState)
    (raw : RawStorage) (h : StorageRepresentation.Represents b.host raw) (key value : Near.Bytes) :
    let p := (applyCharges (written b key value).host (postCharges b key)).1
    StorageRepresentation.Represents (finished extra b 1 0 u64Max 0 key value p).host (rawWrite raw key value) := by
  have hp := ((h.setStorage key value).invalidateIterators).applyCharges
    (postCharges b key) (postCharges_burnsOnly b key)
  exact hp.updateStorageUsage extra "storage_write" b b.mem (args 1 0 u64Max 0)

/-- The actual computed storage post-state represents the model write. -/
theorem after_represents (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset) :
    StorageRepresentation.Represents (FundedEmpty.after ctx host).host (savedStorage raw ctx.args).toFinset := by
  have hp := (before_represents ctx raw host hhost hwf).applyCharges (preCharges ctx host)
    (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0)
  rw [show (applyCharges (FundedEmpty.before ctx host).host (preCharges ctx host)).1 = paid ctx host
    by unfold paid; rfl] at hp
  have hpre := hp.paidStore (FundedEmpty.before ctx host)
  have hphase := hpre.prepared (Output.paidStore (FundedEmpty.before ctx host) (paid ctx host))
    (applyCharges (accounted (Output.paidStore (FundedEmpty.before ctx host) (paid ctx host)) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    (ctx.trie.set (Near.TrieOverlay.contractKey (paid ctx host).context.currentAccountId "k".toUTF8.toList) ctx.args)
  have hf := finished_rep ctx.protocol.fees.numExtraBytesRecord _ raw.toFinset hphase "k".toUTF8.toList ctx.args
  rw [show (savedStorage raw ctx.args).toFinset = rawWrite raw.toFinset "k".toUTF8.toList ctx.args
    from rawWrite_toFinset raw _ _]
  simpa only [FundedEmpty.after, FundedEmpty.phase] using hf

end WNear.Skeleton.FundedObservation
