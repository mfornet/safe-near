import Skeleton.FinalState
import Skeleton.Model
import NearRuntime.Refinement

/-!
# Success observation from local storage postconditions

The output suffix supplies the returned input and fixed log. Representation,
accounting and stake premises refer only to the local storage post-state;
no method-execution or observation equation is assumed.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near NearInterface

/-- The exact normal VM fields discharge the boundary's success contract. -/
theorem executionOutcome_successPost
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw state : Storage) (storage : HostStore NearState)
    (hrep : StorageRepresentation.Represents storage.host (savedStorage state ctx.args).toFinset)
    (hpromises : storage.host.promises = []) (hlogs : storage.host.logs = [])
    (hbalance : storage.host.context.accountBalance = ctx.balance + ctx.attached)
    (husage : storage.host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage state ctx.args).toFinset)
    (hstake : stakeDeficit ctx.protocol storage.host.context.storageUsage.toNat
      storage.host.context.accountBalance ctx.locked = 0) :
    Near.Boundary.SuccessPost (model gasBound) ctx raw.toFinset
      (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw storage)) none)
      none none { state := savedStorage state ctx.args, ret := ctx.args, logs := ["saved"], promises := [] } := by
  obtain ⟨ha, hr, hs, hu, hb, hl, hrec, _⟩ := executionOutcome_fields ctx.protocol
    (Near.Boundary.toVMContext ctx) raw storage _ hrep hpromises hlogs
  refine ⟨ha, rfl, rfl, ?_, hr, hs, ?_, hu.trans husage, hl, ?_⟩
  · simpa only [hu, hb] using hstake
  · simpa only [model, receiptDeposits, List.map_nil, List.sum_nil, Nat.sub_zero] using hb.trans hbalance
  · simpa only [model] using hrec

/-- Once local storage accounting is known, observing the normally terminated
machine matches the independent model's successful result. -/
theorem executionOutcome_matches_success
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw state : Storage) (storage : HostStore NearState)
    (hrep : StorageRepresentation.Represents storage.host (savedStorage state ctx.args).toFinset)
    (hpromises : storage.host.promises = []) (hlogs : storage.host.logs = [])
    (hbalance : storage.host.context.accountBalance = ctx.balance + ctx.attached)
    (husage : storage.host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage state ctx.args).toFinset)
    (hstake : stakeDeficit ctx.protocol storage.host.context.storageUsage.toNat
      storage.host.context.accountBalance ctx.locked = 0) :
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observe ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
          (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw storage)) none)
        none none)
      (.ok { state := savedStorage state ctx.args, ret := ctx.args, logs := ["saved"], promises := [] }) :=
  Near.Boundary.observe_matches_success (executionOutcome_successPost gasBound ctx raw state
    storage hrep hpromises hlogs hbalance husage hstake)

end WNear.Skeleton
