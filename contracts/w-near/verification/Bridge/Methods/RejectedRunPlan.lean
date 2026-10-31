import Bridge.Methods.BalanceOfRejectedObservation

namespace WNear.Binary.PanicTotal
open Wasm Wasm.Near NearLogic NearInterface

/-- Exact method-run frontier: finite cost chosen before gas, actual function 297, selected panic error and reachable relaxed host. -/
def RejectedRunPlan (raw : RawStorage) (ctx : Context) : Prop :=
  ∃ (Pre : NearState → Prop) (cost : NearState → Nat) (bs : List UInt8),
    RecordedFailure.RecordedFailureRun ctx.protocol 297 Pre cost (rejectedReceiptPost bs) ∧
      Pre (eraseP (hostOf ctx raw))

/-- Checked receipt composition from a complete rejected method plan. -/
theorem rejected_receipt_of_plan (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (plan : RejectedRunPlan raw ctx) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    RolledBack ctx raw r ∧ ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  obtain ⟨Pre, cost, bs, hrun, hpre⟩ := plan
  exact balance_rejected_receipt_no_issue size codeOf raw ctx Pre cost bs hp hwf hm hrun hpre

end WNear.Binary.PanicTotal
