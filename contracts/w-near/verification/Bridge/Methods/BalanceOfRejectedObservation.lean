import Bridge.Methods.FtBalanceOfCopiedRun
import Bridge.Functions.BalanceOf297RejectPanicTotal
import Bridge.Methods.RecordedFailure

namespace WNear.Binary.PanicTotal
open Wasm Wasm.Near NearLogic NearInterface ContractModel

/-- Exact erased host relation of the constructed two-branch panic path. -/
def rejectedPanicPost (bs : List UInt8) (h e : NearState) : Prop :=
  e = erase { h with lastError := some (expectedError h bs) }

/-- Receipt safety needs exact final failure fields while allowing actual input/storage reads to update registers. -/
def rejectedReceiptPost (bs : List UInt8) (h e : NearState) : Prop :=
  e.lastError = some (expectedError h bs) ∧ e.lastExecutionIssue = none

/-- The local trap's stronger erased-state relation supplies the receipt's exact error fields. -/
theorem rejectedPanicPost_receipt (bs : List UInt8) (h e : NearState)
    (he : rejectedPanicPost bs h e) (hi : h.lastExecutionIssue = none) :
    rejectedReceiptPost bs h e := by
  unfold rejectedPanicPost at he
  rw [he]
  exact ⟨rfl, hi⟩

/-- The actual panic-error choice composes to complete receipt rollback/no-issue once its full method run is supplied. -/
theorem rejected_receipt_no_issue (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (bs : List UInt8) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : RecordedFailure.RecordedFailureRun ctx.protocol i Pre cost (rejectedReceiptPost bs))
    (hpreP : Pre (eraseP (hostOf ctx raw))) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    RolledBack ctx raw r ∧ ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  apply RecordedFailure.method_boundary_no_issue size codeOf raw ctx Pre cost (rejectedReceiptPost bs)
    (expectedError (hostOf ctx raw) bs) hp hwf hname hexp hft h1 h2 hspec hpreP
  · intro e he
    obtain ⟨herr, hnone⟩ := he
    refine ⟨?_, hnone⟩
    exact herr.trans (congrArg some (expectedError_eraseP (hostOf ctx raw) bs))
  · exact expectedError_no_issue (hostOf ctx raw) bs

/-- Actual exported ft_balance_of receipt route, conditional on its exact complete rejected panic run. -/
theorem balance_rejected_receipt_no_issue (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (Pre : NearState → Prop) (cost : NearState → Nat)
    (bs : List UInt8) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hm : ctx.method = "ft_balance_of")
    (hspec : RecordedFailure.RecordedFailureRun ctx.protocol 297 Pre cost (rejectedReceiptPost bs))
    (hpreP : Pre (eraseP (hostOf ctx raw))) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    RolledBack ctx raw r ∧ ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  exact rejected_receipt_no_issue size codeOf raw ctx Pre cost bs hp hwf
    (by rw [hm]; decide) (by rw [hm]; exact BalanceOf297AbsentCall.export_297)
    BalanceOf297AbsentCall.funcType_297 (by decide) (by decide) hspec hpreP

end WNear.Binary.PanicTotal
