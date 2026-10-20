import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-! Terminal total-WP rules for the scoped outcome adapter. -/

namespace Wasm.SmallStep
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

theorem twp_outcome_done [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)}
    {values : List Value} :
    Φ (.done values) ⊢
      WP (Expr.done values : Expr α) @ s; E [{ Φ }] :=
  twp.value rfl

theorem twp_outcome_trapped [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)}
    {reason : TrapReason} :
    Φ (.trapped reason) ⊢
      WP (Expr.trapped reason : Expr α) @ s; E [{ Φ }] :=
  twp.value rfl

end Wasm.SmallStep
