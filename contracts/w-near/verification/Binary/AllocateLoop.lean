import Binary.AllocateSearch

/-! Exact control and candidate-preparation code of the deployed search580. -/
namespace WNear.Binary.AllocateSearch
open Wasm
set_option maxRecDepth 30000

def candidatePrepare : Expr := [.local_get 1,.load .i32 none {align:=2,offset:=8},.local_tee 9,
  .i32_const 1,.i32_binop .and,.br_if 0,.local_get 1,.i32_const 8,.i32_binop .add,.local_set 9]
def candidateUnits : Expr := [.local_get 0,.call 572,.local_set 10]
def candidateSize : Expr := [.local_get 1,.call 576,.local_get 10,.i32_relop .lt_u,.br_if 3]

theorem candidateOuter_eq : candidateOuter = [.block .empty candidateMiddle] ++ candidateOuter.drop 1 := by kernel_rfl
theorem candidateMiddle_eq : candidateMiddle = [.block .empty candidateInner] ++ candidateMiddle.drop 1 := by kernel_rfl
theorem candidateInner_eq : candidateInner = [.loop .empty candidateLoop] ++ candidateInner.drop 1 := by kernel_rfl
theorem candidateLoop_eq : candidateLoop = [.block .empty inspect] ++ candidateLoop.drop 1 := by kernel_rfl
theorem inspect_eq : inspect = candidatePrepare ++ candidateUnits ++ candidateSize ++ [.block .empty splitOuter] ++ inspect.drop 19 := by kernel_rfl

theorem splitOuter_eq : splitOuter = [.block .empty split1] ++ splitOuter.drop 1 := by kernel_rfl
theorem split1_eq : split1 = [.block .empty split2] ++ split1.drop 1 := by kernel_rfl
theorem split2_eq : split2 = [.block .empty split3] ++ split2.drop 1 := by kernel_rfl
theorem split3_eq : split3 = [.block .empty split4] ++ split3.drop 1 := by kernel_rfl
theorem split4_eq : split4 = [.block .empty splitBody] ++ split4.drop 1 := by kernel_rfl
end WNear.Binary.AllocateSearch
