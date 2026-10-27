import Binary.Allocate

/-! Exact code organization for the deployed positive free-list search580. -/
namespace WNear.Binary.AllocateSearch
open Wasm
set_option maxRecDepth 30000

def children : Instr → Expr | .block _ body | .loop _ body => body | _ => []
def atPath : List Nat → Expr → Expr | [],code=>code | index::rest,code=>atPath rest (children code[index]!)
noncomputable def outer := atPath [16] Allocate.searchFunction.body
noncomputable def exhausted := atPath [16,0] Allocate.searchFunction.body
noncomputable def scan := atPath [16,0,0] Allocate.searchFunction.body
noncomputable def candidateOuter := atPath [16,0,0,3] Allocate.searchFunction.body
noncomputable def candidateMiddle := atPath [16,0,0,3,0] Allocate.searchFunction.body
noncomputable def candidateInner := atPath [16,0,0,3,0,0] Allocate.searchFunction.body
noncomputable def candidateLoop := atPath [16,0,0,3,0,0,0] Allocate.searchFunction.body
noncomputable def inspect := atPath [16,0,0,3,0,0,0,0] Allocate.searchFunction.body
noncomputable def splitOuter := atPath [16,0,0,3,0,0,0,0,18] Allocate.searchFunction.body
noncomputable def split1 := atPath [16,0,0,3,0,0,0,0,18,0] Allocate.searchFunction.body
noncomputable def split2 := atPath [16,0,0,3,0,0,0,0,18,0,0] Allocate.searchFunction.body
noncomputable def split3 := atPath [16,0,0,3,0,0,0,0,18,0,0,0] Allocate.searchFunction.body
noncomputable def split4 := atPath [16,0,0,3,0,0,0,0,18,0,0,0,0] Allocate.searchFunction.body
noncomputable def splitBody := atPath [16,0,0,3,0,0,0,0,18,0,0,0,0,0] Allocate.searchFunction.body

def initialCode : Expr := [.i32_const 0,.local_set 5,.i32_const 0,.local_get 1,.i32_binop .sub,.local_set 6,
  .local_get 1,.i32_const 4294967295,.i32_binop .add,.local_tee 7,.local_get 1,.i32_relop .gt_u,
  .local_set 8,.local_get 2,.load .i32 none {align:=2,offset:=0},.local_set 1]
def signature : FuncType := {params := [.num .i32,.num .i32,.num .i32,.num .i32,.num .i32],results := [.num .i32]}

theorem function_signature : WNear.Binary.wNearModule.types[34]? = some signature := by kernel_rfl
theorem function_body : Allocate.searchFunction.body = initialCode ++ [.block .empty outer,.local_get 5] := by kernel_rfl
theorem outer_eq : outer = [.block .empty exhausted] ++ Allocate.commit := by kernel_rfl
theorem exhausted_eq : exhausted = [.loop .empty scan] ++ exhausted.drop 1 := by kernel_rfl
theorem scan_eq : scan = [.local_get 1,.i32_eqz,.br_if 2,.block .empty candidateOuter] := by kernel_rfl
end WNear.Binary.AllocateSearch
