import Binary.StateRead
import NearVM.MeteredWasmCall

/-! Exact deployed Borsh slice split helpers, including their rejected panic paths. -/
namespace WNear.Binary.StateDecodeSlices
open Wasm Wasm.Near

def guard : Expr := [.local_get 2,.local_get 3,.i32_relop .ge_u,.br_if 0]
def panic (callee : Nat) : Expr := [.local_get 3,.local_get 2,.local_get 4,.call callee,.unreachable]
def dropWrites : Expr := [.local_get 0,.local_get 2,.local_get 3,.i32_binop .sub,.store .i32 none {align:=2,offset:=4},
  .local_get 0,.local_get 1,.local_get 3,.i32_binop .add,.store .i32 none {align:=2,offset:=0}]
def takeWrites : Expr := [.local_get 0,.local_get 3,.store .i32 none {align:=2,offset:=4},
  .local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=0}]
def body (drop : Bool) : Expr :=
  [.block .empty (guard++panic (if drop then 868 else 855))]++(if drop then dropWrites else takeWrites)
def function (drop : Bool) : Func := {type:=39,locals:=[],body:=body drop,bodySize:=if drop then 45 else 39}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32,.num .i32,.num .i32],results:=[]}
def index (drop : Bool) : Nat := if drop then 361 else 362
def bodyCost (drop : Bool) : Nat := if drop then 14 else 10
def bodySteps (drop : Bool) : Nat := bodyCost drop+1

theorem drop_function : wNearModule.funcs[313]?=some (function true) := by kernel_rfl
theorem take_function : wNearModule.funcs[314]?=some (function false) := by kernel_rfl
theorem module_type : wNearModule.types[39]?=some signature := by kernel_rfl
theorem activation (drop : Bool) (op : Nat) (out pointer len split location : UInt32) :
    activationGas op (MeteredLogic.wasmLocals (function drop) [.i32 out,.i32 pointer,.i32 len,.i32 split,.i32 location])=11*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function]
end WNear.Binary.StateDecodeSlices
