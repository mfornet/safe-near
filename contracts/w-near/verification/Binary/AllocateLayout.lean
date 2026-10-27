import Binary.InterfaceSet
import NearVM.MeteredWasmCall

/-! Exact deployed alignment-layout leaves and alignment-one wrappers. -/
namespace WNear.Binary.AllocateLayout
open Wasm Wasm.Near
set_option maxRecDepth 20000

def reserve : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 2,.global_set 0]
def guard : Expr := [.local_get 1,.load .i32 none {align := 2,offset := 4},.local_tee 3,
  .i32_unop .popcnt,.i32_const 1,.i32_relop .eq,.br_if 0]
def panic (message location previous : UInt32) : Expr := [.i32_const message,.i32_const 43,.local_get 2,
  .i32_const 8,.i32_binop .add,.i32_const location,.i32_const previous,.call 881,.unreachable]
def tail : Expr := [.local_get 1,.load .i32 none {align := 2,offset := 0},.local_set 1,
  .local_get 0,.local_get 3,.store .i32 none {align := 2,offset := 4},.local_get 0,.local_get 3,
  .local_get 1,.i32_binop .add,.i32_const 4294967295,.i32_binop .add,.i32_const 0,.local_get 3,
  .i32_binop .sub,.i32_binop .and,.store .i32 none {align := 2,offset := 0},
  .local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]
def body (message location previous : UInt32) : Expr := reserve ++ [.block .empty (guard ++ panic message location previous)] ++ tail
def function (message location previous : UInt32) : Func :=
  {type := 14,locals := [.num .i32,.num .i32],body := body message location previous,bodySize := 113}
def signature : FuncType := {params := [.num .i32,.num .i32],results := []}
def body751 := body 1065620 1065664 1065508
def function751 := function 1065620 1065664 1065508
def body684 := body 1063100 1063144 1063084
def function684 := function 1063100 1063144 1063084

def wrapperBody (callee : Nat) : Expr := reserve ++ [.local_get 2,.i32_const 1,.store .i32 none {align := 2,offset := 12},
  .local_get 2,.local_get 1,.store .i32 none {align := 2,offset := 8},.local_get 2,.local_get 2,
  .i32_const 8,.i32_binop .add,.call callee,.local_get 0,.local_get 2,.load .i64 none {align := 3,offset := 0},
  .store .i64 none {align := 3,offset := 0},.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]
def wrapper (callee : Nat) : Func := {type := 14,locals := [.num .i32],body := wrapperBody callee,bodySize := 69}
def function752 := wrapper 751
def function685 := wrapper 684

theorem body751_eq : f751.body = body751 := rfl
theorem body684_eq : f684.body = body684 := rfl
theorem body752_eq : f752.body = wrapperBody 751 := rfl
theorem body685_eq : f685.body = wrapperBody 684 := rfl
theorem module751 : wNearModule.funcs[703]? = some function751 := by kernel_rfl
theorem module752 : wNearModule.funcs[704]? = some function752 := by kernel_rfl
theorem module684 : wNearModule.funcs[636]? = some function684 := by kernel_rfl
theorem module685 : wNearModule.funcs[637]? = some function685 := by kernel_rfl
theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl
theorem guard_length : guard.length = 7 := rfl
theorem tail_length : tail.length = 21 := rfl
theorem wrapperBody_length (callee : Nat) : (wrapperBody callee).length = 24 := rfl
theorem leaf_activation (op : Nat) (out input : UInt32) : activationGas op #[.i32 out,.i32 input,.i32 0,.i32 0] = 10 * op := by simp [activationGas]
theorem wrapper_activation (op : Nat) (out size : UInt32) : activationGas op #[.i32 out,.i32 size,.i32 0] = 10 * op := by simp [activationGas]

end WNear.Binary.AllocateLayout
