import Binary.Module
import NearVM.Run

/-! Exact deployed Some-state unwrap f155, its absent-state panic f156, and
its actual forty-byte copy dependency f951. No execution adequacy is assumed. -/
namespace WNear.Binary.UnwrapState
open Wasm Wasm.Near
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

def tagCheck : Expr := [.local_get 1, .load .i32 none {align := 2, offset := 24}, .br_if 0]
def panicTail : Expr := [.local_get 1, .call 156, .unreachable]
def body : Expr := [.block .empty (tagCheck ++ panicTail),
  .local_get 0, .local_get 1, .i32_const 40, .call 951, .drop]
def function : Func := {type := 14, locals := [], body, bodySize := 34}
def signature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem module_function : wNearModule.funcs[107]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl
theorem global_signature : wNearModule.funcType? 155 = some signature := by kernel_rfl

theorem body_length : body.length = 6 := rfl
theorem activation_cost (op : Nat) (out source : UInt32) :
    activationGas op #[.i32 out, .i32 source] = 9 * op := by simp [activationGas]

namespace Panic

def body : Expr := [.i32_const 1050868, .i32_const 31, .call 521, .unreachable]
def function : Func := {type := 0, locals := [], body, bodySize := 17}
def signature : FuncType := {params := [.num .i32], results := []}
theorem module_function : wNearModule.funcs[108]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[0]? = some signature := by kernel_rfl

end Panic

namespace Copy

def loopBody : Expr :=
  [.local_get 3, .local_get 1, .load .i32 (some ⟨8, false⟩) {align := 0, offset := 0},
   .store .i32 (some 8) {align := 0, offset := 0},
   .local_get 1, .i32_const 1, .i32_binop .add, .local_set 1,
   .local_get 3, .i32_const 1, .i32_binop .add, .local_set 3,
   .local_get 2, .i32_const 4294967295, .i32_binop .add, .local_tee 2, .br_if 0]

def body : Expr :=
  [.block .empty [.local_get 2, .i32_eqz, .br_if 0,
    .local_get 0, .local_set 3, .loop .empty loopBody], .local_get 0]
def function : Func := {type := 15, locals := [.num .i32], body, bodySize := 54}
def signature : FuncType := {params := [.num .i32, .num .i32, .num .i32], results := [.num .i32]}
theorem module_function : wNearModule.funcs[903]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[15]? = some signature := by kernel_rfl
theorem global_signature : wNearModule.funcType? 951 = some signature := by kernel_rfl
theorem loop_length : loopBody.length = 17 := rfl
theorem body_length : body.length = 2 := rfl
theorem activation_cost (op : Nat) (out source count : UInt32) :
    activationGas op #[.i32 out, .i32 source, .i32 count, .i32 0] = 10 * op := by simp [activationGas]

end Copy
end WNear.Binary.UnwrapState
