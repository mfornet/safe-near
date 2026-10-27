import Binary.InterfaceSet

/-! Exact deployed deallocation header-size and unlink helpers. -/
namespace WNear.Binary.DeallocateList
open Wasm Wasm.Near
set_option maxRecDepth 20000

def sizePrefix : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 4294967292,
  .i32_binop .and, .local_tee 1, .local_get 0, .i32_binop .sub, .i32_const 4294967288,
  .i32_binop .add, .local_tee 0, .local_get 1, .i32_relop .gt_u, .br_if 0, .local_get 0, .return]
def sizePanic : Expr := [.i32_const 1057152, .i32_const 33, .i32_const 1057368, .call 853, .unreachable]
def sizeBody : Expr := [.block .empty sizePrefix] ++ sizePanic
def sizeFunction : Func := {type := 32, locals := [.num .i32], body := sizeBody, bodySize := 54}
def sizeSignature : FuncType := {params := [.num .i32], results := [.num .i32]}

def previous : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_tee 1,
  .i32_const 4294967292, .i32_binop .and, .local_tee 2, .i32_eqz, .br_if 0,
  .i32_const 0, .local_get 2, .local_get 1, .i32_const 2, .i32_binop .and, .select none,
  .local_tee 1, .i32_eqz, .br_if 0, .local_get 1, .local_get 1,
  .load .i32 none {align := 2, offset := 4}, .i32_const 3, .i32_binop .and,
  .local_get 0, .load .i32 none {align := 2, offset := 4}, .i32_const 4294967292,
  .i32_binop .and, .i32_binop .or, .store .i32 none {align := 2, offset := 4}]
def next : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 4}, .local_tee 1,
  .i32_const 4294967292, .i32_binop .and, .local_tee 2, .i32_eqz, .br_if 0,
  .local_get 2, .local_get 2, .load .i32 none {align := 2, offset := 0}, .i32_const 3,
  .i32_binop .and, .local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 4294967292,
  .i32_binop .and, .i32_binop .or, .store .i32 none {align := 2, offset := 0},
  .local_get 0, .load .i32 none {align := 2, offset := 4}, .local_set 1]
def clear : Expr := [.local_get 0, .local_get 1, .i32_const 3, .i32_binop .and,
  .store .i32 none {align := 2, offset := 4}, .local_get 0, .local_get 0,
  .load .i32 none {align := 2, offset := 0}, .i32_const 3, .i32_binop .and,
  .store .i32 none {align := 2, offset := 0}]
def unlinkBody : Expr := [.block .empty previous, .block .empty next] ++ clear
def unlinkFunction : Func := {type := 0, locals := [.num .i32, .num .i32], body := unlinkBody, bodySize := 129}
def unlinkSignature : FuncType := {params := [.num .i32], results := []}

theorem size_body_eq : f576.body = sizeBody := rfl
theorem unlink_body_eq : f575.body = unlinkBody := rfl
theorem module_size : wNearModule.funcs[528]? = some sizeFunction := by kernel_rfl
theorem module_unlink : wNearModule.funcs[527]? = some unlinkFunction := by kernel_rfl
theorem module_sizeSignature : wNearModule.types[32]? = some sizeSignature := by kernel_rfl
theorem module_unlinkSignature : wNearModule.types[0]? = some unlinkSignature := by kernel_rfl
theorem sizePrefix_length : sizePrefix.length = 15 := rfl
theorem previous_length : previous.length = 28 := rfl
theorem next_length : next.length = 22 := rfl
theorem clear_length : clear.length = 11 := rfl

theorem size_activation (op : Nat) (pointer : UInt32) : activationGas op #[.i32 pointer, .i32 0] = 9 * op := by simp [activationGas]
theorem unlink_activation (op : Nat) (pointer : UInt32) : activationGas op #[.i32 pointer, .i32 0, .i32 0] = 10 * op := by simp [activationGas]

end WNear.Binary.DeallocateList
