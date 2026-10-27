import Binary.Module

/-! Actual table-selected U128 formatter adapters, before decimal conversion. -/
namespace WNear.Binary.SerializeFormatter
open Wasm
set_option maxRecDepth 20000

def boxPrefix : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_get 1]
def boxBody : Expr := boxPrefix ++ [.call 901]
def boxFunction : Func := {type := 13, locals := [], body := boxBody, bodySize := 15}
def u128Prefix : Expr := [.local_get 0, .load .i64 none {align := 3, offset := 0}, .local_get 0,
  .i32_const 8, .i32_binop .add, .load .i64 none {align := 3, offset := 0}, .i32_const 1, .local_get 1]
def u128Body : Expr := u128Prefix ++ [.call 902]
def u128Function : Func := {type := 13, locals := [], body := u128Body, bodySize := 25}
def signature : FuncType := {params := [.num .i32, .num .i32], results := [.num .i32]}

theorem box_module : wNearModule.funcs[305]? = some boxFunction := by kernel_rfl
theorem u128_module : wNearModule.funcs[853]? = some u128Function := by kernel_rfl
theorem module_signature : wNearModule.types[13]? = some signature := by kernel_rfl
/-- Element segment starts at table1; its92nd installed slot is global f353. -/
theorem table92 : (wNearModule.elems[0]!).init[91]? = some [.ref_func 353] := by kernel_rfl
end WNear.Binary.SerializeFormatter
