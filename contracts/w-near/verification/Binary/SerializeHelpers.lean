import Binary.VectorDrop

/-! Actual small callees on the deployed f96 serialization path. -/
namespace WNear.Binary.SerializeHelpers
open Wasm
set_option maxRecDepth 20000

def pairBody : Expr := [.local_get 0, .local_get 2, .store .i32 none {align := 2, offset := 4},
  .local_get 0, .local_get 1, .store .i32 none {align := 2, offset := 0}]
def pairFunction : Func := {type := 31, locals := [], body := pairBody, bodySize := 16}
def pairSignature : FuncType := {params := [.num .i32, .num .i32, .num .i32], results := []}
def panic : Expr := [.i32_const 1051844, .i32_const 55, .local_get 1, .i32_const 8,
  .i32_binop .add, .i32_const 1052036, .i32_const 1051976, .call 881, .unreachable]
def checkBody : Expr := [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 1, .global_set 0,
  .block .empty ([.local_get 0, .i32_eqz, .br_if 0] ++ panic),
  .local_get 1, .i32_const 16, .i32_binop .add, .global_set 0]
def checkFunction : Func := {type := 0, locals := [.num .i32], body := checkBody, bodySize := 72}
def checkSignature : FuncType := {params := [.num .i32], results := []}

theorem pair_module : wNearModule.funcs[424]? = some pairFunction := by kernel_rfl
theorem pair_signature : wNearModule.types[31]? = some pairSignature := by kernel_rfl
theorem check_module : wNearModule.funcs[317]? = some checkFunction := by kernel_rfl
theorem check_signature : wNearModule.types[0]? = some checkSignature := by kernel_rfl
/-- f321 has precisely the same function descriptor as f68. -/
theorem drop_module : wNearModule.funcs[273]? = some VectorDrop.function68 := by kernel_rfl
end WNear.Binary.SerializeHelpers
