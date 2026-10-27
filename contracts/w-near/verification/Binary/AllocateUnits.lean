import Binary.Module
import NearVM.Run

/-! Actual checked allocation word-to-byte and minimum-size helpers. -/
namespace WNear.Binary.AllocateUnits
open Wasm Wasm.Near
set_option maxRecDepth 10000

def unitsPanic : Expr := [.i32_const 1057216,.i32_const 33,.i32_const 1057252,.call 853,.unreachable]
def unitsGuard : Expr := [.local_get 0,.i32_const 1073741823,.i32_binop .and,.local_get 0,.i32_relop .eq,.br_if 0]
def unitsTail : Expr := [.local_get 0,.i32_const 2,.i32_binop .shl]
def unitsBody : Expr := [.block .empty (unitsGuard ++ unitsPanic)] ++ unitsTail
def unitsFunction : Func := {type := 32,locals := [],body := unitsBody,bodySize := 45}
def unitsSignature : FuncType := {params := [.num .i32],results := [.num .i32]}

def minimumGuard : Expr := [.local_get 0,.i32_const 4294967288,.i32_binop .add,.local_get 0,.i32_relop .gt_u,.br_if 0,.return]
def minimumPanic : Expr := [.i32_const 1057152,.i32_const 33,.i32_const 1057268,.call 853,.unreachable]
def minimumBody : Expr := [.block .empty minimumGuard] ++ minimumPanic
def minimumFunction : Func := {type := 0,locals := [],body := minimumBody,bodySize := 37}
def minimumSignature : FuncType := {params := [.num .i32],results := []}

def quantumFunction : Func := {type := 13,locals := [],body := [.i32_const 16],bodySize := 4}
def quantumSignature : FuncType := {params := [.num .i32,.num .i32],results := [.num .i32]}

theorem units_function : wNearModule.funcs[524]? = some unitsFunction := by kernel_rfl
theorem units_signature : wNearModule.types[32]? = some unitsSignature := by kernel_rfl
theorem minimum_function : wNearModule.funcs[526]? = some minimumFunction := by kernel_rfl
theorem minimum_signature : wNearModule.types[0]? = some minimumSignature := by kernel_rfl
theorem quantum_function : wNearModule.funcs[530]? = some quantumFunction := by kernel_rfl
theorem quantum_signature : wNearModule.types[13]? = some quantumSignature := by kernel_rfl
end WNear.Binary.AllocateUnits
