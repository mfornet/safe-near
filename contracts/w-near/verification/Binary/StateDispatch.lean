import Binary.StateRead

/-! Actual SDK dispatch and accepted i64 result-unwrapping function metadata. -/
namespace WNear.Binary.StateDispatch
open Wasm Wasm.Near

def returnPrefix : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 2,.global_set 0]
def returnGuard : Expr := [.local_get 0,.cvt .i32_wrap_i64,.i32_eqz,.br_if 0]
def returnPanic : Expr := [.i32_const 1054165,.i32_const 70,.local_get 2,.i32_const 8,.i32_binop .add,
  .i32_const 1054900,.i32_const 1054316,.call 881,.unreachable]
def returnSuffix : Expr := [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 1]
def returnBody : Expr := returnPrefix ++ [.block .empty (returnGuard ++ returnPanic)] ++ returnSuffix
def returnFunction : Func := {type := 24,locals := [.num .i32],body := returnBody,bodySize := 76}
def returnSignature : FuncType := {params := [.num .i64,.num .i64],results := [.num .i64]}

noncomputable def storageFunction : Func := WNear.Binary.f459
noncomputable def lengthFunction : Func := WNear.Binary.f440
noncomputable def readFunction : Func := WNear.Binary.f435

def storageSignature : FuncType := {params := [.num .i32,.num .i32],results := [.num .i64]}
def lengthSignature : FuncType := storageSignature
def readSignature : FuncType := {params := [.num .i32,.num .i32,.num .i32],results := []}

theorem return_function : wNearModule.funcs[384]? = some returnFunction := by kernel_rfl
theorem return_signature : wNearModule.types[24]? = some returnSignature := by kernel_rfl
theorem storage_function : wNearModule.funcs[411]? = some storageFunction := by kernel_rfl
theorem length_function : wNearModule.funcs[392]? = some lengthFunction := by kernel_rfl
theorem read_function : wNearModule.funcs[387]? = some readFunction := by kernel_rfl
theorem storage_signature : wNearModule.types[30]? = some storageSignature := by kernel_rfl
theorem length_signature : wNearModule.types[30]? = some lengthSignature := by kernel_rfl
theorem read_signature : wNearModule.types[31]? = some readSignature := by kernel_rfl

theorem return_activation (op : Nat) (status value : UInt64) :
    activationGas op #[.i64 status,.i64 value,.i32 0] = 11 * op := by simp [activationGas]
end WNear.Binary.StateDispatch
