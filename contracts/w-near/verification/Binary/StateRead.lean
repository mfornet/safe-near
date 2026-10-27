import Binary.Module
import NearVM.Run

/-! Actual state-read entry and SDK storage/register functions. -/
namespace WNear.Binary.StateRead
open Wasm Wasm.Near
set_option maxRecDepth 10000

def resultPanic : Expr := [.local_get 2,.local_get 3,.local_get 4,.call 879,.unreachable]
def resultGuard : Expr := [.local_get 1,.load .i32 none {align := 2,offset := 0},.br_if 0]
def resultLow : Expr := [.local_get 0,.local_get 1,.load .i64 none {align := 2,offset := 0},.store .i64 none {align := 2,offset := 0}]
def resultHigh : Expr := [.local_get 0,.i32_const 8,.i32_binop .add,.local_get 1,.i32_const 8,.i32_binop .add,
  .load .i32 none {align := 2,offset := 0},.store .i32 none {align := 2,offset := 0}]
def resultBody : Expr := [.block .empty (resultGuard ++ resultPanic)] ++ resultLow ++ resultHigh
def resultFunction : Func := {type := 39,locals := [],body := resultBody,bodySize := 51}
def resultSignature : FuncType := {params := [.num .i32,.num .i32,.num .i32,.num .i32,.num .i32],results := []}

noncomputable def stateFunction : Func := WNear.Binary.f219
def stateSignature : FuncType := {params := [.num .i32],results := []}
noncomputable def storageFunction : Func := WNear.Binary.f548
def storageSignature : FuncType := {params := [.num .i32,.num .i32,.num .i32],results := []}
noncomputable def dispatchFunction : Func := WNear.Binary.f459
def dispatchSignature : FuncType := {params := [.num .i32,.num .i32],results := [.num .i64]}
noncomputable def registerFunction : Func := WNear.Binary.f523
def registerSignature : FuncType := {params := [.num .i32,.num .i64],results := []}

def storageForwardBody : Expr := [.local_get 1,.local_get 2,.local_get 3,.call 43]
def storageForwardFunction : Func := {type := 6,locals := [],body := storageForwardBody,bodySize := 14}
def storageForwardSignature : FuncType := {params := [.num .i32,.num .i64,.num .i64,.num .i64],results := [.num .i64]}
def registerForwardBody : Expr := [.local_get 1,.local_get 2,.call 0]
def registerForwardFunction : Func := {type := 4,locals := [],body := registerForwardBody,bodySize := 12}
def registerForwardSignature : FuncType := {params := [.num .i32,.num .i64,.num .i64],results := []}
def lengthForwardBody : Expr := [.local_get 1,.call 1]
def lengthForwardFunction : Func := {type := 7,locals := [],body := lengthForwardBody,bodySize := 10}
def lengthForwardSignature : FuncType := {params := [.num .i32,.num .i64],results := [.num .i64]}

theorem result_function : wNearModule.funcs[450]? = some resultFunction := by kernel_rfl
theorem result_signature : wNearModule.types[39]? = some resultSignature := by kernel_rfl
theorem state_function : wNearModule.funcs[171]? = some stateFunction := by kernel_rfl
theorem state_signature : wNearModule.types[0]? = some stateSignature := by kernel_rfl
theorem storage_function : wNearModule.funcs[500]? = some storageFunction := by kernel_rfl
theorem storage_signature : wNearModule.types[31]? = some storageSignature := by kernel_rfl
theorem dispatch_function : wNearModule.funcs[411]? = some dispatchFunction := by kernel_rfl
theorem dispatch_signature : wNearModule.types[30]? = some dispatchSignature := by kernel_rfl
theorem register_function : wNearModule.funcs[475]? = some registerFunction := by kernel_rfl
theorem register_signature : wNearModule.types[5]? = some registerSignature := by kernel_rfl
theorem storage_forward_function : wNearModule.funcs[236]? = some storageForwardFunction := by kernel_rfl
theorem storage_forward_signature : wNearModule.types[6]? = some storageForwardSignature := by kernel_rfl
theorem register_forward_function : wNearModule.funcs[192]? = some registerForwardFunction := by kernel_rfl
theorem register_forward_signature : wNearModule.types[4]? = some registerForwardSignature := by kernel_rfl
theorem length_forward_function : wNearModule.funcs[193]? = some lengthForwardFunction := by kernel_rfl
theorem length_forward_signature : wNearModule.types[7]? = some lengthForwardSignature := by kernel_rfl

theorem state_key : (List.range 5).map (fun i => wNearSource.read (159306 + 1212 + i)) = [83,84,65,84,69] := by kernel_rfl

theorem result_activation (op : Nat) (out source message length location : UInt32) :
    activationGas op #[.i32 out,.i32 source,.i32 message,.i32 length,.i32 location] = 11 * op := by simp [activationGas]

end WNear.Binary.StateRead
