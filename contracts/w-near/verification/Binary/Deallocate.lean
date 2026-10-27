import Binary.Module
import NearVM.MeteredWasmCall

/-! Deployed deallocation entry f237 and its actual allocator implementation f582. -/
namespace WNear.Binary.Deallocate
open Wasm Wasm.Near

def entryBody : Expr := [.i32_const 1074896,.local_get 0,.local_get 1,.local_get 2,.call 582]
def entryFunction : Func := {type := 31,locals := [],body := entryBody,bodySize := 20}
def entrySignature : FuncType := {params := [.num .i32,.num .i32,.num .i32],results := []}

def guard : Expr := [.local_get 1,.i32_eqz,.br_if 0,.local_get 2,.i32_eqz,.br_if 0]
def alignCall : Expr := [.local_get 2,.call 570,.drop]
def saveHead : Expr := [.local_get 0,.load .i32 none {align := 2,offset := 0},.local_set 4]
def markFree : Expr := [.local_get 1,.i32_const 4294967288,.i32_binop .add,.local_tee 2,
  .local_get 2,.load .i32 none {align := 2,offset := 0},.i32_const 4294967294,.i32_binop .and,
  .store .i32 none {align := 2,offset := 0}]
def sizeCall : Expr := [.local_get 2,.call 576,.drop]
def zeroLink : Expr := [.local_get 1,.i32_const 0,.store .i32 none {align := 2,offset := 0}]
def previousGuard : Expr := [.local_get 1,.i32_const 4294967292,.i32_binop .add,
  .load .i32 none {align := 2,offset := 0},.i32_const 4294967292,.i32_binop .and,.local_tee 5,
  .i32_eqz,.br_if 0,.local_get 5,.load .i32 (some {bits := 8,signed := false}) {align := 0,offset := 0},
  .i32_const 1,.i32_binop .and,.i32_eqz,.br_if 1]
def nextGuard : Expr := [.local_get 2,.load .i32 none {align := 2,offset := 0},.local_tee 5,
  .i32_const 4294967292,.i32_binop .and,.local_tee 6,.i32_eqz,.br_if 1,
  .i32_const 0,.local_get 6,.local_get 5,.i32_const 2,.i32_binop .and,.select none,
  .local_tee 5,.i32_eqz,.br_if 1,.local_get 5,
  .load .i32 (some {bits := 8,signed := false}) {align := 0,offset := 0},.i32_const 1,.i32_binop .and,.br_if 1]
def linkNext : Expr := [.local_get 1,.local_get 5,.load .i32 none {align := 2,offset := 8},
  .i32_const 4294967292,.i32_binop .and,.store .i32 none {align := 2,offset := 0},
  .local_get 5,.local_get 2,.i32_const 1,.i32_binop .or,.store .i32 none {align := 2,offset := 8},
  .local_get 4,.local_set 2,.br 2]
def propagateFlag : Expr := [.local_get 2,.load .i32 (some {bits := 8,signed := false}) {align := 0,offset := 0},
  .i32_const 2,.i32_binop .and,.i32_eqz,.br_if 0,
  .local_get 5,.local_get 5,.load .i32 none {align := 2,offset := 0},.i32_const 2,.i32_binop .or,
  .store .i32 none {align := 2,offset := 0}]
def mergePrevious : Expr := [.local_get 2,.call 575,.block .empty propagateFlag,
  .local_get 5,.call 576,.drop,.local_get 4,.local_set 2,.br 1]
def insertHead : Expr := [.local_get 1,.local_get 4,.store .i32 none {align := 2,offset := 0}]
def installHead : Expr := [.local_get 0,.local_get 2,.store .i32 none {align := 2,offset := 0}]
def inspectNeighbors : Expr := [.block .empty ([.block .empty ([.block .empty
  ([.block .empty previousGuard] ++ nextGuard ++ linkNext)] ++ mergePrevious)] ++ insertHead)]
def coreBody : Expr := [.block .empty (guard ++ alignCall ++ saveHead ++ markFree ++ sizeCall ++ zeroLink ++ inspectNeighbors ++ installHead)]
def coreFunction : Func := {type := 45,locals := [.num .i32,.num .i32,.num .i32],body := coreBody,bodySize := 239}
def coreSignature : FuncType := {params := [.num .i32,.num .i32,.num .i32,.num .i32],results := []}

theorem entry_function : wNearModule.funcs[189]? = some entryFunction := by kernel_rfl
theorem entry_signature : wNearModule.types[31]? = some entrySignature := by kernel_rfl
theorem core_function : wNearModule.funcs[534]? = some coreFunction := by kernel_rfl
theorem core_signature : wNearModule.types[45]? = some coreSignature := by kernel_rfl

theorem entry_activation (op : Nat) (pointer length align : UInt32) :
    activationGas op #[.i32 pointer,.i32 length,.i32 align] = 10 * op := by simp [activationGas]
theorem core_activation (op : Nat) (allocator pointer length align : UInt32) :
    activationGas op #[.i32 allocator,.i32 pointer,.i32 length,.i32 align,.i32 0,.i32 0,.i32 0] = 12 * op := by simp [activationGas]

end WNear.Binary.Deallocate
