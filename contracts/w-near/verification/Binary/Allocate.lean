import Binary.Module
import NearVM.MeteredWasmCall

/-! Actual malloc wrapper f581 and the allocation commit suffix of f580.
The free-list search and the memory-growth branch remain separate obligations. -/
namespace WNear.Binary.Allocate
open Wasm Wasm.Near

def alignAndSave : Expr := [.local_get 1,.call 570,.local_set 4,.local_get 3,.local_get 0,
  .load .i32 none {align := 2,offset := 0},.store .i32 none {align := 2,offset := 12}]
def attempt : Expr := [.local_get 4,.local_get 2,.local_get 3,.i32_const 12,.i32_binop .add,
  .i32_const 1057464,.i32_const 1057464,.call 580]
def retry : Expr := [.local_get 3,.i32_const 1057464,.local_get 4,.local_get 2,.call 577,
  .i32_const 0,.local_set 1,.local_get 3,.load .i32 none {align := 2,offset := 0},.br_if 0,
  .local_get 3,.load .i32 none {align := 2,offset := 4},.local_tee 1,.local_get 3,
  .load .i32 none {align := 2,offset := 12},.store .i32 none {align := 2,offset := 8},
  .local_get 3,.local_get 1,.store .i32 none {align := 2,offset := 12}] ++ attempt ++ [.local_set 1]
def body : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 3,.global_set 0,
  .block .empty ([.block .empty [.local_get 1,.br_if 0,.local_get 2,.local_set 1,.br 1]] ++
    alignAndSave ++ [.block .empty (attempt ++ [.local_tee 1,.br_if 0] ++ retry),
      .local_get 0,.local_get 3,.load .i32 none {align := 2,offset := 12},.store .i32 none {align := 2,offset := 0}]),
  .local_get 3,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 1]
def function : Func := {type := 15,locals := [.num .i32,.num .i32],body,bodySize := 194}
def signature : FuncType := {params := [.num .i32,.num .i32,.num .i32],results := [.num .i32]}

def markAllocated : Expr := [.local_get 9,.local_get 9,.load .i32 none {align := 2,offset := 0},
  .i32_const 1,.i32_binop .or,.store .i32 none {align := 2,offset := 0}]
def resultPointer : Expr := [.local_get 9,.i32_const 8,.i32_binop .add,.local_set 5]
def commit : Expr := markAllocated ++ resultPointer
private def blockBody : Instr → Expr | .block _ code => code | _ => []

noncomputable def searchFunction : Func := wNearModule.funcs[532]!
/-- The actual final ten instructions in the successful search block. -/
theorem search_commit : (blockBody searchFunction.body[16]!).drop 1 = commit := by kernel_rfl

theorem module_signature : wNearModule.types[15]? = some signature := by kernel_rfl
-- The size is checked separately so the instruction decomposition is independently visible.
theorem module_function : wNearModule.funcs[533]? = some function := by kernel_rfl

theorem module_body : (wNearModule.funcs[533]!).body = body := by kernel_rfl

theorem activation (op : Nat) (allocator size alignment : UInt32) :
    activationGas op #[.i32 allocator,.i32 size,.i32 alignment,.i32 0,.i32 0] = 11 * op := by simp [activationGas]
end WNear.Binary.Allocate
