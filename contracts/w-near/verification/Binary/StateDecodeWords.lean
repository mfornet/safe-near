import Binary.StateRead
import NearVM.MeteredWasmCall

/-! Exact deployed Borsh fixed-width word readers. -/
namespace WNear.Binary.StateDecodeWords
open Wasm Wasm.Near

def guard (width : UInt32) : Expr := [.local_get 2,.i32_const width,.i32_relop .ne,.br_if 0]
def low : Expr := [.local_get 0,.local_get 1,.load .i64 none {align:=0,offset:=0},.store .i64 none {align:=0,offset:=1}]
def high : Expr := [.local_get 0,.i32_const 9,.i32_binop .add,.local_get 1,.i32_const 8,.i32_binop .add,
  .load .i64 none {align:=0,offset:=0},.store .i64 none {align:=0,offset:=0}]
def setFlag (value : UInt32) : Expr := [.i32_const value,.local_set 3]
def status : Expr := [.local_get 0,.local_get 3,.store .i32 (some 8) {align:=0,offset:=0}]
def body (wide : Bool) : Expr := setFlag 1++[.block .empty
  (guard (if wide then 16 else 8)++low++(if wide then high else [])++setFlag 0)]++status
def function (wide : Bool) : Func := {type:=31,locals:=[.num .i32],body:=body wide,bodySize:=if wide then 55 else 39}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}
theorem function694 : wNearModule.funcs[646]?=some (function true) := by kernel_rfl
theorem function710 : wNearModule.funcs[662]?=some (function false) := by kernel_rfl
theorem module_signature : wNearModule.types[31]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out source width : UInt32) :
    activationGas op #[.i32 out,.i32 source,.i32 width,.i32 0]=10*op := by simp [activationGas]
end WNear.Binary.StateDecodeWords
