import Binary.AllocateLayout
import Binary.AllocateRawForward

/-! Exact deployed nonzeroing vector record wrappers f767/f769/f770. -/
namespace WNear.Binary.StateDecodeRaw
open Wasm Wasm.Near

def setup (slot : Nat) (amount : UInt32) : Expr :=
  [.global_get 0,.i32_const amount,.i32_binop .sub,.local_tee slot,.global_set 0]
def restore (slot : Nat) (amount : UInt32) : Expr :=
  [.local_get slot,.i32_const amount,.i32_binop .add,.global_set 0]
def layoutArguments : Expr := [.local_get 3,.i32_const 24,.i32_binop .add,.local_get 1,.call 752]
def alignmentGuard : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=28},.local_tee 1,.i32_eqz,.br_if 0]
def sizeGuard : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=24},.local_tee 4,
  .i32_const 4294967295,.i32_relop .le_s,.br_if 0]
def flagGuard : Expr := [.local_get 2,.i32_eqz,.br_if 0]
def zeroedArguments : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.local_get 4,.local_get 1,.call 774]
def zeroedCache : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=12},.local_set 5,
  .local_get 3,.load .i32 none {align:=2,offset:=8},.local_set 2]
def rawArguments : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.local_get 4,.local_get 1,.call 769]
def rawCache : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=20},.local_set 5,
  .local_get 3,.load .i32 none {align:=2,offset:=16},.local_set 2]
def choice : Expr := [.block .empty ([.block .empty (flagGuard++zeroedArguments++zeroedCache++[.br 1])]++rawArguments++rawCache)]
def output : Expr := [.local_get 2,.i32_eqz,.br_if 1,.local_get 0,.local_get 2,
  .store .i32 none {align:=2,offset:=0},.local_get 0,.local_get 5,.store .i32 none {align:=2,offset:=4}]
def body767 : Expr := setup 3 32++layoutArguments++[.block .empty
  ([.block .empty (alignmentGuard++sizeGuard++choice++output++restore 3 32++[.return])]
    ++[.call 844,.unreachable])]++[.local_get 4,.local_get 1,.call 842,.unreachable]
def function767 : Func := {type:=31,locals:=[.num .i32,.num .i32,.num .i32],body:=body767,bodySize:=182}
def arguments770 : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.local_get 1,.local_get 2,.i32_const 0,.call 770]
def lowCopy : Expr := [.local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=8},.store .i32 none {align:=2,offset:=0}]
def highCopy : Expr := [.local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=4}]
def body769 : Expr := setup 3 16++arguments770++lowCopy++highCopy++restore 3 16
def function769 : Func := {type:=31,locals:=[.num .i32],body:=body769,bodySize:=69}
def nonzeroGuard : Expr := [.local_get 1,.i32_eqz,.br_if 0]
def recordFlagGuard : Expr := [.local_get 3,.i32_eqz,.br_if 0]
def zeroedCall : Expr := [.local_get 1,.local_get 2,.call 313,.local_set 2,.br 1]
def rawCall : Expr := [.local_get 1,.local_get 2,.call 310,.local_set 2]
def recordWrites : Expr := [.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=4},
  .local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=0}]
def body770 : Expr := [.block .empty (nonzeroGuard++[.block .empty (recordFlagGuard++zeroedCall)]++rawCall)]++recordWrites
def function770 : Func := {type:=45,locals:=[],body:=body770,bodySize:=58}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}
def recordSignature : FuncType := {params:=[.num .i32,.num .i32,.num .i32,.num .i32],results:=[]}
theorem function767_eq : wNearModule.funcs[719]?=some function767 := by kernel_rfl
theorem function769_eq : wNearModule.funcs[721]?=some function769 := by kernel_rfl
theorem function770_eq : wNearModule.funcs[722]?=some function770 := by kernel_rfl
theorem module_signature : wNearModule.types[31]?=some signature := by kernel_rfl
theorem module_recordSignature : wNearModule.types[45]?=some recordSignature := by kernel_rfl
end WNear.Binary.StateDecodeRaw
