import Binary.StateDecodePrefixLeaves

/-! Exact deployed Borsh byte-vector prefix reader and its result wrapper. -/
namespace WNear.Binary.StateDecodePrefix
open Wasm Wasm.Near

def setup : Expr := [.global_get 0,.i32_const 64,.i32_binop .sub,.local_tee 2,.global_set 0]
def lengthGuard : Expr := [.local_get 1,.load .i32 none {align:=2,offset:=4},.local_tee 3,.i32_const 4,.i32_relop .lt_u,.br_if 0]
def takeFour : Expr := [.local_get 2,.i32_const 40,.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 3,.i32_const 4,.i32_const 1052240,.call 362]
def wordArguments : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=40},.local_get 2,.load .i32 none {align:=2,offset:=44},.call 765]
def wordStatus : Expr := [.local_tee 4,.i64_const 1,.i64_binop .and,.i64_eqz,.i32_eqz,.br_if 0]
def dropFour : Expr := [.local_get 2,.i32_const 32,.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},.i32_const 4,.i32_const 1052240,.call 361]
def advanceFour : Expr := [.local_get 1,.local_get 2,.load .i64 none {align:=3,offset:=32},.store .i64 none {align:=2,offset:=0}]
def nonzero : Expr := [.local_get 4,.i64_const 8,.i64_binop .shr_u,.cvt .i32_wrap_i64,.local_tee 3,.br_if 0,
  .local_get 0,.i64_const 4294967296,.store .i64 none {align:=2,offset:=0},.local_get 0,.i32_const 8,.i32_binop .add,
  .i64_const 0,.store .i64 none {align:=2,offset:=0},.br 4]
def lengthArguments : Expr := [.local_get 2,.i32_const 24,.i32_binop .add,.local_get 3,.call 764]
def lengthStatus : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=24},.br_if 2]
def enough : Expr := [.local_get 1,.load .i32 none {align:=2,offset:=4},.local_tee 5,.local_get 2,.load .i32 none {align:=2,offset:=28},.local_tee 3,.i32_relop .ge_u,.br_if 0,
  .i32_const 11,.i32_const 1052128,.i32_const 26,.call 736,.local_set 4,.local_get 0,.i32_const 1,.store .i32 none {align:=2,offset:=0},.local_get 0,.local_get 4,.store .i64 none {align:=2,offset:=4},.br 4]
def takePayload : Expr := [.local_get 2,.i32_const 16,.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 5,.local_get 3,.i32_const 1052508,.call 362]
def copyArguments : Expr := [.local_get 2,.i32_const 48,.i32_binop .add,.local_get 2,.load .i32 none {align:=2,offset:=16},.local_get 2,.load .i32 none {align:=2,offset:=20},.call 374]
def dropPayload : Expr := [.local_get 2,.i32_const 8,.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},.local_get 3,.i32_const 1052524,.call 361]
def output : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=8},.local_set 4,
  .local_get 0,.i32_const 12,.i32_binop .add,.local_get 2,.load .i32 none {align:=2,offset:=56},.store .i32 none {align:=2,offset:=0},
  .local_get 0,.local_get 2,.load .i64 none {align:=3,offset:=48},.store .i64 none {align:=2,offset:=4},
  .local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0},.local_get 1,.local_get 4,.store .i64 none {align:=2,offset:=0},.br 3]
def accepted : Expr := wordArguments++wordStatus++dropFour++advanceFour++[.block .empty nonzero]++lengthArguments++lengthStatus++[.block .empty enough]++takePayload++copyArguments++dropPayload++output
def panic : Expr := [.i32_const 1052068,.i32_const 43,.local_get 2,.i32_const 48,.i32_binop .add,.i32_const 1052112,.i32_const 1052240,.call 881,.unreachable]
def short : Expr := [.i32_const 11,.i32_const 1052128,.i32_const 26,.call 736,.call 760,.local_set 4,
  .local_get 0,.i32_const 1,.store .i32 none {align:=2,offset:=0},.local_get 0,.local_get 4,.store .i64 none {align:=2,offset:=4},.br 1]
def invalid : Expr := [.local_get 0,.i32_const 1,.store .i32 none {align:=2,offset:=0},.local_get 0,.i64_const 2817,.store .i64 none {align:=2,offset:=4}]
def restore : Expr := [.local_get 2,.i32_const 64,.i32_binop .add,.global_set 0]
def body : Expr := setup++[.block .empty ([.block .empty ([.block .empty (lengthGuard++takeFour++[.block .empty accepted]++panic)]++short)]++invalid)]++restore
def function : Func := {type:=14,locals:=[.num .i32,.num .i32,.num .i64,.num .i32],body,bodySize:=471}
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}
noncomputable def wrapperFunction : Func := WNear.Binary.f315

theorem function316 : wNearModule.funcs[268]?=some function:=by kernel_rfl
theorem function315 : wNearModule.funcs[267]?=some wrapperFunction:=by kernel_rfl
theorem module_signature : wNearModule.types[14]?=some signature:=by kernel_rfl
end WNear.Binary.StateDecodePrefix
