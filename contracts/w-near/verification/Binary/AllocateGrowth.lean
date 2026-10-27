import Binary.AllocateGrowthHelpers

/-! Exact deployed f577 memory-growth control and successful-store decomposition. -/
namespace WNear.Binary.AllocateGrowth
open Wasm

def preparation : Expr := [.local_get 2,.call 572,.local_set 4]
def sizing : Expr := [.local_get 3,.i32_const 64,.i32_binop .add,.local_tee 2,.local_get 3,.i32_relop .lt_u,.br_if 0,
  .local_get 2,.i32_const 536870911,.i32_binop .and,.local_get 2,.i32_relop .ne,.br_if 1,
  .local_get 4,.local_get 2,.i32_const 3,.i32_binop .shl,.local_tee 2,.local_get 4,.local_get 2,.i32_relop .gt_u,
  .select none,.local_tee 2,.i32_const 8,.i32_binop .add,.local_tee 3,.local_get 2,.i32_relop .lt_u,.br_if 2]
def growAttempt : Expr := [.local_get 3,.call 569,.local_tee 3,.memory_grow,.local_tee 2,.i32_const 4294967295,.i32_relop .ne,.br_if 0]
def growFailed : Expr := [.i32_const 1,.local_set 3,.br 1]
def oldPagesGuard : Expr := [.local_get 2,.i32_const 65535,.i32_binop .and,.local_get 2,.i32_relop .ne,.br_if 4]
def bytesAndMinimum : Expr := [.local_get 3,.call 573,.local_tee 4,.call 574]
def freshHeader : Expr := [.local_get 2,.i32_const 16,.i32_binop .shl,.local_tee 2,.i64_const 0,
  .store .i64 none {align:=3,offset:=0},.i32_const 0,.local_set 3,.local_get 2,.i32_const 0,
  .store .i32 none {align:=2,offset:=8},.local_get 2,.local_get 2,.local_get 4,.i32_binop .add,.i32_const 2,
  .i32_binop .or,.store .i32 none {align:=2,offset:=0}]
def growthBlock : Expr := [.block .empty ([.block .empty (growAttempt++growFailed)]++oldPagesGuard++bytesAndMinimum++freshHeader)]
def recordReturn : Expr := [.local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=4},
  .local_get 0,.local_get 3,.store .i32 none {align:=2,offset:=0},.return]
def panicAdd : Expr := [.i32_const 1057104,.i32_const 28,.i32_const 1057268,.call 853,.unreachable]
def panicBits : Expr := [.i32_const 1057216,.i32_const 33,.i32_const 1057268,.call 853,.unreachable]
def panicFinal : Expr := [.i32_const 1057216,.i32_const 33,.i32_const 1057580,.call 853,.unreachable]
def accepted : Expr := sizing++growthBlock++recordReturn
def body : Expr := preparation++[.block .empty ([.block .empty ([.block .empty ([.block .empty accepted]++panicAdd)]++panicBits)]++panicAdd)]++panicFinal
def function : Func := {type:=45,locals:=[.num .i32],body,bodySize:=274}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32,.num .i32],results:=[]}

theorem module_function : wNearModule.funcs[529]?=some function := by kernel_rfl
theorem module_signature577 : wNearModule.types[45]?=some signature := by kernel_rfl
end WNear.Binary.AllocateGrowth
