import Binary.AllocatePositive

/-! Exact growth and retry instruction groups in deployed f581. -/
namespace WNear.Binary.AllocateRetry
open Wasm

def growthArguments : Expr := [.local_get 3,.i32_const 1057464,.local_get 4,.local_get 2]
def growthCheck : Expr := [.i32_const 0,.local_set 1,.local_get 3,
  .load .i32 none {align:=2,offset:=0},.br_if 0]
def relink : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=4},.local_tee 1,
  .local_get 3,.load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=8},
  .local_get 3,.local_get 1,.store .i32 none {align:=2,offset:=12}]
def secondAttempt : Expr := Allocate.attempt++[.local_set 1]

theorem retry_eq : Allocate.retry = growthArguments++[.call 577]++growthCheck++relink++secondAttempt := rfl

theorem relink_length : relink.length=9 := rfl
end WNear.Binary.AllocateRetry
