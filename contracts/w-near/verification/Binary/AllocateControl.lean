import Binary.AllocateSearch
import Binary.AllocateFit
import Binary.AllocateCallback
import Binary.AllocateArithmetic
import Binary.AllocateSplit

/-! Actual link-control code in f580's end-split branch. -/
namespace WNear.Binary.AllocateSearch
open Wasm

def backlinkGuard : Expr := [.local_get 1,.load .i32 none {align:=2,offset:=0},.local_tee 2,
  .i32_const 4294967292,.i32_binop .and,.local_tee 10,.i32_eqz,.br_if 0,
  .i32_const 0,.local_get 10,.local_get 2,.i32_const 2,.i32_binop .and,.select none,.local_tee 2,.i32_eqz,.br_if 0]
def backlinkWrite : Expr := [.local_get 2,.local_get 2,.load .i32 none {align:=2,offset:=4},
  .i32_const 3,.i32_binop .and,.local_get 9,.i32_binop .or,.store .i32 none {align:=2,offset:=4}]
def backlinkBody := backlinkGuard++backlinkWrite

def previousWrite : Expr := [.local_get 9,.local_get 9,.load .i32 none {align:=2,offset:=4},
  .i32_const 3,.i32_binop .and,.local_get 1,.i32_binop .or,.store .i32 none {align:=2,offset:=4}]
def unflagWrite : Expr := [.local_get 1,.local_get 1,.load .i32 none {align:=2,offset:=8},
  .i32_const 4294967294,.i32_binop .and,.store .i32 none {align:=2,offset:=8}]
def headWrite : Expr := [.local_get 1,.local_get 1,.load .i32 none {align:=2,offset:=0},
  .i32_const 3,.i32_binop .and,.local_get 9,.i32_binop .or,.local_tee 2,.store .i32 none {align:=2,offset:=0}]
def flagExit : Expr := [.local_get 2,.i32_const 2,.i32_binop .and,.i32_eqz,.br_if 12]
def linkCode : Expr := [.block .empty backlinkBody]++previousWrite++unflagWrite++headWrite++flagExit

theorem splitBody_eq : splitBody = Allocate.fitHeader++Allocate.callbackCode++Allocate.splitArithmetic++
    [.local_get 2,.call 574]++Allocate.initializeSplit++linkCode++splitBody.drop 98 := by kernel_rfl
end WNear.Binary.AllocateSearch
