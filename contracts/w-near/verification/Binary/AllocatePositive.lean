import Binary.Allocate

/-! Exact positive-size control decomposition of the deployed581 wrapper. -/
namespace WNear.Binary.AllocatePositive
open Wasm

def reserve : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 3,.global_set 0]
def zeroTail : Expr := [.local_get 2,.local_set 1,.br 1]
def positiveGuard : Expr := [.block .empty ([.local_get 1,.br_if 0]++zeroTail)]
def updateHead : Expr := [.local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=0}]
def searchBlock : Expr := [.block .empty (Allocate.attempt++[.local_tee 1,.br_if 0]++Allocate.retry)]
def positive : Expr := positiveGuard++Allocate.alignAndSave++searchBlock++updateHead
def restore : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 1]

theorem body_eq : Allocate.function.body=reserve++[.block .empty positive]++restore := by rfl
end WNear.Binary.AllocatePositive
