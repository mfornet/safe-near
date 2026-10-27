import Binary.AllocateControl

/-! Actual flag-transfer tail after the flags-two split's conditional exit. -/
namespace WNear.Binary.AllocateFlagged
open Wasm
set_option maxRecDepth 30000

def clearOld : Expr := [.local_get 1,.local_get 2,.i32_const 4294967293,.i32_binop .and,.store .i32 none {align:=2,offset:=0}]
def markNew : Expr := [.local_get 9,.local_get 9,.load .i32 none {align:=2,offset:=0},.i32_const 2,.i32_binop .or,.store .i32 none {align:=2,offset:=0}]
def transfer : Expr := clearOld++markNew++[.br 12]
theorem actual_transfer : AllocateSearch.splitBody.drop 98=transfer := by kernel_rfl
end WNear.Binary.AllocateFlagged
