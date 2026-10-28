import Proofs.StateDecodeBorshWrapperState

/-! Literal segmentation of the accepted162 wrapper. The rejected760 call is
retained in its actual block continuation and is not assumed to execute. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near

def setupCode:Expr:=[.global_get 0,.i32_const 96,.i32_binop .sub,.local_tee 2,.global_set 0]
def argumentsCode:Expr:=[.local_get 2,.i32_const 48,.i32_binop .add,.local_get 1]
def cacheValueCode:Expr:=[.local_get 2,.load .i64 none {align:=2,offset:=52},.local_set 3]
def cacheTagCode:Expr:=[.local_get 2,.load .i32 none {align:=2,offset:=48},.local_set 4]
def firstCopyCode:Expr:=[.local_get 2,.i32_const 12,.i32_binop .add,.local_get 2,.i32_const 48,.i32_binop .add,.i32_const 12,.i32_binop .add,.i32_const 36]
def prepareGuardCode:Expr:=[.drop,.i32_const 1,.local_set 1]
def guardCode:Expr:=[.local_get 4,.i32_const 1,.i32_relop .eq,.br_if 0]
def packedStoreCode:Expr:=[.local_get 0,.i32_const 8,.i32_binop .add,.local_get 3,.i64_const 32,.i64_binop .shr_u,.store .i64 (some 32) {align:=2,offset:=0}]
def secondCopyCode:Expr:=[.local_get 0,.i32_const 12,.i32_binop .add,.local_get 2,.i32_const 12,.i32_binop .add,.i32_const 36]
def acceptedExitCode:Expr:=[.drop,.i32_const 0,.local_set 1,.br 1]
def errorCode:Expr:=[.local_get 0,.local_get 3,.call 760,.store .i64 none {align:=2,offset:=4}]
def finishCode:Expr:=[.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=0},.local_get 2,.i32_const 96,.i32_binop .add,.global_set 0]
def acceptedCode:Expr:=guardCode++packedStoreCode++secondCopyCode++[.call 951]++acceptedExitCode
def bodyCode:Expr:=setupCode++argumentsCode++[.call 425]++cacheValueCode++cacheTagCode++firstCopyCode++[.call 951]++prepareGuardCode++
  [.block .empty ([.block .empty acceptedCode]++errorCode)]++finishCode

theorem body_code:WNear.Binary.StateDecodeBorshWrapper.body=bodyCode:=by rfl
end WNear.Proofs.StateDecodeBorshWrapper
