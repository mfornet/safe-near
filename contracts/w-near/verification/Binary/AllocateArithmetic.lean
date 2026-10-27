import Binary.Allocate

/-! The actual five arithmetic guards after f580's minimum-layout callback. -/
namespace WNear.Binary.Allocate
open Wasm

def splitBase : Expr := [.local_get 9,.i32_const 8,.i32_binop .add,.local_tee 10,.local_get 9,.i32_relop .lt_u,.br_if 2]
def splitMinimum : Expr := [.local_get 10,.local_get 13,.i32_binop .add,.local_tee 13,.local_get 10,.i32_relop .lt_u,.br_if 3]
def splitFit : Expr := [.local_get 13,.local_get 12,.local_get 6,.i32_binop .and,.local_tee 10,.i32_relop .gt_u,.br_if 8]
def splitHeader : Expr := [.local_get 10,.i32_const 4294967288,.i32_binop .add,.local_tee 9,.local_get 10,.i32_relop .gt_u,.br_if 4]
def splitLength : Expr := [.local_get 11,.local_get 9,.i32_binop .sub,.local_tee 2,.local_get 11,.i32_relop .gt_u,.br_if 5]
def splitArithmetic := splitBase++splitMinimum++splitFit++splitHeader++splitLength
private def findArithmetic : Nat → Expr → Option Expr
| 0,_ => none
| n+1,code => match code with
  | .local_get 9 :: .i32_const amount :: _ =>
    if amount == 8 then some (code.take 35) else findArithmetic n code.tail
  | [] => none
  | instruction::tail =>
    let nested := match instruction with
      | .block _ body | .loop _ body => findArithmetic n body
      | .if _ left right => (findArithmetic n left).orElse (fun _=>findArithmetic n right)
      | _ => none
    nested.orElse (fun _=>findArithmetic n tail)
theorem splitArithmetic_occurs : findArithmetic 600 searchFunction.body = some splitArithmetic := by kernel_rfl
end WNear.Binary.Allocate
