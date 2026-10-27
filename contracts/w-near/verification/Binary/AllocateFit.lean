import Binary.Allocate

/-! Actual pre-split end subtraction and overflow guards of f580. -/
namespace WNear.Binary.Allocate
open Wasm

def fitHeader : Expr := [.local_get 1,.load .i32 none {align:=2,offset:=0},.i32_const 4294967292,
  .i32_binop .and,.local_tee 11,.local_get 10,.i32_binop .sub,.local_tee 12,.local_get 11,
  .i32_relop .gt_u,.br_if 0,.local_get 8,.br_if 1]
private def findFit : Nat → Expr → Option Expr
| 0,_ => none
| n+1,code => match code with
  | .local_get 1 :: .load .i32 none _ :: .i32_const mask :: _ =>
    if mask == 4294967292 then some (code.take 13) else findFit n code.tail
  | [] => none
  | instruction::tail =>
    let nested := match instruction with
      | .block _ body | .loop _ body => findFit n body
      | .if _ left right => (findFit n left).orElse (fun _=>findFit n right)
      | _ => none
    nested.orElse (fun _=>findFit n tail)
theorem fitHeader_occurs : findFit 600 searchFunction.body = some fitHeader := by kernel_rfl
end WNear.Binary.Allocate
