import Binary.Allocate

/-! The actual free-block initialization in the end-split branch of f580. -/
namespace WNear.Binary.Allocate
open Wasm

def initializeSplit : Expr := [.local_get 9,.i32_const 0,.store .i32 none {align:=2,offset:=8},
  .local_get 9,.i64_const 0,.store .i64 none {align:=2,offset:=0},
  .local_get 9,.local_get 1,.load .i32 none {align:=2,offset:=0},
  .i32_const 4294967292,.i32_binop .and,.store .i32 none {align:=2,offset:=0}]
private def findInitialize : Nat → Expr → Option Expr
| 0,_ => none
| n+1,code => match code with
  | .local_get 9 :: .i32_const zero :: _ =>
    if zero == 0 then some (code.take 12) else findInitialize n code.tail
  | [] => none
  | instruction::tail =>
    let nested := match instruction with
      | .block _ body | .loop _ body => findInitialize n body
      | .if _ left right => (findInitialize n left).orElse (fun _=>findInitialize n right)
      | _ => none
    nested.orElse (fun _=>findInitialize n tail)
/-- Kernel-checked source occurrence, independent of any allocator execution. -/
theorem initializeSplit_occurs : findInitialize 600 searchFunction.body = some initializeSplit := by kernel_rfl
end WNear.Binary.Allocate
