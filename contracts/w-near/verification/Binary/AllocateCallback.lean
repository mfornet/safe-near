import Binary.Allocate

/-! The actual minimum-layout callback and byte conversion in f580. -/
namespace WNear.Binary.Allocate
open Wasm

def callbackCode : Expr := [.local_get 3,.local_get 0,.local_get 4,
  .load .i32 none {align:=2,offset:=16},.call_indirect 13 0,.call 572,.local_set 13]
private def findCallback : Nat → Expr → Option Expr
| 0,_ => none
| n+1,code => match code with
  | .local_get 3 :: .local_get 0 :: .local_get 4 :: _ => some (code.take 7)
  | [] => none
  | instruction::tail =>
    let nested := match instruction with
      | .block _ body | .loop _ body => findCallback n body
      | .if _ left right => (findCallback n left).orElse (fun _=>findCallback n right)
      | _ => none
    nested.orElse (fun _=>findCallback n tail)
theorem callbackCode_occurs : findCallback 600 searchFunction.body = some callbackCode := by kernel_rfl
end WNear.Binary.Allocate
