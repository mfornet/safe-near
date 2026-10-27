import Binary.AllocateLoop

/-! Actual short-candidate traversal suffix in the deployed f580 search. -/
namespace WNear.Binary.AllocateSkip
open Wasm

def advance : Expr := [.local_get 2,.local_get 9,.load .i32 none {align:=2,offset:=0},
  .local_tee 1,.store .i32 none {align:=2,offset:=0},.br 1]

theorem advance_eq : AllocateSearch.candidateOuter.drop 1=advance := by kernel_rfl
end WNear.Binary.AllocateSkip
