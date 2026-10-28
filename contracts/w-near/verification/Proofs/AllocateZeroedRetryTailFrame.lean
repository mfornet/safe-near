import Proofs.AllocateZeroedRetryGas

/-! Generic frames for the actual153 guard/memset/drop suffix. These apply to
the concrete post-allocation memory, retaining all aliases. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] ZeroFill.callAfter

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem tail_memory (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32)
    (hm : s.mems[index]?=some memory) :
    (AllocateZeroed.tailAfter s op index memory ptr len).mems[index]?=
      some (ZeroFill.filledMemory memory ptr 0 len.toNat) := by
  rw [AllocateZeroed.tailAfter,mems_paid,AllocateZeroed.tailFilled]
  apply ZeroFill.callAfter_memory
  rw [mems_paid,mems_paid]
  exact hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_fill (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :
    fields (ZeroFill.callAfter s op index memory ptr 0 len)=fields s := by
  have h := ZeroFill.callAfter_fields s op index memory ptr 0 len
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

theorem tail_fields (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :
    (AllocateZeroed.tailAfter s op index memory ptr len).funcs=s.funcs ∧
    (AllocateZeroed.tailAfter s op index memory ptr len).modules=s.modules ∧
    (AllocateZeroed.tailAfter s op index memory ptr len).tables=s.tables ∧
    (AllocateZeroed.tailAfter s op index memory ptr len).globals=s.globals := by
  have h : fields (AllocateZeroed.tailAfter s op index memory ptr len)=fields s := by
    rw [AllocateZeroed.tailAfter,fields_paid,AllocateZeroed.tailFilled,fields_fill,fields_paid,fields_paid]
  exact ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,
    congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_fill (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :
    view seed (ZeroFill.callAfter s op index memory ptr 0 len).host=view seed s.host := by
  have h := congrArg (view seed) (ZeroFill.callAfter_host s op index memory ptr 0 len)
  simpa only [view] using h

theorem tail_functional_host (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :
    {(AllocateZeroed.tailAfter s op index memory ptr len).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (AllocateZeroed.tailAfter s op index memory ptr len).host=s.host
  rw [AllocateZeroed.tailAfter,view_paid,AllocateZeroed.tailFilled,view_fill,view_paid,view_paid]
  rfl
end WNear.Proofs.AllocateZeroedRetry
