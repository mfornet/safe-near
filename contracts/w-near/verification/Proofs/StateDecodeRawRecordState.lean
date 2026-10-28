import Proofs.StateDecodeRawState
import Proofs.StateDecodeRawGuards

/-! Generic original-resource interface for f770's actual nonzeroing allocation
call. Descriptor fields are structural code facts, not execution callbacks. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure RecordCode (s : Store NearState) (inst : Nat) (q : AllocatePositive.Layout) (address581 address236 address310 : Nat) : Prop where
  allocation : AllocatePositive.Code s inst q
  index581 : q.mi.funcAddrs[581]?=some address581
  function581 : s.funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature inst WNear.Binary.Allocate.function)
  index236 : q.mi.funcAddrs[236]?=some address236
  function236 : s.funcs[address236]?=some (.wasm WNear.Binary.AllocateRawForward.signature inst WNear.Binary.AllocateRawForward.function236)
  index310 : q.mi.funcAddrs[310]?=some address310
  function310 : s.funcs[address310]?=some (.wasm WNear.Binary.AllocateRawForward.signature inst WNear.Binary.AllocateRawForward.function310)

def allocatedRecord (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) :=
  AllocateRawForwardDirect.callAfter310 cfg (paid s cfg.regularOpCost 2) q
def allocationFrame (frame : CallFrame) (q : AllocatePositive.Layout) :=
  {frame with locals:=frame.locals.set! 2 (.i32 (AllocatePositive.result q))}
def recordInput (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) :=
  paid (allocatedRecord cfg s q) cfg.regularOpCost 1

private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
theorem RecordCode.paid (s : Store NearState) (op n inst : Nat) (q : AllocatePositive.Layout) (a581 a236 a310 : Nat)
    (h : RecordCode s inst q a581 a236 a310) : RecordCode (paid s op n) inst q a581 a236 a310 := by
  refine {h with allocation:=h.allocation.paid s op n inst q,function581:=?_,function236:=?_,function310:=?_}
  · rw[funcs_paid];exact h.function581
  · rw[funcs_paid];exact h.function236
  · rw[funcs_paid];exact h.function310
end WNear.Proofs.StateDecodeRaw
