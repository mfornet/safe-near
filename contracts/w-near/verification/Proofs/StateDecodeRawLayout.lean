import Proofs.StateDecodeRawCode

/-! Original-resource readiness of the actual752 layout call in767. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

def reservedRaw (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def layoutArgumentsRaw (s : Store NearState) (op : Nat) (p : Layout) := paid (reservedRaw s op p) op 4

def reservedRawFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 3 (.i32 (scratch p))}

private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem global_funcs (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).modules=s.modules:=rfl
private theorem global_mems (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems:=rfl

/-- All local752 readiness follows from original code, memory and stack bounds.
The actual reserved global is derived, not a future array-lookup hypothesis. -/
theorem layout_ready (s : Store NearState) (op inst height : Nat) (p : Layout) (a581 a236 : Nat)
    (hn : Native p) (hc : Code s inst p a581 a236)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) :
    AllocateLayoutWrapper.Ready (layoutArgumentsRaw s op p)
      (AllocateLayoutWrapper.leafFrame inst height (layout752 p)) (layout752 p) := by
  have b:=layout_bounds p hn
  have mm : (layoutArgumentsRaw s op p).modules=s.modules := by
    simp only [layoutArgumentsRaw,reservedRaw,paid_modules,global_modules]
  have mf : (layoutArgumentsRaw s op p).funcs=s.funcs := by
    simp only [layoutArgumentsRaw,reservedRaw,paid_funcs,global_funcs]
  have me : (layoutArgumentsRaw s op p).mems=s.mems := by
    simp only [layoutArgumentsRaw,reservedRaw,paid_mems,global_mems]
  have gg : (layoutArgumentsRaw s op p).globals[p.globalIndex]?=some (layout752 p).global := by
    simp only [layoutArgumentsRaw,reservedRaw,paid_globals,setGlobal,Array.getElem?_modify,hg,Option.map_some,layout752,ite_true]
  refine ⟨?_,hc.record.allocation.globalIndex,gg,rfl,hc.record.allocation.search.memoryIndex,?_,
    hc.index751,?_,rfl,rfl,by simp [AllocateLayoutWrapper.leafFrame],hn.allocation.wf,hn.allocation.width,b.1,b.2⟩
  · change (layoutArgumentsRaw s op p).modules[inst]?=some p.mi
    rw [mm];exact hc.record.allocation.search.module
  · change (layoutArgumentsRaw s op p).mems[p.memoryIndex]?=some p.memory
    rw [me];exact hm
  · rw [mf]
    exact hc.function751
end WNear.Proofs.StateDecodeRaw
