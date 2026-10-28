import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodePrefixAllocationCode

/-! Original425 installed descriptors. Scalar child code is derived for the
actual sequential layouts; no future code or execution equation is a field. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] prefixMemory savedPrefixMemory savedWideMemory wideMemory wideFirstMemory wideSecondMemory readI32 readI64 writeI32 writeI64

structure Code (s : Store NearState) (inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat) : Prop where
  prefixCode : StateDecodePrefixWrapper.Code s inst p.toPrefixWrapper
  allocation : StateDecodeVectorCopy.Code s inst q a581 a236
  index315 : p.mi.funcAddrs[315]?=some p.address315
  function315 : s.funcs[p.address315]?=some (.wasm WNear.Binary.StateDecodePrefixWrapper.signature inst WNear.Binary.StateDecodePrefixWrapper.function)
  index372 : p.mi.funcAddrs[372]?=some p.address372
  function372 : s.funcs[p.address372]?=some (.wasm WNear.Binary.StateDecodeScalar.signature inst (WNear.Binary.StateDecodeScalar.function true))
  index371 : p.mi.funcAddrs[371]?=some p.address371
  function371 : s.funcs[p.address371]?=some (.wasm WNear.Binary.StateDecodeScalar.signature inst (WNear.Binary.StateDecodeScalar.function false))
  index694 : p.mi.funcAddrs[694]?=some p.address694
  function694 : s.funcs[p.address694]?=some (.wasm WNear.Binary.StateDecodeWords.signature inst (WNear.Binary.StateDecodeWords.function true))
  index710 : p.mi.funcAddrs[710]?=some p.address710
  function710 : s.funcs[p.address710]?=some (.wasm WNear.Binary.StateDecodeWords.signature inst (WNear.Binary.StateDecodeWords.function false))

private theorem prefix_transport (s t : Store NearState) (inst : Nat) (p : StateDecodePrefix.Layout)
    (hc : StateDecodePrefix.Code s inst p) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) : StateDecodePrefix.Code t inst p := by
  refine {hc with module:=?_,takeFunction:=?_,dropFunction:=?_,wordFunction:=?_,lengthFunction:=?_,copyFunction:=?_}
  · rw[hm];exact hc.module
  · rw[hf];exact hc.takeFunction
  · rw[hf];exact hc.dropFunction
  · rw[hf];exact hc.wordFunction
  · rw[hf];exact hc.lengthFunction
  · rw[hf];exact hc.copyFunction

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    Code t inst p q a581 a236 := by
  have child:=prefix_transport s t inst p.toPrefix hc.prefixCode.child hf hm
  have prefixCode:StateDecodePrefixWrapper.Code t inst p.toPrefixWrapper:=by
    refine {hc.prefixCode with child:=child,childFunction:=?_}
    rw[hf];exact hc.prefixCode.childFunction
  have allocation:=StateDecodePrefix.allocation_copy_code_transport s t inst q a581 a236 hc.allocation hf hm ht
  refine {hc with prefixCode:=prefixCode,allocation:=allocation,function315:=?_,function372:=?_,function371:=?_,function694:=?_,function710:=?_}
  · rw[hf];exact hc.function315
  · rw[hf];exact hc.function372
  · rw[hf];exact hc.function371
  · rw[hf];exact hc.function694
  · rw[hf];exact hc.function710

/-- The memory and decoded pointer/length in wideLayout are actual computed
values, but code depends only on its original module/address fields. -/
theorem Code.wide (s : Store NearState) (inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) : StateDecodeScalar.Code true s inst (wideLayout p q) := by
  exact ⟨hc.prefixCode.child.module,hc.prefixCode.child.memoryIndex,hc.prefixCode.child.globalIndex,
    hc.prefixCode.child.takeAddress,hc.prefixCode.child.takeFunction,hc.index694,hc.function694,
    hc.prefixCode.child.dropAddress,hc.prefixCode.child.dropFunction⟩

theorem Code.narrow (s : Store NearState) (inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) : StateDecodeScalar.Code false s inst (narrowLayout p q) := by
  exact ⟨hc.prefixCode.child.module,hc.prefixCode.child.memoryIndex,hc.prefixCode.child.globalIndex,
    hc.prefixCode.child.takeAddress,hc.prefixCode.child.takeFunction,hc.index710,hc.function710,
    hc.prefixCode.child.dropAddress,hc.prefixCode.child.dropFunction⟩

theorem Code.wide_on (s t : Store NearState) (inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) :
    StateDecodeScalar.Code true t inst (wideLayout p q) :=
  (hc.wide s inst p q a581 a236).transport hf hm

theorem Code.narrow_on (s t : Store NearState) (inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) :
    StateDecodeScalar.Code false t inst (narrowLayout p q) :=
  (hc.narrow s inst p q a581 a236).transport hf hm

private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem global_funcs (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).modules=s.modules:=rfl
private theorem global_tables (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).tables=s.tables:=rfl

theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) : Code (StorePairCaller.paid s op n) inst p q a581 a236 :=
  hc.transport s (StorePairCaller.paid s op n) inst p q a581 a236 (paid_funcs s op n) (paid_modules s op n) (paid_tables s op n)

theorem Code.reserved (s : Store NearState) (op inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) : Code (StateDecodeBorsh.reserved s op p) inst p q a581 a236 := by
  apply hc.transport s (StateDecodeBorsh.reserved s op p) inst p q a581 a236
  · simp only[StateDecodeBorsh.reserved,global_funcs,paid_funcs]
  · simp only[StateDecodeBorsh.reserved,global_modules,paid_modules]
  · simp only[StateDecodeBorsh.reserved,global_tables,paid_tables]

theorem Code.prefixArguments (s : Store NearState) (op inst : Nat) (p : Layout) (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : Code s inst p q a581 a236) : Code (StateDecodeBorsh.prefixArguments s op p) inst p q a581 a236 := by
  have cr:=hc.reserved s op inst p q a581 a236
  apply cr.transport (StateDecodeBorsh.reserved s op p) (StateDecodeBorsh.prefixArguments s op p) inst p q a581 a236
  · simp only[StateDecodeBorsh.prefixArguments,paid_funcs]
  · simp only[StateDecodeBorsh.prefixArguments,paid_modules]
  · simp only[StateDecodeBorsh.prefixArguments,paid_tables]
end WNear.Proofs.StateDecodeBorsh
