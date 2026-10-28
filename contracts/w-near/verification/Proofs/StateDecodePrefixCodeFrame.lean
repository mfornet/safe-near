import Proofs.StateDecodePrefixCode
import Proofs.StateDecodePrefixTakeCall
import Proofs.StateDecodePrefixWordCall

/-! Original installed prefix-decoder code through its actual early calls. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) : Code t inst p := by
  refine {h with module:=?_,takeFunction:=?_,dropFunction:=?_,wordFunction:=?_,lengthFunction:=?_,copyFunction:=?_}
  · rw[hm];exact h.module
  · rw[hf];exact h.takeFunction
  · rw[hf];exact h.dropFunction
  · rw[hf];exact h.wordFunction
  · rw[hf];exact h.lengthFunction
  · rw[hf];exact h.copyFunction

theorem Code.after_paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (paid s op n) inst p := h.transport s (paid s op n) inst p (paid_funcs s op n) (paid_modules s op n)

attribute [local irreducible] takeAfter wordAfter

theorem Code.after_take (cfg : WasmConfig) (s : Store NearState) (inst : Nat) (p : Layout)
    (h : Code s inst p) (scratch pointer len : UInt32) :
    Code (takeAfter cfg s p.memoryIndex p.memory scratch pointer len) inst p := by
  have f:=StateDecodeSlices.callAfter_fields false (paid s cfg.regularOpCost 8) cfg.regularOpCost p.memoryIndex p.memory (scratch+40) pointer len 4
  have hf : (takeAfter cfg s p.memoryIndex p.memory scratch pointer len).funcs=s.funcs := by
    unfold WNear.Proofs.StateDecodePrefix.takeAfter
    rw[f.1,paid_funcs]
  have hm : (takeAfter cfg s p.memoryIndex p.memory scratch pointer len).modules=s.modules := by
    unfold WNear.Proofs.StateDecodePrefix.takeAfter
    rw[f.2.1,paid_modules]
  exact h.transport s _ inst p hf hm

theorem Code.after_word (cfg : WasmConfig) (s : Store NearState) (inst : Nat) (p : Layout)
    (h : Code s inst p) : Code (wordAfter cfg s) inst p := by
  have f:=StateDecodePrefixLeaves.wordCallAfter_fields cfg (paid s cfg.regularOpCost 4)
  have hf : (wordAfter cfg s).funcs=s.funcs := by unfold WNear.Proofs.StateDecodePrefix.wordAfter;rw[f.1,paid_funcs]
  have hm : (wordAfter cfg s).modules=s.modules := by unfold WNear.Proofs.StateDecodePrefix.wordAfter;rw[f.2.1,paid_modules]
  exact h.transport s _ inst p hf hm
end WNear.Proofs.StateDecodePrefix
