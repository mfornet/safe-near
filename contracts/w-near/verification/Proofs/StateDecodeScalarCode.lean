import Proofs.StateDecodeScalarFrame

/-! Original deployed child descriptors required by scalar decoding. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic

structure Code (wide : Bool) (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  module : s.modules[inst]?=some p.mi
  memoryIndex : p.mi.memAddrs[0]?=some p.memoryIndex
  globalIndex : p.mi.globalAddrs[0]?=some p.globalIndex
  takeAddress : p.mi.funcAddrs[362]?=some p.addressTake
  takeFunction : s.funcs[p.addressTake]?=some (.wasm WNear.Binary.StateDecodeSlices.signature inst (WNear.Binary.StateDecodeSlices.function false))
  wordAddress : p.mi.funcAddrs[if wide then 694 else 710]?=some p.addressWord
  wordFunction : s.funcs[p.addressWord]?=some (.wasm WNear.Binary.StateDecodeWords.signature inst (WNear.Binary.StateDecodeWords.function wide))
  dropAddress : p.mi.funcAddrs[361]?=some p.addressDrop
  dropFunction : s.funcs[p.addressDrop]?=some (.wasm WNear.Binary.StateDecodeSlices.signature inst (WNear.Binary.StateDecodeSlices.function true))

theorem Code.transport {wide : Bool} {s t : Store NearState} {inst : Nat} {p : Layout}
    (h : Code wide s inst p) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) : Code wide t inst p := by
  refine {h with module:=?_,takeFunction:=?_,wordFunction:=?_,dropFunction:=?_}
  · rw [hm];exact h.module
  · rw [hf];exact h.takeFunction
  · rw [hf];exact h.wordFunction
  · rw [hf];exact h.dropFunction

private theorem paid_funcs (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem global_funcs (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).modules=s.modules:=rfl

theorem Code.reserved (wide : Bool) (s : Store NearState) (op : Nat) (inst : Nat) (p : Layout)
    (h : Code wide s inst p) : Code wide (reserved s op p) inst p := by
  apply Code.transport h
  · simp only [StateDecodeScalar.reserved,global_funcs,paid_funcs]
  · simp only [StateDecodeScalar.reserved,global_modules,paid_modules]

theorem Code.taken (wide : Bool) (s : Store NearState) (op : Nat) (inst : Nat) (p : Layout)
    (h : Code wide s inst p) : Code wide (taken wide s op p) inst p := by
  have hr:=Code.reserved wide s op inst p h
  have hf:=taken_fields wide s op p
  exact hr.transport hf.1 hf.2.1

theorem Code.readWords (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (inst : Nat) (p : Layout)
    (h : Code wide s inst p) : Code wide (readWords wide cfg s p) inst p := by
  have hr:=Code.reserved wide s cfg.regularOpCost inst p h
  have hf:=readWords_fields wide cfg s p
  exact hr.transport hf.1 hf.2.1

theorem Code.dropped (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (inst : Nat) (p : Layout)
    (h : Code wide s inst p) : Code wide (dropped wide cfg s p) inst p := by
  have hr:=Code.reserved wide s cfg.regularOpCost inst p h
  have hf:=dropped_fields wide cfg s p
  exact hr.transport hf.1 hf.2.1

end WNear.Proofs.StateDecodeScalar
