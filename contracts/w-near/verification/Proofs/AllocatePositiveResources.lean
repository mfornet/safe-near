import Proofs.AllocatePositiveFrame

/-! Original installed-code resources transport through the actual wrapper phases. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] readI32 writeI32 prefixed searched found updated after

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  constructor
  · constructor
    · exact h.search.toCode.transport s t (searchLayout p) inst hf hm ht
    · exact h.search.sizeIndex
    · rw [hf]; exact h.search.sizeFunction
  · exact h.globalIndex
  · exact h.alignIndex
  · rw [hf]; exact h.alignFunction
  · exact h.roundIndex
  · rw [hf]; exact h.roundFunction
  · exact h.searchIndex
  · rw [hf]; exact h.searchFunction

theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) : Code (paid s op n) inst p := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.transport _ _ inst p rfl rfl rfl

theorem prefixed_code (s : Store NearState) (op inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (prefixed s op p) inst p := by
  have fs := prefixed_fields s op p
  exact h.transport s _ inst p fs.1 fs.2.1 fs.2.2

theorem found_code (s : Store NearState) (op inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (found s op p) inst p := by
  have fs := found_fields s op p
  exact h.transport s _ inst p fs.1 fs.2.1 fs.2.2

theorem updated_code (s : Store NearState) (op inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (updated s op p) inst p := by
  have fs := updated_fields s op p
  exact h.transport s _ inst p fs.1 fs.2.1 fs.2.2

theorem searchedMemory_size (p : Layout) (hn : Native p) : (searchedMemory p).byteSize=p.memory.byteSize := by
  have scratchBound := (scratch_numbers p hn).2.2.1
  have saved := writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hn.wf (by omega)
  exact (AllocateSearch.final_shape (searchLayout p) hn.search).size.trans saved.2.1
end WNear.Proofs.AllocatePositive
