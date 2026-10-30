import Bridge.Functions.BalanceOf297ParserFixedCompose
import Bridge.Functions.FromSliceEsc

/-! Carry the copied-string parser's concrete allocator bounds into balance execution. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endFreeBound growthPages)
open WNear.Binary.SerdeScratchValueDrop (cleanValue)

/-- Maximum pages consumed by the copied parser result, including its owned value allocation. -/
def copiedParserPages (bs : List UInt8) (q : Nat) (a : WNear.AccountId) : Nat :=
  growthPages 0 0 (appendChunks (bs.drop q) []) +
    (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat a.val.toUTF8.toList.length)) 1).toNat

/-- The exact free-list bound recorded by copied-string parser cleanup. -/
def copiedParserFree (bs : List UInt8) (q F : Nat) : Nat :=
  max (endFreeBound F 0 0 (appendChunks (bs.drop q) [])) 1 + 1

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem heap_alignment (n maxP len F : Nat) (live : List (Nat × Nat)) :
    heapInv (GF := GF) n maxP len live F ⊢ ⌜len % 65536 = 0⌝ ∗ heapInv n maxP len live F := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hw, hl⟩, Hh, Hl, Hm, Hcells⟩
  isplitr
  · ipureintro; exact hl ▸ hw.len_al
  iunfold heapInv
  iexists M
  iframe Hh Hl Hm Hcells
  ipureintro; exact ⟨hw, hl⟩

/-- Parser growth plus six reserved pages gives the exact result heap the required balance room. -/
theorem copied_result_room (n hl F : Nat) (live : List (Nat × Nat)) (out p c L : UInt32)
    (bs : List UInt8) (q : Nat) (a : WNear.AccountId)
    (hroom : HeapRoomK (copiedParserPages bs q a + 6) hl 2048) :
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
      n ↦[i32][ out.toNat + 12 ] L ∗ cleanValue (GF := GF) n 2048 hl live F 0 bs
        a.val.toUTF8.toList q p c L ⊢
    ∃ hl', ⌜HeapRoomK 6 hl' 2048⌝ ∗ okAtFixed n out a live hl' (copiedParserFree bs q F) := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hsize := Wasm.ByteEncoding.string_utf8_length a.val
  have hm : (UInt32.ofNat a.val.toUTF8.toList.length).toNat = a.val.toUTF8.toList.length := by
    change a.val.toUTF8.toList.length % 2 ^ 32 = a.val.toUTF8.toList.length
    exact Nat.mod_eq_of_lt (by omega)
  iintro ⟨O0, O4, O8, O12, Hclean⟩
  iunfold cleanValue at Hclean
  icases Hclean with ⟨%⟨hc, hL, hp⟩, Hb, %hl', %F', %⟨hlow, hhigh, hF⟩, Hheap⟩
  subst hc hL F'
  ihave Hheap := heap_alignment n 2048 hl' _ _ $$ Hheap
  icases Hheap with ⟨%hal, Hheap⟩
  have hr : HeapRoomK 6 hl' 2048 := by
    obtain ⟨ha, hp0, hmax, h32⟩ := hroom
    unfold HeapRoomK at *
    unfold copiedParserPages at hmax h32
    refine ⟨hal, by omega, by omega, by omega⟩
  iexists hl'
  isplitr
  · ipureintro; exact hr
  iunfold okAtFixed
  rw [← hsize]
  iexists p, UInt32.ofNat a.val.toUTF8.toList.length
  isplitr
  · ipureintro; exact ⟨hp, by rw [hm]⟩
  unfold copiedParserFree
  iframe O0 O4 O8 O12 Hb Hheap
  rw [hm, Nat.sub_self]
  iunfold block
  iexists ([] : List UInt8)
  isplitr
  · ipureintro; rfl
  iapply ScratchGrow.memBytes_nil
end Spec
end WNear.Binary.BalanceOf297AbsentCall
