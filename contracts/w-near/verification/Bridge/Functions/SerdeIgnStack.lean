import Bridge.Functions.SerdeIgnPush
import Bridge.Functions.SerdeIgnFrameStack
import Bridge.Functions.SerdeDeStr

/-!
# Scratch frames in the pure ignored machine's order

`IgnoreModel` keeps the innermost saved frame first. The actual vector appends
and pops at its end, so `state` stores the reverse list. Clearing the vector
returns all formerly used bytes to its spare region without freeing its block.
-/

namespace WNear.Binary.SerdeIgnStack

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.ScratchGrow (sbuf capAfter fAfter hlAfter roomRes)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A descriptor and its allocation, with saved frames innermost first. -/
def state (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (vec p cap : UInt32)
    (frames : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
    n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat frames.length ∗ sbuf n maxP hl live F p cap frames.reverse)

/-- Clearing changes the used/spare partition only; the allocation and every live block remain. -/
theorem sbuf_clear {n maxP hl F : Nat} {live : List (Nat × Nat)} {p cap : UInt32} {bs : List UInt8} :
    sbuf (GF := GF) n maxP hl live F p cap bs ⊢ sbuf n maxP hl live F p cap [] := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%⟨hbl, hp, hpc, hz⟩, B, ⟨%junk, %hj, J⟩, Hheap⟩
  ihave BJ := BorshFT.joinB bs junk rfl $$ [B J]
  · iframe B J
  iunfold sbuf
  isplitr
  · ipureintro; exact ⟨by simp, hp, hpc, hz⟩
  isplitl []
  · iapply ScratchGrow.memBytes_nil
  iframe Hheap
  iexists bs ++ junk
  simp only [List.length_nil, Nat.add_zero, Nat.sub_zero]
  iframe BJ
  ipureintro; simp only [List.length_append]; omega

/-- The actual clear call (82, whose body is 343) retains the scratch allocation. -/
theorem f343_clear (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (vec p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (frames : List UInt8)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    A 674 ↪[wf] FuncInst.wasm types[14]! inst f674 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f343 Cg
        (fun args => iprop(⌜args = [.i32 vec]⌝ ∗ state n maxP hl live F vec p cap frames))
        (fun _ => 30 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ state n maxP hl live F vec p cap [])) := by
  have base := SerdeDeStr.f343_s (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg vec
    (UInt32.ofNat frames.length) hvec
  iintro #HC
  ihave #S := base $$ HC
  clear base
  iunfold MFunSpec at S
  iunfold MFunSpec
  imodintro
  iintro %args %R ⟨%ha, H⟩ Hc
  iunfold state at H
  icases H with ⟨D0, D4, D8, Hsb⟩
  iapply mwpInvoke_wand
  isplitl [D8 Hc]
  · iapply S $$ %args %R [D8] Hc
    dsimp only
    iframe D8
    ipureintro; exact ha
  isplit
  · iintro %rs ⟨Hc, %hrs, D8⟩
    dsimp only
    iframe Hc
    isplitr
    · ipureintro; exact hrs
    iunfold state
    ihave Hsb := sbuf_clear $$ Hsb
    simp only [List.length_nil, List.reverse_nil]
    iframe D0 D4 D8 Hsb
  · iintro Htrap; iexact Htrap

/-- Pushing the current frame is cons in the pure stack and append in the actual vector. -/
theorem f84_cons (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec p cap idx : UInt32) (b : UInt8) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (frames : List UInt8) (hs : 80 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap : cap.toNat < 2 ^ 27)
    (hlen : frames.length + 1 < 2 ^ 27) (hr : roomRes hl maxP cap (UInt32.ofNat frames.length) 1) :
    SerdeIgnReserve.code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f84 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 1, .i32 b.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        state n maxP hl live F vec p cap frames))
      (fun _ => SerdeIgnPush.cost cfg F cap frames.length)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p' : UInt32) (hl' : Nat),
        ⌜hlAfter hl hl' cap (UInt32.ofNat frames.length) 1⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        state n maxP hl' live (fAfter F cap (UInt32.ofNat frames.length) 1) vec p'
          (capAfter cap (UInt32.ofNat frames.length) 1) (b :: frames))) := by
  have hb : MemSet.byteOf b.toUInt32 = b := by simp [MemSet.byteOf]
  simpa only [state, List.length_reverse, List.length_cons, List.reverse_cons, hb] using
    (SerdeIgnPush.f84_some (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt s vec b.toUInt32
      p cap idx maxP hl F live frames.reverse hs hvec hcap (by simpa using hlen) (by simpa using hr))

/-- With no current frame to save, 84 preserves the represented stack and allocator. -/
theorem f84_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec p cap idx b : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (frames : List UInt8) (hs : 80 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    SerdeIgnReserve.code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f84 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 0, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        state n maxP hl live F vec p cap frames))
      (fun _ => 120 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗
        AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ state n maxP hl live F vec p cap frames)) := by
  iintro #HC
  iunfold SerdeIgnReserve.code at HC
  icases HC with ⟨-, #CW⟩
  iunfold VecGrow.waCode at CW
  icases CW with ⟨-, #CA⟩
  have hlt := s.toNat_lt
  iunfold MFunSpec
  imodintro
  iintro %args %R ⟨%ha, Hg, H80, Hvt, H⟩ Hc
  iunfold state at H
  icases H with ⟨D0, D4, D8, Hsb⟩
  icases ScratchGrow.sbuf_pure $$ Hsb with ⟨%⟨hlen, -⟩, Hsb⟩
  simp only [List.length_reverse] at hlen
  have hroom : (UInt32.ofNat frames.length).toNat ≤ cap.toNat := by simp; omega
  have base := SerdeIgnFrame.f84_none (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    s vec p (UInt32.ofNat frames.length) cap b (by omega) hvec hroom
  ihave #S := base $$ CA
  clear base
  iunfold MFunSpec at S
  icases VecFromElem.stk_split n (s.toNat - 80) 64 16 $$ H80 with ⟨Lo, H16⟩
  ihave H16 := VecFromElem.stk_addr (show s.toNat - 80 + 64 = s.toNat - 16 by omega) $$ H16
  iapply mwpInvoke_wand
  isplitl [Hg H16 D0 D4 D8 Hc]
  · iapply S $$ %args %R [Hg H16 D0 D4 D8] Hc
    dsimp only
    iframe Hg H16 D0 D4 D8
    ipureintro; exact ha
  isplit
  · iintro %rs ⟨Hc, %hrs, Hg, H16, D0, D4, D8⟩
    dsimp only
    iframe Hc Hg Hvt
    isplitr
    · ipureintro; exact hrs
    isplitl [Lo H16]
    · iapply VecFromElem.stk_join n (s.toNat - 80) 64 16
      rw [show s.toNat - 80 + 64 = s.toNat - 16 by omega]
      iframe Lo H16
    iunfold state
    iframe D0 D4 D8 Hsb
  · iintro Htrap; iexact Htrap

/-- A pop's flag, byte and remaining stack in machine order. -/
def popped (frames : List UInt8) : UInt8 × UInt8 × List UInt8 :=
  match frames with
  | [] => (0, 0, [])
  | b :: frames => (1, b, frames)

/-- The actual pop implements the pure stack's head/tail split, including the empty case. -/
theorem f85_pop (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec p cap : UInt32)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames : List UInt8) (b0 b1 : UInt8)
    (hout : out.toNat + 2 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f85 Cg
      (fun args => iprop(⌜args = [.i32 out, .i32 vec]⌝ ∗ state n maxP hl live F vec p cap frames ∗
        n ↦[wms][ out.toNat ] [b0] ∗ n ↦[wms][ out.toNat + 1 ] [b1]))
      (fun _ => 50 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ state n maxP hl live F vec p cap (popped frames).2.2 ∗
        n ↦[wms][ out.toNat ] [(popped frames).1] ∗ n ↦[wms][ out.toNat + 1 ] [(popped frames).2.1])) := by
  iunfold MFunSpec
  imodintro
  iintro %args %R ⟨%ha, H, O0, O1⟩ Hc
  iunfold state at H
  icases H with ⟨D0, D4, D8, Hsb⟩
  cases frames with
  | nil =>
    have base := SerdeIgnFrame.f85_empty (GF := GF) cfg lim d type htype inst mi n hn Cg out vec b0 b1 hout hvec
    ihave #S := base
    clear base
    iunfold MFunSpec at S
    iapply mwpInvoke_wand
    isplitl [D8 O0 O1 Hc]
    · iapply S $$ %args %R [D8 O0 O1]
      · dsimp only
        iframe D8 O0 O1
        ipureintro; exact ha
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; dsimp only; omega
    isplit
    · iintro %rs ⟨Hc, %hrs, D8, O0, O1⟩
      dsimp only
      simp only [popped]
      iframe Hc O0 O1
      isplitr
      · ipureintro; exact hrs
      iunfold state
      iframe D0 D4 D8 Hsb
    · iintro Htrap; iexact Htrap
  | cons b frames =>
    have base := SerdeIgnFrameStack.f85_nonempty (GF := GF) cfg lim d type htype inst mi n hn Cg out vec p cap
      maxP hl F live frames.reverse b b0 b1 hout hvec
    simp only [List.length_reverse] at base
    ihave #S := base
    clear base
    iunfold MFunSpec at S
    iapply mwpInvoke_wand
    isplitl [D0 D8 Hsb O0 O1 Hc]
    · iapply S $$ %args %R [D0 D8 Hsb O0 O1] Hc
      dsimp only
      simp only [List.length_cons, List.reverse_cons]
      iframe D0 D8 Hsb O0 O1
      ipureintro; exact ha
    isplit
    · iintro %rs ⟨Hc, %hrs, D0, D8, O0, O1, Hsb⟩
      dsimp only
      simp only [popped]
      iframe Hc O0 O1
      isplitr
      · ipureintro; exact hrs
      iunfold state
      iframe D0 D4 D8 Hsb
    · iintro Htrap; iexact Htrap

end Proof
end WNear.Binary.SerdeIgnStack
