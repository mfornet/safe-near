import Bridge.Functions.SerdeSyntaxCalls

namespace WNear.Binary.SerdeSyntax
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters WNear.Binary.SerdeActualSink
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- The actual first engine accepts the retained three-pair Arguments representation and arbitrary padding. -/
theorem f872_copied (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 20 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s vec argp desc e tag idx pad : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hs : 160 ≤ s.toNat) (hs32 : s.toNat + 32 ≤ 2 ^ 32)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hargp : argp.toNat + 8 ≤ 2 ^ 32)
    (hsb : sb.length = (syntaxSlice tag).2.toNat) (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗
      A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗ A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 (s + 4), .i32 1057784, .i32 (s + 8)]⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ s.toNat + 4 ] vec ∗
          SerdeDebug.args24 n (s + 8) (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad)
            (VecFromElem.pair64 argp 1) ∗
          engineIn n ta s vec idx argp desc e tag (A 578) (A 591) (A 616) maxP hl F live sb))
        (fun _ => costEngine cfg F (s + 4) tag)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ s.toNat + 4 ] vec ∗
          SerdeDebug.args24 n (s + 8) (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad)
            (VecFromElem.pair64 argp 1) ∗
          engineOut n ta s vec idx argp desc e tag (A 578) (A 591) (A 616) maxP hl F live sb)) := by
  iintro ⟨#Hi, #F591, #F592, #F912, #F616, #Hk⟩
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h4 : (s + 4).toNat = s.toNat + 4 := by simp [UInt32.toNat_add]; omega
  have h8 : (s + 8).toNat = s.toNat + 8 := by simp [UInt32.toNat_add]; omega
  iapply AllocFresh.MFunSpec_frame (Fr := iprop(n ↦[i32][ (s + 8).toNat + 12 ] pad))
    (P := fun args => iprop(⌜args = [.i32 (s + 4), .i32 1057784, .i32 (s + 8)]⌝ ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ VecFromElem.stk n (s.toNat - 48) 48 ∗ FmtWrite.argsAt n (s + 8) 1057628 argp ∗
      FmtWrite.pieceArg n ta 1057628 1057628 0 argp desc 126 (A 591) ∗
      n ↦[i32][ (1057784 : UInt32).toNat + 12 ] 130 ∗ ta ↦[wt][ (130 : UInt32).toNat ] Ref.func (A 616) ∗
      stringBody n ta (s - 48) (s + 4) vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      VecFromElem.stk n (s.toNat - 48) 48 ∗ FmtWrite.argsAt n (s + 8) 1057628 argp ∗
      FmtWrite.pieceArg n ta 1057628 1057628 0 argp desc 126 (A 591) ∗
      n ↦[i32][ (1057784 : UInt32).toNat + 12 ] 130 ∗ ta ↦[wt][ (130 : UInt32).toNat ] Ref.func (A 616) ∗
      writtenBody n ta (s - 48) (s + 4) vec idx desc e tag (A 578) maxP hl F live sb))
  · intro args
    iintro ⟨%ha, Hg, DD, HA, HI⟩
    icases (args24_argsAt n (s + 8) 1057628 argp pad).1 $$ HA with ⟨HA, Pad⟩
    iunfold engineIn at HI
    icases HI with ⟨Hs, HPA, Vt, HT, Hvt, HV, Hb, HP⟩
    icases VecFromElem.stk_split n (s.toNat - 160) 112 48 $$ Hs with ⟨Hs112, Hs48⟩
    iunfold SerdeDebug.stringCells at HV
    icases HV with ⟨V0, V4, V8⟩
    iunfold stringBody
    simp only [h4, h48]
    iframe Pad Hg DD HA HPA Vt HT Hvt V0 V4 V8 Hb HP
    isplitr
    · ipureintro; exact ha
    isplitl [Hs48]
    · iapply VecFromElem.stk_addr (by omega) $$ Hs48
    iapply VecFromElem.stk_addr (by omega) $$ Hs112
  · intro args rs
    iintro ⟨Pad, %hrs, Hg, Hs48, HA, HPA, Vt, HT, HW⟩
    iunfold writtenBody at HW
    icases HW with ⟨%p, %hl', %hhl, HS, HP⟩
    iunfold stringBody at HS
    icases HS with ⟨DD, Hs112, Hvt, V0, V4, V8, Hb⟩
    ihave HA := (args24_argsAt n (s + 8) 1057628 argp pad).2 $$ [HA Pad]
    · iframe HA Pad
    iunfold engineOut, SerdeDebug.stringCells
    simp only [h4, h48]
    iframe Hg DD HA HPA Vt HT Hvt
    isplitr
    · ipureintro; exact hrs
    isplitl [Hs112 Hs48]
    · iapply VecFromElem.stk_join n (s.toNat - 160) 112 48
      isplitl [Hs112]
      · iapply VecFromElem.stk_addr (by omega) $$ Hs112
      iapply VecFromElem.stk_addr (by omega) $$ Hs48
    iexists p, hl'
    iframe V0 V4 V8 Hb HP
    ipureintro; exact hhl
  iapply (f872_syntax cfg lim d inst mi A n g ta hm hd Cg gt s (s + 4) vec (s + 8) argp desc e tag idx
    maxP hl F live sb hdesc he hlow hhigh hs hsb (by omega) hvec (by omega) hargp hlk hsrc hr)
  iframe Hi F591 F592 F912 F616 Hk

/-- Actual String::write_fmt instantiates its engine from checked static ErrorCode and String sink behavior. -/
theorem f598_syntax (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 21 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp vec ar argp desc e tag idx pad : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsp : 192 ≤ sp.toNat) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (har : ar.toNat + 24 ≤ 2 ^ 32)
    (hargp : argp.toNat + 8 ≤ 2 ^ 32) (hsb : sb.length = (syntaxSlice tag).2.toNat)
    (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗ A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗
      ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[13]! inst mi f598 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 32) 32 ∗
          SerdeDebug.args24 n ar (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad)
            (VecFromElem.pair64 argp 1) ∗
          engineIn n ta (sp - 32) vec idx argp desc e tag (A 578) (A 591) (A 616) maxP hl F live sb))
        (fun _ => 60 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
          costEngine cfg F (sp - 32 + 4) tag)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 32) 32 ∗
          SerdeDebug.args24 n ar (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad)
            (VecFromElem.pair64 argp 1) ∗
          engineOut n ta (sp - 32) vec idx argp desc e tag (A 578) (A 591) (A 616) maxP hl F live sb)) := by
  iintro ⟨#Hi, #F872, #F591, #F592, #F912, #F616, #Hk⟩
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave HS := f872_copied (GF := GF) cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) vec argp desc e tag idx pad maxP hl F live sb hdesc he hlow hhigh (by omega)
    (by omega) hvec hargp hsb hlk hsrc hr $$ [Hi F591 F592 F912 F616 Hk]
  · iframe Hi F591 F592 F912 F616 Hk
  iapply (SerdeDebug.f598_delegate cfg lim d types[13]! rfl inst mi A n g ta hm (by omega) Cg gt
    sp vec ar (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad) (VecFromElem.pair64 argp 1)
    0 (costEngine cfg F (sp - 32 + 4) tag)
    (engineIn n ta (sp - 32) vec idx argp desc e tag (A 578) (A 591) (A 616) maxP hl F live sb)
    (engineOut n ta (sp - 32) vec idx argp desc e tag (A 578) (A 591) (A 616) maxP hl F live sb)
    (by omega) har)
  iunfold SerdeDebug.StringFmtEngineSpec
  iframe Hi F872 HS

end WNear.Binary.SerdeSyntax
