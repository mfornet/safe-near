import Bridge.Functions.SerdeSyntaxResources

namespace WNear.Binary.SerdeSyntax
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters WNear.Binary.SerdeActualSink
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- The actual empty first format piece preserves the dangling empty String and heap exactly. -/
theorem f616_empty (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 16 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s dd vec src idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (hs : 112 ≤ s.toNat)
    (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f616 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 src, .i32 0]⌝ ∗
          stringState n g ta gt s dd vec 1 0 idx (A 578) maxP hl F live []))
        (fun _ => 36 * cfg.regularOpCost + ScratchGrow.costExt cfg F 0 0 0)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          stringState n g ta gt s dd vec 1 0 idx (A 578) maxP hl F live [])) := by
  iintro ⟨#Hi, #Hk⟩
  iapply AllocFresh.MFunSpec_frame (Fr := iprop(True))
    (P := fun args => iprop(⌜args = [.i32 dd, .i32 src, .i32 0]⌝ ∗
      stringState n g ta gt s dd vec 1 0 idx (A 578) maxP hl F live [] ∗
      n ↦[wms][ src.toNat ] ([] : List UInt8)))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
      ⌜ScratchGrow.hlAfter hl hl' 0 0 0⌝ ∗
      stringState n g ta gt s dd vec p (ScratchGrow.capAfter 0 0 0) idx (A 578) maxP hl'
        (ScratchGrow.fAfter F 0 0 0) live ([] ++ []) ∗ n ↦[wms][ src.toNat ] ([] : List UInt8)))
  · intro args
    iintro ⟨%ha, Hs⟩
    iframe Hs
    isplitr
    · ipureintro; exact ha
    iapply ScratchGrow.memBytes_nil
  · intro args rs
    iintro ⟨-, %hrs, %p, %hl', %hhl, HS, -⟩
    have hfit : ScratchGrow.fits 0 0 0 := by simp [ScratchGrow.fits]
    simp only [ScratchGrow.hlAfter, hfit, if_true] at hhl
    subst hl'
    isimp only [ScratchGrow.capAfter, ScratchGrow.fAfter, hfit, if_true, List.nil_append] at HS
    iunfold stringState at HS
    icases HS with ⟨DD, Hg, Hs, Hvt, V0, V4, V8, Hb⟩
    icases ScratchGrow.sbuf_pure $$ Hb with ⟨%hbuf, Hb⟩
    have hp : p = 1 := hbuf.2.2.2 rfl
    subst p
    isplitr
    · ipureintro; exact hrs
    iunfold stringState
    iframe DD Hg Hs Hvt V0 V4 V8 Hb
  iapply (f616_append cfg lim d inst mi A n g ta hm hd Cg gt s dd vec 1 0 src 0 idx maxP hl F live
    [] [] hs hdd hvec (by decide) (by decide) rfl (by have := src.toNat_lt; simpa using this.le)
    (by simp [ScratchGrow.roomRes, ScratchGrow.fits]))
  iframe Hi Hk

/-- Empty-piece call framed by actual static ErrorCode payload ownership, with one global cell. -/
theorem f616_empty_framed (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 16 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s dd vec src idx desc e tag : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (hs : 112 ≤ s.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f616 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 src, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stringBody n ta s dd vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb))
        (fun _ => 36 * cfg.regularOpCost + ScratchGrow.costExt cfg F 0 0 0)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stringBody n ta s dd vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb)) := by
  iintro ⟨#Hi, #Hk⟩
  iapply AllocFresh.MFunSpec_frame (Fr := syntaxPayload n desc e tag sb)
    (P := fun args => iprop(⌜args = [.i32 dd, .i32 src, .i32 0]⌝ ∗
      stringState n g ta gt s dd vec 1 0 idx (A 578) maxP hl F live []))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
      stringState n g ta gt s dd vec 1 0 idx (A 578) maxP hl F live []))
  · intro args
    iintro ⟨%ha, Hg, HS, HP⟩
    iunfold stringBody at HS
    icases HS with ⟨DD, Hs, Hvt, V0, V4, V8, Hb⟩
    iunfold stringState
    iframe HP Hg DD Hs Hvt V0 V4 V8 Hb
    ipureintro; exact ha
  · intro args rs
    iintro ⟨HP, %hrs, HS⟩
    iunfold stringState at HS
    icases HS with ⟨DD, Hg, Hs, Hvt, V0, V4, V8, Hb⟩
    iunfold stringBody
    iframe HP Hg DD Hs Hvt V0 V4 V8 Hb
    ipureintro; exact hrs
  iapply (f616_empty cfg lim d inst mi A n g ta hm hd Cg gt s dd vec src idx maxP hl F live hs hdd hvec)
  iframe Hi Hk

open WNear.Binary.SerdeErrorWriters

/-- The actual static ErrorCode formatter satisfies the argument interface expected by function 872. -/
theorem f591_argument (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 19 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (desc e fmt tag s dd vec idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21) (hf : fmt.toNat + 32 ≤ 2 ^ 32)
    (hs : 112 ≤ s.toNat) (hsb : sb.length = (syntaxSlice tag).2.toNat)
    (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[13]! inst mi f591 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          FmtPad.fmtr n ta fmt dd 1057784 130 (A 616) ∗
          stringBody n ta s dd vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb))
        (fun _ => costArg cfg F dd tag)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          FmtPad.fmtr n ta fmt dd 1057784 130 (A 616) ∗
          writtenBody n ta s dd vec idx desc e tag (A 578) maxP hl F live sb)) := by
  iintro ⟨#Hi, #F592, #F912, #F616, #Hk⟩
  have hv : (1057784 : UInt32).toNat + 12 = 1057796 := rfl
  have hi : (130 : UInt32).toNat = 130 := rfl
  iapply AllocFresh.MFunSpec_frame
    (Fr := iprop(n ↦[i32][ fmt.toNat ] 0 ∗ n ↦[i32][ fmt.toNat + 8 ] 0))
    (P := fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗
      n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
      n ↦[i32][ fmt.toNat + 24 ] dd ∗ n ↦[i32][ fmt.toNat + 28 ] 1057784 ∗
      n ↦[i32][ 1057796 ] 130 ∗ ta ↦[wt][ 130 ] Ref.func (A 616) ∗
      stringState n g ta gt s dd vec 1 0 idx (A 578) maxP hl F live [] ∗
      n ↦[wms][ (syntaxSlice tag).1.toNat ] sb))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
      n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
      n ↦[i32][ fmt.toNat + 24 ] dd ∗ n ↦[i32][ fmt.toNat + 28 ] 1057784 ∗
      n ↦[i32][ 1057796 ] 130 ∗ ta ↦[wt][ 130 ] Ref.func (A 616) ∗
      ∃ (p : UInt32) (hl' : Nat),
      ⌜ScratchGrow.hlAfter hl hl' 0 0 (syntaxSlice tag).2⌝ ∗
      stringState n g ta gt s dd vec p (ScratchGrow.capAfter 0 0 (syntaxSlice tag).2) idx
        (A 578) maxP hl' (ScratchGrow.fAfter F 0 0 (syntaxSlice tag).2) live ([] ++ sb) ∗
      n ↦[wms][ (syntaxSlice tag).1.toNat ] sb))
  · intro args
    iintro ⟨%ha, Hg, HF, HS, HP⟩
    iunfold FmtPad.fmtr at HF
    isimp only [hv, hi] at HF
    icases HF with ⟨F0, F8, F24, F28, Vt, HT⟩
    iunfold stringBody at HS
    icases HS with ⟨DD, Hs, Hvt, V0, V4, V8, Hb⟩
    iunfold syntaxPayload at HP
    icases HP with ⟨Desc, Tag, Hsrc⟩
    iunfold stringState
    iframe F0 F8 Hg F24 F28 Vt HT DD Hs Hvt V0 V4 V8 Hb Desc Tag Hsrc
    ipureintro; exact ha
  · intro args rs
    iintro ⟨⟨F0, F8⟩, %hrs, Desc, Tag, F24, F28, Vt, HT, %p, %hl', %hhl, HS, Hsrc⟩
    iunfold stringState at HS
    icases HS with ⟨DD, Hg, Hs, Hvt, V0, V4, V8, Hb⟩
    iunfold FmtPad.fmtr, writtenBody, stringBody, syntaxPayload
    simp only [hv, hi, List.nil_append]
    iframe Hg F0 F8 F24 F28 Vt HT
    isplitr
    · ipureintro; exact hrs
    iexists p, hl'
    iframe DD Hs Hvt V0 V4 V8 Hb Desc Tag Hsrc
    ipureintro; exact hhl
  unfold costArg
  iapply (f591_syntax_append cfg lim d types[13]! rfl inst mi A n g ta hm hd Cg gt
    desc e fmt tag s dd vec 1 0 idx maxP hl F live [] sb hdesc he hlow hhigh hf hs hsb hdd hvec
    (by decide) (by simpa using hlk) hsrc hr)
  iframe Hi F592 F912 F616 Hk

/-- The actual first formatting engine writes its empty piece and then all static ErrorCode bytes through function 616. -/
theorem f872_syntax (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 20 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp dd vec ar argp desc e tag idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsp : 160 ≤ sp.toNat) (hsb : sb.length = (syntaxSlice tag).2.toNat)
    (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (har : ar.toNat + 24 ≤ 2 ^ 32) (hargp : argp.toNat + 8 ≤ 2 ^ 32)
    (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗
      A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 1057784, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 48) 48 ∗ FmtWrite.argsAt n ar 1057628 argp ∗
          FmtWrite.pieceArg n ta 1057628 1057628 0 argp desc 126 (A 591) ∗
          n ↦[i32][ (1057784 : UInt32).toNat + 12 ] 130 ∗ ta ↦[wt][ (130 : UInt32).toNat ] Ref.func (A 616) ∗
          stringBody n ta (sp - 48) dd vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb))
        (fun _ => costEngine cfg F dd tag)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 48) 48 ∗ FmtWrite.argsAt n ar 1057628 argp ∗
          FmtWrite.pieceArg n ta 1057628 1057628 0 argp desc 126 (A 591) ∗
          n ↦[i32][ (1057784 : UInt32).toNat + 12 ] 130 ∗ ta ↦[wt][ (130 : UInt32).toNat ] Ref.func (A 616) ∗
          writtenBody n ta (sp - 48) dd vec idx desc e tag (A 578) maxP hl F live sb)) := by
  iintro ⟨#Hi, #F591, #F592, #F912, #F616, #Hk⟩
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf : (sp - 48 + 8).toNat + 32 ≤ 2 ^ 32 := by simp [UInt32.toNat_add, h48]; omega
  ihave #Sa := f616_empty_framed (GF := GF) cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt
    (sp - 48) dd vec 1057628 idx desc e tag maxP hl F live sb (by omega) hdd hvec $$ [Hi Hk]
  · iframe Hi Hk
  ihave #Sb := f591_argument (GF := GF) cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt
    desc e (sp - 48 + 8) tag (sp - 48) dd vec idx maxP hl F live sb hdesc he hlow hhigh hf
    (by omega) hsb hdd hvec hlk hsrc hr $$ [Hi F592 F912 F616 Hk]
  · iframe Hi F592 F912 F616 Hk
  unfold costEngine
  iapply (FmtWrite.f872_one cfg lim d types[15]! rfl inst mi A n g ta hm (by omega) Cg gt
    sp dd 1057784 ar 1057628 argp 1057628 0 desc 126 130 (by omega) (by decide) har (by decide) hargp
    (A 616) (A 591) f616 f591
    iprop(stringBody n ta (sp - 48) dd vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb)
    iprop(stringBody n ta (sp - 48) dd vec 1 0 idx (A 578) maxP hl F live [] ∗ syntaxPayload n desc e tag sb)
    (writtenBody n ta (sp - 48) dd vec idx desc e tag (A 578) maxP hl F live sb)
    (36 * cfg.regularOpCost + ScratchGrow.costExt cfg F 0 0 0) (costArg cfg F dd tag))
  iframe Hi F616 F591 Sa Sb

/-- The copied Arguments keep their unused padding word when exposed to the concrete formatting engine. -/
theorem args24_argsAt (n : Nat) (ar pp argp pad : UInt32) :
    SerdeDebug.args24 (GF := GF) n ar (VecFromElem.pair64 pp 1) (VecFromElem.pair64 0 pad)
      (VecFromElem.pair64 argp 1) ⊣⊢
      FmtWrite.argsAt n ar pp argp ∗ n ↦[i32][ ar.toNat + 12 ] pad := by
  constructor
  · iintro HA
    iunfold SerdeDebug.args24 at HA
    icases HA with ⟨A0, A8, A16⟩
    isimp only [VecFromElem.storeBytes_pair64] at A0 A8 A16
    icases BorshFT.splitB (bytes32 pp) (bytes32 1) rfl $$ A0 with ⟨P0, P4⟩
    icases BorshFT.splitB (bytes32 0) (bytes32 pad) rfl $$ A8 with ⟨P8, P12⟩
    icases BorshFT.splitB (bytes32 argp) (bytes32 1) rfl $$ A16 with ⟨P16, P20⟩
    iunfold FmtWrite.argsAt
    simp only [bytes32_length]
    simp only [show ar.toNat + 8 + 4 = ar.toNat + 12 by omega,
      show ar.toNat + 16 + 4 = ar.toNat + 20 by omega]
    iframe P0 P4 P8 P12 P16 P20
  · iintro ⟨HA, Pad⟩
    iunfold FmtWrite.argsAt at HA
    icases HA with ⟨P0, P4, P8, P16, P20⟩
    iunfold SerdeDebug.args24
    simp only [VecFromElem.storeBytes_pair64]
    isplitl [P0 P4]
    · iapply BorshFT.joinB (bytes32 pp) (bytes32 1) rfl
      simp only [bytes32_length]
      iframe P0 P4
    isplitl [P8 Pad]
    · iapply BorshFT.joinB (bytes32 0) (bytes32 pad) rfl
      simp only [bytes32_length]
      iframe P8
      iapply AllocNewCell.memBytes_addr (by omega) $$ Pad
    iapply BorshFT.joinB (bytes32 argp) (bytes32 1) rfl
    simp only [bytes32_length]
    iframe P16
    iapply AllocNewCell.memBytes_addr (by omega) $$ P20

end WNear.Binary.SerdeSyntax
