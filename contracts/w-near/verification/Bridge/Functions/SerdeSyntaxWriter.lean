import Bridge.Functions.SerdeSyntaxAdapter

namespace WNear.Binary.SerdeSyntax
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters WNear.Binary.SerdeActualSink
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Empty dangling String bytes and spare capacity own no memory; heap ownership is retained. -/
theorem empty_sbuf (n maxP hl F : Nat) (live : List (Nat × Nat)) :
    AllocInv.heapInv (GF := GF) n maxP hl live F ⊢ ScratchGrow.sbuf n maxP hl live F 1 0 [] := by
  iintro Hh
  iunfold ScratchGrow.sbuf
  simp only [List.length_nil, UInt32.toNat_zero, Nat.sub_zero, Nat.add_zero, ite_true]
  iframe Hh
  isplitr
  · ipureintro; decide
  isplitr
  · iapply ScratchGrow.memBytes_nil
  iexists ([] : List UInt8)
  isplitr
  · ipureintro; rfl
  iapply ScratchGrow.memBytes_nil

/-- Static first-writer instance with the exact serde Debug frame and owned String output. -/
theorem f598_frame_syntax (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 21 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (b e tag idx pad : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (hb : 192 ≤ b.toNat) (hb80 : b.toNat + 80 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsb : sb.length = (syntaxSlice tag).2.toNat) (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗ A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗
      ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[13]! inst mi f598 Cg
        (fun args => iprop(⌜args = [.i32 (b + 40), .i32 (b + 56)]⌝ ∗ g ↦[wg] ⟨gt, .i32 b⟩ ∗
          VecFromElem.stk n (b.toNat - 192) 192 ∗ SerdeDebug.stringCells n (b + 40) 1 0 0 ∗
          SerdeDebug.firstErrorArg n b e ∗ SerdeDebug.firstErrorArgs n b pad ∗
          codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F))
        (fun _ => 60 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
          costEngine cfg F (b - 32 + 4) tag)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 b⟩ ∗
          VecFromElem.stk n (b.toNat - 192) 192 ∗
          ∃ p c l : UInt32, SerdeDebug.stringCells n (b + 40) p c l ∗
          SerdeDebug.firstErrorArg n b e ∗ SerdeDebug.firstErrorArgs n b pad ∗
          codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb p c l)) := by
  iintro ⟨#Hi, #F872, #F591, #F592, #F912, #F616, #Hk⟩
  have h32 : (b - 32).toNat = b.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h16 : (b + 16).toNat = b.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have h40 : (b + 40).toNat = b.toNat + 40 := by simp [UInt32.toNat_add]; omega
  have h52 : (b + 52).toNat = b.toNat + 52 := by simp [UInt32.toNat_add]; omega
  have h56 : (b + 56).toNat = b.toNat + 56 := by simp [UInt32.toNat_add]; omega
  have hslot : (1057784 : UInt32).toNat + 12 = 1057796 := rfl
  have ht130 : (130 : UInt32).toNat = 130 := rfl
  have ht126 : (126 : UInt32).toNat = 126 := rfl
  have hpp : (1057628 : UInt32).toNat = 1057628 := rfl
  iapply AllocFresh.MFunSpec_frame (Fr := iprop(True))
    (P := fun args => iprop(⌜args = [.i32 (b + 40), .i32 (b + 56)]⌝ ∗ g ↦[wg] ⟨gt, .i32 b⟩ ∗
      VecFromElem.stk n (b.toNat - 32) 32 ∗
      SerdeDebug.args24 n (b + 56) (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad)
        (VecFromElem.pair64 (b + 16) 1) ∗
      engineIn n ta (b - 32) (b + 40) idx (b + 16) (b + 52) e tag (A 578) (A 591) (A 616) maxP hl F live sb))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 b⟩ ∗
      VecFromElem.stk n (b.toNat - 32) 32 ∗
      SerdeDebug.args24 n (b + 56) (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad)
        (VecFromElem.pair64 (b + 16) 1) ∗
      engineOut n ta (b - 32) (b + 40) idx (b + 16) (b + 52) e tag (A 578) (A 591) (A 616) maxP hl F live sb))
  · intro args
    iintro ⟨%ha, Hg, Hs, HV, HArg, HA, HC, Hh⟩
    iunfold codeShared at HC
    icases HC with ⟨Tag, Hsrc, P0, P4, T126, Vt, T130, Hvt⟩
    iunfold SerdeDebug.firstErrorArg at HArg
    icases HArg with ⟨G0, G4, Desc⟩
    iunfold SerdeDebug.firstErrorArgs at HA
    icases VecFromElem.stk_split n (b.toNat - 192) 160 32 $$ Hs with ⟨Hs160, Hs32⟩
    iunfold engineIn, FmtWrite.pieceArg, syntaxPayload
    simp only [h32, h16, h52, hslot, ht130, ht126, hpp, Nat.add_assoc, Nat.reduceAdd]
    iframe Hg HV HA G0 G4 Desc Tag Hsrc P0 P4 T126 Vt T130 Hvt
    isplitr
    · ipureintro; exact ha
    isplitl [Hs32]
    · iapply VecFromElem.stk_addr (by omega) $$ Hs32
    isplitl [Hs160]
    · iapply VecFromElem.stk_addr (by omega) $$ Hs160
    iapply empty_sbuf
    iexact Hh
  · intro args rs
    iintro ⟨-, %hrs, Hg, Hs32, HA, HO⟩
    iunfold engineOut at HO
    icases HO with ⟨Hs160, HPA, Vt, T130, Hvt, %p, %hl', %hhl, HV, Hb, HP⟩
    iunfold FmtWrite.pieceArg at HPA
    icases HPA with ⟨P0, P4, G0, G4, T126⟩
    iunfold syntaxPayload at HP
    icases HP with ⟨Desc, Tag, Hsrc⟩
    simp only [h32, h16, h52, hslot, ht130, ht126, hpp, Nat.add_assoc, Nat.reduceAdd]
    iframe Hg
    isplitr
    · ipureintro; exact hrs
    isplitl [Hs160 Hs32]
    · iapply VecFromElem.stk_join n (b.toNat - 192) 160 32
      isplitl [Hs160]
      · iapply VecFromElem.stk_addr (by omega) $$ Hs160
      iapply VecFromElem.stk_addr (by omega) $$ Hs32
    iexists p, ScratchGrow.capAfter 0 0 (syntaxSlice tag).2, UInt32.ofNat sb.length
    iframe HV
    iunfold SerdeDebug.firstErrorArg, SerdeDebug.firstErrorArgs, codeResult, codeShared
    simp only [h16, h52, Nat.add_assoc, Nat.reduceAdd]
    iframe HA G0 G4 Desc Tag Hsrc P0 P4 T126 Vt T130 Hvt
    iexists hl'
    iframe Hb
    ipureintro; exact ⟨trivial, trivial, hhl⟩
  iapply (f598_syntax cfg lim d inst mi A n g ta hm hd Cg gt b (b + 40) (b + 56) (b + 16)
    (b + 52) e tag idx pad maxP hl F live sb (by omega) he hlow hhigh hb (by omega) (by omega)
    (by omega) hsb hlk hsrc hr)
  iframe Hi F872 F591 F592 F912 F616 Hk

/-- The exact first-writer family is constructed for every padding word, with a concrete owned result. -/
theorem code_writer_instance (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 21 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp e tag idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (hsp : 272 ≤ sp.toNat) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsb : sb.length = (syntaxSlice tag).2.toNat) (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗ A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗
      ScratchGrow.sgCode n maxP inst mi A ⊢
      SerdeDebug.ErrorCodeStringWriteSpec (GF := GF) cfg lim d inst mi n g gt sp e 192
        (costCodeWriter cfg F sp tag) Cg
        iprop(codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F)
        (codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb) := by
  iintro ⟨#Hi, #F872, #F591, #F592, #F912, #F616, #Hk⟩
  have hlt := sp.toNat_lt
  have h80 : (sp - 80).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iunfold SerdeDebug.ErrorCodeStringWriteSpec
  iintro %pad
  unfold costCodeWriter
  iapply (f598_frame_syntax cfg lim d inst mi A n g ta hm hd Cg gt (sp - 80) e tag idx pad maxP hl F live sb
    (by omega) (by omega) he hlow hhigh hsb hlk hsrc hr)
  iframe Hi F872 F591 F592 F912 F616 Hk

/-- The concrete static writer retains additional owned error-box and caller resources through every padding choice. -/
theorem code_writer_instance_framed (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 21 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp e tag idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8) (U : IProp GF)
    (hsp : 272 ≤ sp.toNat) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsb : sb.length = (syntaxSlice tag).2.toNat) (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗ A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗
      ScratchGrow.sgCode n maxP inst mi A ⊢
      SerdeDebug.ErrorCodeStringWriteSpec (GF := GF) cfg lim d inst mi n g gt sp e 192
        (costCodeWriter cfg F sp tag) Cg
        iprop(codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F ∗ U)
        (fun p c l => iprop(codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb p c l ∗ U)) := by
  iintro ⟨#Hi, #F872, #F591, #F592, #F912, #F616, #Hk⟩
  ihave #HS := code_writer_instance cfg lim d inst mi A n g ta hm hd Cg gt sp e tag idx maxP hl F live sb
    hsp he hlow hhigh hsb hlk hsrc hr $$ [Hi F872 F591 F592 F912 F616 Hk]
  · iframe Hi F872 F591 F592 F912 F616 Hk
  iunfold SerdeDebug.ErrorCodeStringWriteSpec at HS
  iunfold SerdeDebug.ErrorCodeStringWriteSpec
  iintro %pad
  ihave #Hpad := HS $$ %pad
  iapply AllocFresh.MFunSpec_frame (Fr := U)
    (P := fun args => iprop(⌜args = [.i32 (sp - 80 + 40), .i32 (sp - 80 + 56)]⌝ ∗
      g ↦[wg] ⟨gt, .i32 (sp - 80)⟩ ∗ VecFromElem.stk n ((sp - 80).toNat - 192) 192 ∗
      SerdeDebug.stringCells n (sp - 80 + 40) 1 0 0 ∗ SerdeDebug.firstErrorArg n (sp - 80) e ∗
      SerdeDebug.firstErrorArgs n (sp - 80) pad ∗ codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗
      AllocInv.heapInv n maxP hl live F))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 80)⟩ ∗
      VecFromElem.stk n ((sp - 80).toNat - 192) 192 ∗ ∃ p c l : UInt32,
      SerdeDebug.stringCells n (sp - 80 + 40) p c l ∗ SerdeDebug.firstErrorArg n (sp - 80) e ∗
      SerdeDebug.firstErrorArgs n (sp - 80) pad ∗
      codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb p c l))
  · intro args
    iintro ⟨%ha, Hg, Hs, HV, HArg, HA, HC, Hh, HU⟩
    iframe HU Hg Hs HV HArg HA HC Hh
    ipureintro; exact ha
  · intro args rs
    iintro ⟨HU, %hrs, Hg, Hs, %p, %c, %l, HV, HArg, HA, HQ⟩
    iframe Hg Hs
    isplitr
    · ipureintro; exact hrs
    iexists p, c, l
    dsimp only
    iframe HV HArg HA HQ HU
  iexact Hpad

end WNear.Binary.SerdeSyntax
