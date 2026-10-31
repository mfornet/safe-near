import Bridge.Functions.SerdeSyntaxWriter

namespace WNear.Binary.SerdeSyntax
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters WNear.Binary.SerdeActualSink
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Whole actual Debug for static ErrorCodes constructs its first writer; outer formatting and room remain explicit. -/
theorem f641_static_composed (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 22 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp desc fmt e tag idx ret : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (U : IProp GF) (T : UInt32 → UInt32 → UInt32 → Nat → List (Nat × Nat) → Nat → IProp GF) (K913 : Nat)
    (hsp : 272 ≤ sp.toNat) (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsb : sb.length = (syntaxSlice tag).2.toNat) (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 598 ↪[wf] FuncInst.wasm types[13]! inst f598 ∗
      A 610 ↪[wf] FuncInst.wasm types[0]! inst f610 ∗ A 725 ↪[wf] FuncInst.wasm types[31]! inst f725 ∗
      A 913 ↪[wf] FuncInst.wasm types[13]! inst f913 ∗ A 599 ↪[wf] FuncInst.wasm types[0]! inst f599 ∗
      A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ∗ DropVec.dropCode inst mi A ∗
      A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗ A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗
      A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗ A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗ ScratchGrow.sgCode n maxP inst mi A ∗
      (∀ p : UInt32, ∀ c : UInt32, ∀ l : UInt32,
        SerdeDebug.ErrorEnvelopeWriteSpec cfg lim (d + 1) inst mi n g gt (sp - 80) fmt e p c l ret 192 K913 Cg
          iprop(codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb p c l ∗ U)
          iprop(∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            SerdeDebug.stringHeap n maxP len live F p c ∗ T p c l len live F)) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f641 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 272) 272 ∗ n ↦[i32][ desc.toNat ] e ∗
          codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F ∗ U))
        (fun _ => 700 * cfg.regularOpCost + costCodeWriter cfg F sp tag + K913)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 272) 272 ∗ n ↦[i32][ desc.toNat ] e ∗
          ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            SerdeDebug.stringHeapFreed n maxP len live F p c ∗ T p c l len live F)) := by
  iintro ⟨#Hi, #F598, #F610, #F725, #F913, #F599, #F601, #HD,
    #F872, #F591, #F592, #F912, #F616, #Hk, #S913⟩
  ihave #S598 := code_writer_instance_framed cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt
    sp e tag idx maxP hl F live sb U hsp he hlow hhigh hsb hlk hsrc hr $$ [Hi F872 F591 F592 F912 F616 Hk]
  · iframe Hi F872 F591 F592 F912 F616 Hk
  iapply (SerdeDebug.f641_composed cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt
    sp desc fmt e ret 192 maxP (by simpa using hsp) hdesc
    iprop(codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F ∗ U)
    (fun p c l => iprop(codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb p c l ∗ U))
    T (costCodeWriter cfg F sp tag) K913)
  iframe Hi F598 F610 F725 F913 F599 F601 HD S598 S913

/-- Actual dynamic serde Debug dispatch uses the checked static first writer and whole body. -/
theorem f882_static_composed (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp desc fmt e tag idx pp : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8)
    (U : IProp GF) (T : UInt32 → UInt32 → UInt32 → Nat → List (Nat × Nat) → Nat → IProp GF) (K913 : Nat)
    (hsp : 272 ≤ sp.toNat) (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hpp : pp.toNat + 8 ≤ 2 ^ 32) (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hsb : sb.length = (syntaxSlice tag).2.toNat) (hlk : (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP 0 0 (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 641 ↪[wf] FuncInst.wasm types[13]! inst f641 ∗
      A 598 ↪[wf] FuncInst.wasm types[13]! inst f598 ∗ A 610 ↪[wf] FuncInst.wasm types[0]! inst f610 ∗
      A 725 ↪[wf] FuncInst.wasm types[31]! inst f725 ∗ A 913 ↪[wf] FuncInst.wasm types[13]! inst f913 ∗
      A 599 ↪[wf] FuncInst.wasm types[0]! inst f599 ∗ A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ∗
      DropVec.dropCode inst mi A ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      A 591 ↪[wf] FuncInst.wasm types[13]! inst f591 ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗ A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗
      ScratchGrow.sgCode n maxP inst mi A ∗
      (∀ p : UInt32, ∀ c : UInt32, ∀ l : UInt32,
        SerdeDebug.ErrorEnvelopeWriteSpec cfg lim (d + 2) inst mi n g gt (sp - 80) fmt e p c l 0 192 K913 Cg
          iprop(codeResult n ta e tag idx (A 578) (A 591) (A 616) maxP hl F live sb p c l ∗ U)
          iprop(∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            SerdeDebug.stringHeap n maxP len live F p c ∗ T p c l len live F)) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f882 Cg
        (fun args => iprop(⌜args = [.i32 pp, .i32 fmt]⌝ ∗
          n ↦[i32][ pp.toNat ] desc ∗ n ↦[i32][ pp.toNat + 4 ] 1049036 ∗
          n ↦[i32][ 1049048 ] 12 ∗ ta ↦[wt][ 12 ] Ref.func (A 641) ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ VecFromElem.stk n (sp.toNat - 272) 272 ∗ n ↦[i32][ desc.toNat ] e ∗
          codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F ∗ U))
        (fun _ => 719 * cfg.regularOpCost + costCodeWriter cfg F sp tag + K913)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[i32][ pp.toNat ] desc ∗ n ↦[i32][ pp.toNat + 4 ] 1049036 ∗
          n ↦[i32][ 1049048 ] 12 ∗ ta ↦[wt][ 12 ] Ref.func (A 641) ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ VecFromElem.stk n (sp.toNat - 272) 272 ∗ n ↦[i32][ desc.toNat ] e ∗
          ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            SerdeDebug.stringHeapFreed n maxP len live F p c ∗ T p c l len live F)) := by
  iintro ⟨#Hi, #F641, #F598, #F610, #F725, #F913, #F599, #F601, #HD,
    #F872, #F591, #F592, #F912, #F616, #Hk, #S913⟩
  ihave S641 := f641_static_composed cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt
    sp desc fmt e tag idx 0 maxP hl F live sb U T K913 hsp hdesc he hlow hhigh hsb hlk hsrc hr
    $$ [Hi F598 F610 F725 F913 F599 F601 HD F872 F591 F592 F912 F616 Hk S913]
  · iframe Hi F598 F610 F725 F913 F599 F601 HD F872 F591 F592 F912 F616 Hk S913
  have H := PanicDebug.f882_serde_error_delegate (GF := GF) cfg lim d type htype inst mi A n g ta hm
    (by omega) Cg pp desc fmt (700 * cfg.regularOpCost + costCodeWriter cfg F sp tag + K913)
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ VecFromElem.stk n (sp.toNat - 272) 272 ∗ n ↦[i32][ desc.toNat ] e ∗
      codeShared n ta e tag idx (A 578) (A 591) (A 616) sb ∗ AllocInv.heapInv n maxP hl live F ∗ U)
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ VecFromElem.stk n (sp.toNat - 272) 272 ∗ n ↦[i32][ desc.toNat ] e ∗
      ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
        SerdeDebug.stringHeapFreed n maxP len live F p c ∗ T p c l len live F) hpp
  have hc : 19 * cfg.regularOpCost + (700 * cfg.regularOpCost + costCodeWriter cfg F sp tag + K913) =
      719 * cfg.regularOpCost + costCodeWriter cfg F sp tag + K913 := by omega
  rw [hc] at H
  iapply H
  iunfold PanicDebug.SerdeErrorDebugSpec
  iframe Hi F641 S641

end WNear.Binary.SerdeSyntax
