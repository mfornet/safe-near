import Bridge.Functions.SerdeDebugFirst
import Bridge.Functions.SerdeDebugSecond
import Bridge.Functions.SerdeDebugCleanup

namespace WNear.Binary.SerdeDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr stk_intro stk_word)
open WNear.Binary.PanicHook (stk4_word)
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- Complete actual serde error Debug body: two formatting calls and concrete temporary cleanup.
Both exact writer contracts remain explicit; no formatting implementation is assumed proven. -/
theorem f641_composed (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp desc fmt e ret : UInt32) (S maxP : Nat) (hsp : S + 80 ≤ sp.toNat)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (P : IProp GF) (Q : UInt32 → UInt32 → UInt32 → IProp GF)
    (T : UInt32 → UInt32 → UInt32 → Nat → List (Nat × Nat) → Nat → IProp GF) (K598 K913 : Nat) :
    inst ↪[inst] mi ∗ A 598 ↪[wf] FuncInst.wasm types[13]! inst f598 ∗
      A 610 ↪[wf] FuncInst.wasm types[0]! inst f610 ∗ A 725 ↪[wf] FuncInst.wasm types[31]! inst f725 ∗
      A 913 ↪[wf] FuncInst.wasm types[13]! inst f913 ∗ A 599 ↪[wf] FuncInst.wasm types[0]! inst f599 ∗
      A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ∗ DropVec.dropCode inst mi A ∗
      ErrorCodeStringWriteSpec cfg lim (d + 1) inst mi n g gt sp e S K598 Cg P Q ∗
      (∀ p : UInt32, ∀ c : UInt32, ∀ l : UInt32,
        ErrorEnvelopeWriteSpec cfg lim (d + 1) inst mi n g gt (sp - 80) fmt e p c l ret S K913 Cg (Q p c l)
          iprop(∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeap n maxP len live F p c ∗ T p c l len live F)) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f641 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗ P))
        (fun _ => 700 * cfg.regularOpCost + K598 + K913)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗
          ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeapFreed n maxP len live F p c ∗ T p c l len live F)) := by
  iintro ⟨#Hi, #F598, #F610, #F725, #F913, #F599, #F601, #HD, #S598, #S913⟩
  have hlt := sp.toNat_lt
  have h80 : (sp - 80).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hrestore : sp - 80 + 80 = sp := UInt32.sub_add_cancel _ _
  have hframe : ({ locals := entryLocals f641 [.i32 desc, .i32 fmt], inst := inst, mi := mi } : Frame) =
      debugFrame inst mi desc fmt 0 0 := by
    simp [entryLocals, f641, ValType.default, debugFrame]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Desc, HP⟩
  subst hargs
  rw [hframe]
  have hcode : f641.body = f641.body.take 49 ++ (f641.body.drop 49).take 56 ++ f641.body.drop 105 := rfl
  rw [hcode, List.append_assoc]
  iapply mwpi_seq
  ihave Hc : credits Cg (100 * cfg.regularOpCost + K598 + (600 * cfg.regularOpCost + K913 + R)) $$ [Hc]
  · iapply BorrowMut.credits_le; iframe Hc; ipureintro; omega
  iapply (f641_first_format_exists cfg lim d inst mi A n g ta hm (by omega) Cg
    (600 * cfg.regularOpCost + K913 + R) gt sp desc fmt e 0 0 S hsp hdesc P Q K598 _)
  iframe Hi F598 S598 Hc Hg Hs Desc HP
  inext
  iintro %p %c %l ⟨Hc, Hg, Low, Pad0, Pad24, HC, HE, HA, Desc, HQ0⟩
  simp only [Post.mseq_normal]
  iapply mwpi_seq
  ihave Hc : credits Cg (200 * cfg.regularOpCost + K913 + (400 * cfg.regularOpCost + R)) $$ [Hc]
  · iapply BorrowMut.credits_le; iframe Hc; ipureintro; omega
  ispecialize S913 $$ %p %c %l
  iapply (f641_second_format cfg lim d inst mi A n g ta hm (by omega) Cg (400 * cfg.regularOpCost + R)
    gt (sp - 80) fmt e 0 S (by omega) (by omega) p c l ret (Q p c l)
    iprop(∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
      stringHeap n maxP len live F p c ∗ T p c l len live F) K913 _)
  iframe Hi F610 F725 F913 S913 Hc Hg Low Pad0 Pad24 HC HE HA HQ0
  inext
  iintro ⟨Hc, Hg, Low, Pad0, HC, W52, HA, HV, %len, %live, %F, Hheap, HT⟩
  simp only [Post.mseq_normal]
  iunfold stringHeap at Hheap
  icases Hheap with ⟨Hinv, Hb⟩
  iapply (f641_cleanup cfg lim d inst mi A n g ta hm hd Cg R gt (sp - 80) fmt e ret
    (VecFromElem.pair64 (e + 12) 3) S (by omega) (by omega) p c l maxP len F live (T p c l len live F) _)
  iframe HD F601 F599 Hc Hg Low Pad0 HC W52 HA HV Hinv Hb HT
  inext
  iintro ⟨Hc, Hg, Hs, Hinv, HT⟩
  simp only [hrestore]
  ihave Hs := stk_addr (show (sp - 80).toNat - S = sp.toNat - (S + 80) by omega) $$ Hs
  simp [Post.mfunc, htype]
  iframe Hc Hg Hs Desc
  iintro Hret
  iframe Hret
  iexists p, c, l, len, live, F
  iunfold stringHeapFreed
  iframe Hinv HT

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- Actual function-641 body constructs its deployed Debug contract from explicit writer contracts. -/
theorem f641_debug_instance (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp desc fmt e : UInt32) (S maxP : Nat) (hsp : S + 80 ≤ sp.toNat)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (P : IProp GF) (Q : UInt32 → UInt32 → UInt32 → IProp GF)
    (T : UInt32 → UInt32 → UInt32 → Nat → List (Nat × Nat) → Nat → IProp GF) (K598 K913 : Nat) :
    inst ↪[inst] mi ∗ A 598 ↪[wf] FuncInst.wasm types[13]! inst f598 ∗
      A 610 ↪[wf] FuncInst.wasm types[0]! inst f610 ∗ A 725 ↪[wf] FuncInst.wasm types[31]! inst f725 ∗
      A 913 ↪[wf] FuncInst.wasm types[13]! inst f913 ∗ A 599 ↪[wf] FuncInst.wasm types[0]! inst f599 ∗
      A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ∗ DropVec.dropCode inst mi A ∗
      ErrorCodeStringWriteSpec cfg lim (d + 1) inst mi n g gt sp e S K598 Cg P Q ∗
      (∀ p : UInt32, ∀ c : UInt32, ∀ l : UInt32,
        ErrorEnvelopeWriteSpec cfg lim (d + 1) inst mi n g gt (sp - 80) fmt e p c l 0 S K913 Cg (Q p c l)
          iprop(∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeap n maxP len live F p c ∗ T p c l len live F)) ⊢
      PanicDebug.SerdeErrorDebugSpec (GF := GF) cfg lim d inst mi desc fmt
        (700 * cfg.regularOpCost + K598 + K913) Cg
        iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗ P)
        iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗
          ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeapFreed n maxP len live F p c ∗ T p c l len live F) := by
  unfold PanicDebug.SerdeErrorDebugSpec
  exact f641_composed cfg lim d types[13]! rfl inst mi A n g ta hm hd Cg gt sp desc fmt e 0
    S maxP hsp hdesc P Q T K598 K913

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- Actual dynamic serde Debug dispatch instantiates the checked whole body, leaving only its precise writer contracts. -/
theorem f882_serde_composed (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp desc fmt e pp : UInt32) (S maxP : Nat) (hsp : S + 80 ≤ sp.toNat)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (hpp : pp.toNat + 8 ≤ 2 ^ 32) (P : IProp GF) (Q : UInt32 → UInt32 → UInt32 → IProp GF)
    (T : UInt32 → UInt32 → UInt32 → Nat → List (Nat × Nat) → Nat → IProp GF) (K598 K913 : Nat) :
    inst ↪[inst] mi ∗ A 641 ↪[wf] FuncInst.wasm types[13]! inst f641 ∗ A 598 ↪[wf] FuncInst.wasm types[13]! inst f598 ∗
      A 610 ↪[wf] FuncInst.wasm types[0]! inst f610 ∗ A 725 ↪[wf] FuncInst.wasm types[31]! inst f725 ∗
      A 913 ↪[wf] FuncInst.wasm types[13]! inst f913 ∗ A 599 ↪[wf] FuncInst.wasm types[0]! inst f599 ∗
      A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ∗ DropVec.dropCode inst mi A ∗
      ErrorCodeStringWriteSpec cfg lim (d + 2) inst mi n g gt sp e S K598 Cg P Q ∗
      (∀ p : UInt32, ∀ c : UInt32, ∀ l : UInt32,
        ErrorEnvelopeWriteSpec cfg lim (d + 2) inst mi n g gt (sp - 80) fmt e p c l 0 S K913 Cg (Q p c l)
          iprop(∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeap n maxP len live F p c ∗ T p c l len live F)) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f882 Cg
        (fun args => iprop(⌜args = [.i32 pp, .i32 fmt]⌝ ∗
          n ↦[i32][ pp.toNat ] desc ∗ n ↦[i32][ pp.toNat + 4 ] 1049036 ∗
          n ↦[i32][ 1049048 ] 12 ∗ ta ↦[wt][ 12 ] Ref.func (A 641) ∗ iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗ P)))
        (fun _ => 719 * cfg.regularOpCost + K598 + K913)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[i32][ pp.toNat ] desc ∗ n ↦[i32][ pp.toNat + 4 ] 1049036 ∗
          n ↦[i32][ 1049048 ] 12 ∗ ta ↦[wt][ 12 ] Ref.func (A 641) ∗ iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗
          ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeapFreed n maxP len live F p c ∗ T p c l len live F))) := by
  iintro ⟨#Hi, #F641, #F598, #F610, #F725, #F913, #F599, #F601, #HD, #S598, #S913⟩
  ihave S641 := f641_debug_instance cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt
    sp desc fmt e S maxP hsp hdesc P Q T K598 K913 $$ [Hi F598 F610 F725 F913 F599 F601 HD S598 S913]
  · iframe Hi F598 F610 F725 F913 F599 F601 HD S598 S913
  have H := PanicDebug.f882_serde_error_delegate (GF := GF) cfg lim d type htype inst mi A n g ta hm
    (by omega) Cg pp desc fmt (700 * cfg.regularOpCost + K598 + K913) iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗ P) iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗
          ∃ p c l : UInt32, ∃ len : Nat, ∃ live : List (Nat × Nat), ∃ F : Nat,
            stringHeapFreed n maxP len live F p c ∗ T p c l len live F) hpp
  have hcost : 19 * cfg.regularOpCost + (700 * cfg.regularOpCost + K598 + K913) =
      719 * cfg.regularOpCost + K598 + K913 := by omega
  rw [hcost] at H
  iapply H
  iframe Hi F641 S641

end WNear.Binary.SerdeDebug
