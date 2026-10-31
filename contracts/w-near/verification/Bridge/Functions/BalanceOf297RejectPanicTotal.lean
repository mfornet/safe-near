import Bridge.Functions.PanicTotalExpectError
import Bridge.Functions.BalanceOf297RejectPanic

namespace WNear.Binary.PanicTotal
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.PanicStr NearLogic.PanicUtf8Large
open WNear.Binary.Interface
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.PanicHook
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

open WNear.Binary.PanicWithHook
open WNear.Binary.PanicFmt
open WNear.Binary.PanicExpectError
open WNear.Binary.BalanceOf297RejectPanic
open WNear.Binary.BalanceOf297AbsentCall (frame)
set_option maxHeartbeats 16000000 in
/-- Actual rejected ft_balance_of branch reaches the exact total panic entry without requiring all messages to fit. -/
theorem parser_handoff_reject_total (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 err old : UInt32)
    (hs : 112 ≤ s.toNat) (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (E : IProp GF) (K : Nat) (h : NearState) (bs : List UInt8) (Φ : Post NearState GF) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗
      A 881 ↪[wf] FuncInst.wasm types[39]! inst f881 ∗
      Spec817Total cfg lim (d + 5) inst mi Cg n g gt (s - 64 - 16 - 16 - 16) (s - 64 - 16 - 16 - 16)
        (s - 64 + 24) (s - 64 - 16) 1050984
        iprop(n ↦[i32][ (s - 64 - 16).toNat + 8 ] (s - 64 + 24) ∗
          (argsHead n (s - 64 + 24) 2 2 ∗ expectErrArgs n (s - 64) 1050760 38 (s + 128) 1049036 ∗
            (n ↦[i32][ s.toNat + 88 ] 1 ∗ n ↦[i32][ s.toNat + 92 ] err ∗
              n ↦[i32][ s.toNat + 128 ] err ∗ E))) K h bs ∗
      credits Cg (300 * cfg.regularOpCost + K) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ n ↦[i32][ s.toNat + 88 ] 1 ∗ n ↦[i32][ s.toNat + 92 ] err ∗
      n ↦[i32][ s.toNat + 128 ] old ∗ E ∗ ▷ (failedWith Cg h (expectedError h bs) -∗ Φ.trap) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 36).take 1) Φ := by
  iintro ⟨#HC, #F859, #F881, #S817, Hc, Hg, Hs, Tag, Err, Out, HE, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code859 at HC
    icases HC with ⟨#Hi, -⟩
    iexact Hi
  have hn := hm.mem
  have ha881 := hm.funcs 881 (by decide)
  have hlt := s.toNat_lt
  rw [rejectHandoffCode_eq]
  simp only [rejectHandoffCode, frame]
  mstep
  mstep; mstep [Tag]; mstep; mstep; mstep
  mstep; mstep; mstep [Err]; mstep [Out]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 881) (a := A 881) (type := types[39]!) (inst := inst) (mi := mi)
    (code := f881) [.i32 1050760, .i32 38, .i32 (s + 128), .i32 1049036, .i32 1050984]
  isplitr
  · iapply (f881_total_spec cfg lim (d + 1) types[39]! inst mi A n g ta hm (by omega) Cg gt
      s 1050760 38 (s + 128) 1049036 1050984 hs (by decide)
      iprop(n ↦[i32][ s.toNat + 88 ] 1 ∗ n ↦[i32][ s.toNat + 92 ] err ∗
        n ↦[i32][ s.toNat + 128 ] err ∗ E) K h bs)
    iframe HC F859 S817
  isplitr
  · iexact F881
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha881, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hs Tag Err Out HE]
  · iframe Hg Hs Tag Err Out HE
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso; iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock]
    iapply HΦ $$ HT


/-- Rejected handoff constructs its panic entry from explicit payload Get and ToStr contracts. -/
theorem parser_handoff_reject_total_full (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp x1 : UInt32) (x2 : UInt64) (x3 err old lpc : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 192 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (hframe : sp.toNat + 160 ≤ 2 ^ 32) (Ga G' D1 : IProp GF) (Kg K : Nat) (bs : List UInt8)
    (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) (Φ : Post NearState GF) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗
      GetSpec cfg lim (d + 7) inst mi Cg n g gt (sp - 64 - 16 - 16 - 16 - 16 - 32) (sp - 64 - 16 - 16 - 16 - 16)
        (sp - 64 - 16 - 16 - 16 - 16 + 4) 1066400 (S + 32) f826
        iprop(fmtPayload n (sp - 64 - 16 - 16 - 16 - 16) (sp - 64 + 24) ∗
          (argsHead n (sp - 64 + 24) 2 2 ∗ (expectErrArgs n (sp - 64) 1050760 38 (sp + 128) 1049036 ∗ (n ↦[i32][ sp.toNat + 88 ] 1 ∗ n ↦[i32][ sp.toNat + 92 ] err ∗ n ↦[i32][ sp.toNat + 128 ] err ∗ Ga)))) G' Kg ∗
      ToStr cfg lim (d + 9) inst mi Cg n g gt (sp - 64 - 16 - 16 - 16 - 16 - 32 - 32)
        (sp - 64 - 16 - 16 - 16 - 16 - 32 + 16) S
        iprop(infoCells n (sp - 64 - 16 - 16 - 16 - 16 - 32 + 16) (sp - 64 - 16 - 16 - 16 - 16 + 4) 1066400
            (sp - 64 + 24) 1050984 ∗ G' ∗
          (n ↦[i32][ (sp - 64 - 16).toNat + 8 ] (sp - 64 + 24) ∗ D1)) K bs ∗
      A 881 ↪[wf] FuncInst.wasm types[39]! inst f881 ∗
      credits Cg (300 * cfg.regularOpCost + cost817 cfg f826 Kg K bs h) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗
      n ↦[i32][ sp.toNat + 88 ] 1 ∗ n ↦[i32][ sp.toNat + 92 ] err ∗ n ↦[i32][ sp.toNat + 128 ] old ∗
      iprop(stk n ((sp - 64 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗ envP n ta A lpc 1066360 179 (A 826) D1 h) ∗ ▷ (failedWith Cg h (expectedError h bs) -∗ Φ.trap) ⊢
    mwpi cfg lim d (frame inst mi sp x1 x2 x3) [] ((f297.body.drop 36).take 1) Φ := by
  iintro ⟨#HC, #F859, #H817, #F826, #Sg, #Hts, #F881, Hc, Hg, Hs, Tag, Err, Out, HE, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code859 at HC
    icases HC with ⟨#Hi, -⟩
    iexact Hi
  have hn := hm.mem
  have ha881 := hm.funcs 881 (by decide)
  have hlt := sp.toNat_lt
  rw [rejectHandoffCode_eq]
  simp only [rejectHandoffCode, frame]
  mstep
  mstep; mstep [Tag]; mstep; mstep; mstep
  mstep; mstep; mstep [Err]; mstep [Out]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 881) (a := A 881) (type := types[39]!) (inst := inst) (mi := mi)
    (code := f881) [.i32 1050760, .i32 38, .i32 (sp + 128), .i32 1049036, .i32 1050984]
  isplitr
  · iapply (f881_total_full cfg lim (d + 1) types[39]! inst mi e A n g ta mx hm (by omega) Cg gt
      sp 1050760 38 (sp + 128) 1049036 1050984 lpc (by decide) S hS hsp hal
      iprop(n ↦[i32][ sp.toNat + 88 ] 1 ∗ n ↦[i32][ sp.toNat + 92 ] err ∗ n ↦[i32][ sp.toNat + 128 ] err ∗ Ga) G' D1 Kg K bs hpos hlen hutf h hov)
    iframe HC F859 H817 F826 Sg Hts
  isplitr
  · iexact F881
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha881, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hs Tag Err Out HE]
  · icases HE with ⟨Hdeep, HGa, Henv⟩
    simp only [Nat.sub_sub]
    iframe Hg Hs Tag Err Out Hdeep HGa Henv
  inext
  isplit
  · iintro %rs - HF
    iexfalso; iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock]
    iapply HΦ $$ HT

/-- Gas erasure preserves the exact selected panic error. -/
theorem expectedError_erase (h : NearState) (bs : List UInt8) :
    expectedError (erase h) bs = expectedError h bs := by rfl

/-- Raising gas and recorded proof does not change the message-size decision. -/
theorem expectedError_eraseP (h : NearState) (bs : List UInt8) :
    expectedError (eraseP h) bs = expectedError h bs := by rfl

/-- The exact trap postcondition supplies the final host fields required by receipt observation. -/
theorem failedHost_fields (h h' : NearState) (bs : List UInt8)
    (he : erase h' = erase { h with lastError := some (expectedError h bs) })
    (hi : h.lastExecutionIssue = none) :
    h'.lastError = some (expectedError h bs) ∧ h'.lastExecutionIssue = none := by
  refine ⟨?_, ?_⟩
  · exact erase_field he NearState.lastError fun _ => rfl
  · exact (erase_field he NearState.lastExecutionIssue fun _ => rfl).trans hi

end WNear.Binary.PanicTotal
