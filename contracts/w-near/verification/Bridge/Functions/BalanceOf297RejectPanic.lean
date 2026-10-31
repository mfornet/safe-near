import Bridge.Functions.PanicExpectError
import Bridge.Functions.BalanceOf297ParserHandoff

namespace WNear.Binary.BalanceOf297RejectPanic
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.PanicFmt WNear.Binary.PanicExpectError
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.PanicStr (panicked mwpi_callT')
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.BalanceOf297AbsentCall (frame)
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def rejectHandoffCode : List Instr :=
  [.block .empty [.local_get 0, .load .i32 none ⟨2, 88⟩, .i32_const 1, .i32_relop .ne, .br_if 0,
    .local_get 0, .local_get 0, .load .i32 none ⟨2, 92⟩, .store .i32 none ⟨2, 128⟩,
    .i32_const 1050760, .i32_const 38, .local_get 0, .i32_const 128, .i32_binop .add,
    .i32_const 1049036, .i32_const 1050984, .call 881, .unreachable]]

theorem rejectHandoffCode_eq : (f297.body.drop 36).take 1 = rejectHandoffCode := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Actual rejected parser-result branch of the deployed balance export. The exact common panic formatter remains explicit. -/
theorem parser_handoff_reject (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 err old : UInt32)
    (hs : 112 ≤ s.toNat) (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (E : IProp GF) (K : Nat) (h : NearState) (bs : List UInt8) (Φ : Post NearState GF) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗
      A 881 ↪[wf] FuncInst.wasm types[39]! inst f881 ∗
      Spec817 cfg lim (d + 5) inst mi Cg n g gt (s - 64 - 16 - 16 - 16) (s - 64 - 16 - 16 - 16)
        (s - 64 + 24) (s - 64 - 16) 1050984
        iprop(n ↦[i32][ (s - 64 - 16).toNat + 8 ] (s - 64 + 24) ∗
          (argsHead n (s - 64 + 24) 2 2 ∗ expectErrArgs n (s - 64) 1050760 38 (s + 128) 1049036 ∗
            (n ↦[i32][ s.toNat + 88 ] 1 ∗ n ↦[i32][ s.toNat + 92 ] err ∗
              n ↦[i32][ s.toNat + 128 ] err ∗ E))) K h bs ∗
      credits Cg (300 * cfg.regularOpCost + K) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ n ↦[i32][ s.toNat + 88 ] 1 ∗ n ↦[i32][ s.toNat + 92 ] err ∗
      n ↦[i32][ s.toNat + 128 ] old ∗ E ∗ ▷ (panicked Cg h bs -∗ Φ.trap) ⊢
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
  · iapply (f881_spec cfg lim (d + 1) types[39]! inst mi A n g ta hm (by omega) Cg gt
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
end WNear.Binary.BalanceOf297RejectPanic
