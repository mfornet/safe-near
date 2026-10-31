import Bridge.Functions.BalanceOf297ParserHandoff
import Bridge.Functions.StateReadNoneF
import Bridge.Functions.FtTotalSupplyNone
import Bridge.Functions.BalanceOf297StateReadF

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.ReadRegister (iface_of_ifaceR)
open WNear.Binary.BorshFT (splitB stkSp)
open WNear.Binary.FtTotalSupply (stk4_word tsub)
open WNear.Binary.FtTotalSupply (ReadNone storageReadPost_fields logFits_of panicUtf8Use_of codeP staticsP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.StateReadNoneFree (post219NoneF f219_spec_noneF)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The actual balance state segment traps on an absent STATE, for the current arbitrary allocator F. -/
theorem state_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 128 ≤ 2 ^ 32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ob : List UInt8) (hob : ob.length = 40) (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st)
    (rest : List Instr) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP (some maxP) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some maxP) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗
      credits Cg (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R) ∗
      pre219F n g ta A gt s (s + 88) idx maxP len live F ob h [.i32 (s + 88)] ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
        (((f297.body.drop 68).take 11) ++ rest) Φ := by
  iintro ⟨#HSC, #F219, #F155, #HIC, #HP, #Hi, Hc, HP219, HSP, W⟩
  iunfold pre219F at HP219
  icases HP219 with ⟨-, Hg, HI, Lo, Hvt, Hinv, F72, Hkey, Hh⟩
  ihave #HP' := HP
  iunfold codeP at HP'
  icases HP' with ⟨#F156, #F521, #F448, #Hpc⟩
  iunfold staticsP at HSP
  icases HSP with ⟨Hslot, Hmsg⟩
  obtain ⟨hv, hacc, hlim, hb, hz, hlink, hproof, hfit, hov⟩ := hr
  rw [← StateRead.stateKey_eq] at hv hlink hproof
  have hn := hm.mem
  have hg := hm.glob
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  have e1 : (s - 16).toNat = s.toNat - 16 := by rw [tsub _ _ (by simp; omega)]; simp
  have e2 : (s - 16 - 16).toNat = s.toNat - 32 := by
    rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a72 : (s + 88).toNat = s.toNat + 88 := by simp [UInt32.toNat_add]; omega
  rw [BalanceOf297AbsentCall.stateCode297_eq]
  iapply mwpi_seq
  simp only [BalanceOf297AbsentCall.stateCode297, BalanceOf297AbsentCall.frame]
  -- state_read(sp0 + 72): None
  mstep; mstep; mstep
  have S219 := f219_spec_noneF (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm
    (by omega) Cg gt s (s + 88) hs hal (by simp [UInt32.toNat_add]; omega) idx maxP len live F ob hob h hv st hacc
    hlim hb hz hlink hproof
  mcall S219 using [Hg HI Lo Hvt Hinv F72 Hkey Hh]
  · iunfold pre219F
    iframe Hg HI Lo Hvt Hinv F72 Hkey Hh
    ipureintro; rfl
  iunfold post219NoneF at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, -, -, Ho, -, ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  obtain ⟨hcfg, hlogs, hext, -⟩ := storageReadPost_fields hq1
  -- the zero niche at sp0 + 72 + 24
  iunfold StateReadNoneFree.noneAt at Ho
  icases splitB (a := (s + 88).toNat) (b := (s + 88).toNat + 28) (ob.take 24 ++ [0, 0, 0, 0])
    (ob.drop 28) (by simp [hob]) $$ Ho with ⟨Ho, -⟩
  icases splitB (a := (s + 88).toNat) (b := (s + 88).toNat + 24) (ob.take 24) [0, 0, 0, 0]
    (by simp [hob]) $$ Ho with ⟨-, H24⟩
  ihave H24 := (show (n ↦[wms][ (s + 88).toNat + 24 ] [0, 0, 0, 0] : IProp GF) ⊢
    n ↦[i32][ (s + 88).toNat + 24 ] 0 by rw [StateRead.bytes32_zero']) $$ H24
  -- the frames of `env::panic_str` and `LocalKey::with`, out of the stack
  icases stkSp 560 32 rfl $$ Lo with ⟨-, Lo⟩
  icases stkSp 4 28 rfl $$ Lo with ⟨W0, Lo⟩
  icases stkSp 4 24 rfl $$ Lo with ⟨W4, Lo⟩
  icases stkSp 4 20 rfl $$ Lo with ⟨W8, Lo⟩
  icases stkSp 4 16 rfl $$ Lo with ⟨W12, Lo⟩
  icases stkSp 8 8 rfl $$ Lo with ⟨-, Lo⟩
  icases stkSp 4 4 rfl $$ Lo with ⟨C0, C4⟩
  icases stk4_word $$ W0 with ⟨%w0, W0⟩
  icases stk4_word $$ W4 with ⟨%w4, W4⟩
  icases stk4_word $$ W8 with ⟨%w8, W8⟩
  icases stk4_word $$ W12 with ⟨%w12, W12⟩
  icases stk4_word $$ C0 with ⟨%c0, C0⟩
  icases stk4_word $$ C4 with ⟨%c4, C4⟩
  icases iface_of_ifaceR n ta A $$ HI with ⟨HI, -⟩
  -- unwrap_or_default(sp0 + 32, sp0 + 72): a trap
  mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 155) (a := A 155) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f155) [.i32 (s + 48), .i32 (s + 88)])
  isplitr
  · iapply (UnwrapOrDefault.f155_spec_none cfg lim (d + 1) types[14]! inst mi e A n g ta (some maxP) hm
      (by omega) Cg ⟨gt, .i32 s⟩ s rfl (by omega) (by omega) (s + 48) (s + 88)
      c0 c4 w0 w4 w8 w12 h1 (logFits_of hcfg hlogs hfit) (by rw [hext]; exact hov))
    iframe F156 F521 F448 HIC Hpc
  isplitr
  · iexact F155
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha155, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; rw [panicUtf8Use_of hext]; omega
  isplitl [H24 Hg HI Hslot C0 C4 W0 W4 W8 W12 Hmsg Hh]
  · iunfold UnwrapOrDefault.preNone, PanicStr.defaultPre, RegisterLen.frame4
    ihave C0 := memBytes_addr (b := (s - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 16).toNat + 12) (by omega) $$ C4
    ihave W0 := memBytes_addr (b := (s - 16 - 16).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 16 - 16).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 16 - 16).toNat + 8) (by omega) $$ W8
    ihave W12 := memBytes_addr (b := (s - 16 - 16).toNat + 12) (by omega) $$ W12
    iframe H24 Hg HI Hslot C0 C4 W0 W4 W8 W12 Hmsg Hh
    ipureintro; exact ⟨rfl, rfl⟩
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap]
    iapply W $$ %h1 %hq1 HT

end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame parser_handoff)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Once parsing succeeds, the actual function-297 suffix traps on uninitialized state. -/
theorem parsed_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (p c L ip ic il idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (stateTail oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hstateTail : stateTail.length = 24)
    (hA : oldA.length = 8) (hB : oldB.length = 8) (hic : ic ≠ 0)
    (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP (some maxP) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some maxP) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] p ∗
      n ↦[i32][ (s + 88).toNat + 8 ] c ∗ n ↦[i32][ (s + 88).toNat + 12 ] L ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗ n ↦[i32][ (s + 48).toNat + 8 ] il ∗
      block n ip.toNat ic.toNat ∗ heapInv n maxP len ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F ∗
      staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 36).take 114) Φ := by
  iintro ⟨#HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc, Hg, HI, Hstk, Hvt, Hstatekey, Hhost,
    Tag, P, C, L0, HstateTail, A0, A8, B0, B8, I0, I4, I8, Hb, Hinv, HSP, W⟩
  have hseg : (f297.body.drop 36).take 114 =
      (f297.body.drop 36).take 32 ++ (f297.body.drop 68).take 82 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (parser_handoff cfg lim d inst mi A n g ta hm (by omega) Cg
    (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)
    s x1 x2 x3 p c L ip ic il maxP len F live oldA oldB oldC oldD hA hB hic hframe (by omega))
  iframe Hdrop F68 Hc Tag P C L0 A0 A8 B0 B8 I0 I4 I8 Hb Hinv
  inext
  iintro ⟨Hc, Tag, PC, L0, A0, A8, B0, B8, I0, I4, I8, Hinv⟩
  ihave StateTail := AllocNewCell.memBytes_addr (show (s + 104).toNat = (s + 88).toNat + 16 by
    simp [UInt32.toNat_add]; omega) $$ HstateTail
  ihave State0 := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 4)
    (bytes32 0) (bytes32 p ++ bytes32 c) (by simp) $$ [Tag PC]
  · iframe Tag PC
  ihave State0 := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 12)
    (bytes32 0 ++ (bytes32 p ++ bytes32 c)) (bytes32 L) (by simp [bytes32_length]) $$ [State0 L0]
  · iframe State0 L0
  ihave State0 := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 16)
    (bytes32 0 ++ (bytes32 p ++ bytes32 c) ++ bytes32 L) stateTail (by simp [bytes32_length]) $$ [State0 StateTail]
  · iframe State0 StateTail
  have hsuf : (f297.body.drop 68).take 82 = (f297.body.drop 68).take 11 ++ (f297.body.drop 79).take 71 := by rfl
  simp only [Post.mseq_normal]
  rw [hsuf]
  iapply (state_none_panics cfg lim d e inst mi A n g ta hm hd Cg R gt s L (VecFromElem.pair64 p c) (s + 40)
    hs hal (by omega) idx maxP len ((p.toNat, c.toNat) :: live) (F + 1)
    (((bytes32 0 ++ (bytes32 p ++ bytes32 c)) ++ bytes32 L) ++ stateTail) (by simp [bytes32_length, hstateTail])
    h st hr ((f297.body.drop 79).take 71))
  iframe HSC F219 F155 HIC HP Hi Hc HSP
  isplitl [Hg HI Hstk Hvt Hinv State0 Hstatekey Hhost]
  · iunfold pre219F
    iframe Hg HI Hstk Hvt Hinv State0 Hstatekey Hhost
    ipureintro; rfl
  iintro %h1 %hq HT
  iapply W $$ %h1 %hq HT
end WNear.Binary.BalanceOf297NoneCall
