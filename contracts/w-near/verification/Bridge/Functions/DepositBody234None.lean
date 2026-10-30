import Bridge.Functions.DepositBody234
import Bridge.Functions.FtTotalSupplyNone

/-!
# `near_deposit` (234) on an uninitialized contract (M8)

```wat
;; 234 near_deposit(): sp0 = sp - 80
522(); 520(1, 1050188)          setup_panic_hook, set_blockchain_interface
219(sp0 + 40)                   state_read: None (no "STATE")
155(sp0, sp0 + 40)              unwrap_or_default: Contract::default panics, a trap
```

`body234None`: from the statics `body234` starts from, `PanicOnDefault`'s message, and a host with
no value at `STATE` (`FtTotalSupply.ReadNone`), the body traps with the host after `storage_read`
panicked with "The contract is not initialized" (as `FtTotalSupply.segBNone`, on 234's frame).
-/

namespace WNear.Binary.DepositBody234

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.ReadRegister (ifaceR iface_of_ifaceR)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.BorshFT (splitB stkJ stkW stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.StateRead (stateCode pre219 post219None noneAt)
open WNear.Binary.StateWrite (swCode)
open WNear.Binary.PanicStr (panicCode panicSlot panicked notInit)

/-- The cost of 234 on an absent `STATE`, activation excluded. -/
def cost234None (cfg : WasmConfig) (h : NearState) : Nat :=
  2400 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31

section None

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **234 on an uninitialized contract**: `state_read` leaves `None`, `unwrap_or_default` traps
through `Contract::default`, the host after `storage_read` panicked. -/
theorem body234None (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 31 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (SP : Nat) (hSP : 400 ≤ SP)
    (hs : 80 + 224 + SP ≤ s.toNat) (hs1 : 736 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hal : s.toNat % 8 = 0)
    (old k3 aidx : UInt32) (maxP len : Nat) (lpc : UInt32) (Dp : IProp GF)
    (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF) :
    code234 e inst mi A n maxP mx ∗ FtTotalSupply.codeP e inst mi A ∗ credits Cg (cost234None cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (304 + SP)) (304 + SP) ∗
      statics234 n ta A old k3 lpc Dp aidx maxP len ∗ n ↦[wms][ 1050868 ] notInit ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f234.body Φ := by
  iintro ⟨#Hk, #HP, Hc, Hg, Stk, HS, Hmsg, Hh, W⟩
  iunfold code234 at Hk
  icases Hk with ⟨#KA, #HSC, #F219, #F155, -, -, -, #HSW, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold codeA at KA
    icases KA with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #HIC : ifaceCode e inst mi A n mx $$ []
  · iunfold swCode at HSW
    icases HSW with ⟨-, -, #H, -⟩
    iexact H
  ihave #HP' := HP
  iunfold FtTotalSupply.codeP at HP'
  icases HP' with ⟨#F156, #F521, #F448, #Hpc⟩
  iunfold statics234 at HS
  icases HS with ⟨HH0, Hkey, T116, T106, HBI, HV, -, -, -, -, -, -, Hslot, -, -, -, -, -, Hvt, Hinv, HSK⟩
  obtain ⟨hv, hacc, hlim, hb, hz, hlink, hproof, hfit, hov⟩ := hr
  rw [← StateRead.stateKey_eq] at hv hlink hproof
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have e0 : (s - 80).toNat = s.toNat - 80 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 80 - 16).toNat = s.toNat - 96 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 80 - 16 - 16).toNat = s.toNat - 112 := by
    rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a40 : (s - 80 + 40).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, e0]; omega
  -- the stack: (224 + SP) below sp0, then the frame
  icases stkSp (224 + SP) 80 (by omega) $$ Stk with ⟨Lo, Fr⟩
  icases stkSp 40 40 rfl $$ Fr with ⟨-, F40⟩
  icases stkSp (224 + SP - 80) 80 (by omega) $$ Lo with ⟨Lo, L2⟩
  unfold cost234None
  rw [f234_body]
  iapply segA234 cfg lim d inst mi A n g ta hm (by omega) Cg
    (1925 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)
    gt s hs1 hal old k3 bodyB234 Φ
  ihave L2 := stkA (b := s.toNat - 160) (by omega) $$ L2
  iframe KA Hg L2 HH0 Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by omega) $$ Hc
  iintro Hc Hg L2 HI -
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  simp only [bodyB234]
  ihave Lo := DepositBody.stkJ2 (s.toNat - (304 + SP)) (by omega) (by omega) $$ Lo L2
  icases stkSp (224 + SP - 592) 592 (by omega) $$ Lo with ⟨-, Lo⟩
  -- state_read(sp0 + 40): None
  icases stk_bytes' $$ F40 with ⟨%ob, %hob, F40⟩
  mstep; mstep; mstep
  have S219 := StateRead.f219_spec_none (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm
    (by omega) Cg gt (s - 80) (s - 80 + 40) (by omega) (by omega) (by omega) aidx maxP len [] ob hob h hv st hacc
    hlim hb hz hlink hproof
  simp only [StorageReadWrap.costS] at S219
  mcall S219 using [Hg HI Lo Hvt Hinv F40 HSK Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 80).toNat - 592) (by omega) $$ Lo
    ihave F40 := memBytes_addr (b := (s - 80 + 40).toNat) (by omega) $$ F40
    iframe Hg HI Lo Hvt Hinv F40 HSK Hh
    ipureintro; rfl
  iunfold post219None at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, -, -, Ho, -, ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  obtain ⟨hcfg, hlogs, hext, -⟩ := storageReadPost_fields hq1
  -- the zero niche at sp0 + 40 + 24
  iunfold noneAt at Ho
  icases splitB (a := (s - 80 + 40).toNat) (b := (s - 80 + 40).toNat + 28) (ob.take 24 ++ [0, 0, 0, 0])
    (ob.drop 28) (by simp [hob]) $$ Ho with ⟨Ho, -⟩
  icases splitB (a := (s - 80 + 40).toNat) (b := (s - 80 + 40).toNat + 24) (ob.take 24) [0, 0, 0, 0]
    (by simp [hob]) $$ Ho with ⟨-, H24⟩
  ihave H24 := (show (n ↦[wms][ (s - 80 + 40).toNat + 24 ] [0, 0, 0, 0] : IProp GF) ⊢
    n ↦[i32][ (s - 80 + 40).toNat + 24 ] 0 by rw [StateRead.bytes32_zero']) $$ H24
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
  -- unwrap_or_default(sp0, sp0 + 40): a trap
  mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 155) (a := A 155) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f155) [.i32 (s - 80), .i32 (s - 80 + 40)])
  isplitr
  · iapply (UnwrapOrDefault.f155_spec_none cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm
      (by omega) Cg ⟨gt, .i32 (s - 80)⟩ (s - 80) rfl (by omega) (by omega) (s - 80) (s - 80 + 40)
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
    ihave C0 := memBytes_addr (b := (s - 80 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 80 - 16).toNat + 12) (by omega) $$ C4
    ihave W0 := memBytes_addr (b := (s - 80 - 16 - 16).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 80 - 16 - 16).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 80 - 16 - 16).toNat + 8) (by omega) $$ W8
    ihave W12 := memBytes_addr (b := (s - 80 - 16 - 16).toNat + 12) (by omega) $$ W12
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

end None

end WNear.Binary.DepositBody234
