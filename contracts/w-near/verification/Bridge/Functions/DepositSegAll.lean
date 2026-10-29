import Bridge.Functions.InternalDepositOverflow

/-!
# `near_deposit` (232) from the call of `internal_deposit`, every outcome (M8)

`seg406_all`: the segment `seg406 ++ tail232` on the three outcomes of 406, by the balance `B`, the
supply `T` and the amount `a`:

* no overflow: `DepositSeg.seg406_ok`, the frame given back whole (`stk` of the 144 bytes and the
  `80 + SP` below);
* `B + a` overflows: 406 traps (`f406_bal`), the host after the read panicked with
  `"Balance overflow"`;
* `B + a` fits, `T + a` overflows: 406 traps (`f406_sup`), the host after the write panicked with
  "Total supply overflow".

`costSegAll` is the cost of the outcome.
-/

namespace WNear.Binary.DepositSegAll

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA join64' split64' stkW stkB)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StorageWrite (wslot evictedRegister)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.InternalDeposit (code406 pre406 Post406 cost405)
open WNear.Binary.LookupMapInsertSome (cost401s)
open WNear.Binary.DepositTail (tailCode tailStat costTail tail232 logText)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent hookRes pPre PanicSpecD)
open WNear.Binary.DepositSeg (seg406 costSeg LenUp seg406_ok activation406)
open WNear.Binary.InternalDepositOverflow (balMsg textSupply cost406bal cost406sup f406_bal f406_sup)
open WNear.Binary.NewBody (keep)

/-- The cost of the segment on its outcome. -/
noncomputable def costSegAll (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k : List UInt8)
    (x0 x1 t0 t1 lo hi : UInt64) (ab : List UInt8) (K879 : Nat → NewBody.Keep → Nat) : Nat :=
  if x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128 then
    if t0.toNat + 2 ^ 64 * t1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128 then
      costSeg cfg F pl L h k (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) lo hi ab
    else 20 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f406 [.i32 0, .i32 0, .i64 0, .i64 0]) +
      cost406sup cfg F pl L h k (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) K879
  else 20 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f406 [.i32 0, .i32 0, .i64 0, .i64 0]) +
    cost406bal cfg F pl L h k (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the segment (persistent). -/
def codeSeg (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code406 e n maxP inst mi A mx ∗ tailCode e n maxP inst mi A mx ∗
    A 406 ↪[wf] FuncInst.wasm types[38]! inst f406 ∗ A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗
    A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ panicCode e inst mi A ∗
    A 879 ↪[wf] FuncInst.wasm types[31]! inst f879)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (codeSeg (GF := GF) e n maxP inst mi A mx) := by
  unfold codeSeg; infer_instance

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **232 from the call of `internal_deposit`, on every outcome.** -/
theorem seg406_all (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat)
    (hd : d + 26 + D < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp self : UInt32) (l2 l3 l5 l6 : UInt64) (l4 : UInt32)
    (SP : Nat) (hSP : 400 ≤ SP) (hs : 80 + SP ≤ sp.toNat) (hs2 : sp.toNat + 144 ≤ 2 ^ 32 - 16)
    (hal : sp.toNat % 8 = 0)
    (hthis : self.toNat + 36 ≤ 2 ^ 32) (pp pc pl : UInt32) (t0 t1 x0 x1 : UInt64) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre : List UInt8)
    (ap : UInt32) (ab : List UInt8)
    (hpre : pre.length = pl.toNat) (hab : ab.length ≤ 64) (hab0 : 0 < ab.length)
    (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
    (hap : ap.toNat + ab.length ≤ 2 ^ 32) (hlive : (ap.toNat, ab.length) ∈ live)
    (hroom : HeapRoomK 11 hl maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab)))
        (h.storage (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))) +
      writeProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab)))
        (h.storage (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab)).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab)) =
      some (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8))
    (hok : x0.toNat + 2 ^ 64 * x1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat) < 2 ^ 128 →
      t0.toNat + 2 ^ 64 * t1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat) < 2 ^ 128 →
      LogStr.LogOk h (logText l3 l2 ab) (logText l3 l2 ab).length)
    (hfit16 : LogFits h 16) (hov16 : h.extCosts.cost "read_memory_byte" * 16 < 2 ^ 64)
    (hfitS : LogFits h textSupply.length) (hovS : h.extCosts.cost "read_memory_byte" * textSupply.length < 2 ^ 64)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K879 : Nat → NewBody.Keep → Nat)
    (H879 : PanicSpecD cfg lim inst mi C n g ta A gt lpc f879 SP Dp D 1053016 21 1053040 K879 textSupply)
    (Φ : Post NearState GF) :
    codeSeg e n maxP inst mi A mx ∗ C ∗
      credits Cg (costSegAll cfg F pl (UInt32.ofNat ab.length) h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))
        x0 x1 t0 t1 l3 l2 ab K879 + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 80 - SP) (80 + SP) ∗ stk n sp.toNat 24 ∗
      stk n (sp.toNat + 24) 16 ∗ n ↦[wms][ (sp + 40).toNat ] u128Bytes l3 l2 ∗
      n ↦[wms][ (sp + 56).toNat ] (bytes32 ap ++ (bytes32 (UInt32.ofNat ab.length) ++ bytes32 (UInt32.ofNat ab.length))) ∗
      n ↦[wms][ ap.toNat ] ab ∗ stk n (sp.toNat + 68) 4 ∗
      stk n (sp.toNat + 72) 24 ∗ stk n (sp.toNat + 96) 16 ∗ stk n (sp.toNat + 112) 12 ∗ stk n (sp.toNat + 124) 4 ∗
      stk n (sp.toNat + 128) 16 ∗ tailStat n ta A ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
      iface n ta A ∗ Interface.slot n ta 12 38 (A 240) ∗ wslot n ta A ∗ LogStr.lslot n ta A ∗
      panicSlot n ta A ∗ hookRes n ta A lpc ∗ Dp ∗ n ↦[wms][ 1053000 ] balMsg ∗
      n ↦[wms][ self.toNat ] storeBytes (.i64 t0) 8 ∗ n ↦[wms][ self.toNat + 8 ] storeBytes (.i64 t1) 8 ∗
      prefixAt n (self + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ mhostPt h ∗
      (∀ (l2' : UInt64) (hl' F' : Nat) (h' : NearState),
        ⌜F' ≤ F + 11 ∧ LenUp hl 10 hl' ∧
          Post406 e h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))
            (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat))) st bud h'⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ stk n (sp.toNat - 80 - SP) (80 + SP + 144) -∗
        tailStat n ta A -∗ vt n 1057464 aidx ta (A 578) -∗
        heapInv n maxP hl' (live.erase (ap.toNat, ab.length)) F' -∗
        iface n ta A -∗ Interface.slot n ta 12 38 (A 240) -∗ wslot n ta A -∗ LogStr.lslot n ta A -∗
        panicSlot n ta A -∗ hookRes n ta A lpc -∗ Dp -∗ n ↦[wms][ 1053000 ] balMsg -∗
        n ↦[wms][ self.toNat ] StorageBalanceBounds.u128Of (t0.toNat + 2 ^ 64 * t1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat)) -∗
        prefixAt n (self + 24) pp pc pl -∗ n ↦[wms][ pp.toNat ] pre -∗
        mhostPt (LogStr.logged h' (logText l3 l2 ab)) -∗
        Φ.ret [] ⟨#[.i32 self, .i32 sp, .i64 l2', .i64 l3, .i32 l4, .i64 l5, .i64 l6], inst, mi⟩) ∗
      (∀ h1, ⌜StorageReadPost h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab)) 0 st h1⌝ -∗
        panicked Cg h1 balMsg -∗ Φ.trap) ∗
      (∀ h2, ⌜Post406 e h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))
            (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat))) st bud h2⌝ -∗
        panicked Cg h2 textSupply -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 self, .i32 sp, .i64 l2, .i64 l3, .i32 l4, .i64 l5, .i64 l6], inst, mi⟩ []
          (seg406 ++ tail232) Φ := by
  iintro ⟨#Hk, #HC, Hc, Hg, Hlo, Hs24, H24, Hu, HV, Hab, H68, Har, H96, Hout, H124, Harg, HSt, Hvt, Hinv, HI, H12, HW, HL,
    HPS, HH, HD, HM, Ht0, Ht8, Hp, Hpre, Hh, Wok, Wbal, Wsup⟩
  iunfold codeSeg at Hk
  icases Hk with ⟨#H406c, #Htc, #F406, #F521, #F448, #HPC, #F879⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold tailCode, Interface.ifaceCode at Htc
    icases Htc with ⟨-, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #HIC : ifaceCode e inst mi A n mx $$ []
  · iunfold tailCode at Htc
    icases Htc with ⟨-, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have ha406 := hm.funcs 406 (by decide)
  have t38 : types[38]!.params.length = 4 := by rfl
  have hlt := sp.toNat_lt
  have e56 : (sp + 56).toNat = sp.toNat + 56 := by rw [UInt32.toNat_add]; simp; omega
  have hal' : (UInt32.ofNat ab.length).toNat = ab.length := by simp; omega
  icases stkSp (SP - 400) 480 (by omega) $$ Hlo with ⟨Hx, Hlo⟩
  ihave Hlo := stkA (b := sp.toNat - 480) (by omega) $$ Hlo
  unfold costSegAll
  by_cases hno1 : x0.toNat + 2 ^ 64 * x1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat) < 2 ^ 128
  · rw [if_pos hno1]
    by_cases hno2 : t0.toNat + 2 ^ 64 * t1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat) < 2 ^ 128
    · rw [if_pos hno2]
      iapply seg406_ok cfg lim d e inst mi A n g ta mx hm (by omega) Cg R gt sp self l2 l3 l5 l6 l4 (by omega) hs2 hal
        hthis pp pc pl t0 t1 x0 x1 aidx maxP hl live F hF pre ap ab hpre hab hab0 hpl hl0 hpp hap hlive
        (WNear.Binary.InternalDeposit.heapRoom_mono hroom (by omega)) hno1 hno2 h st hview hacc hcanon hlink hproof
        hbud hlim hvlim hreg hsome (hok hno1 hno2) Φ
      iframe H406c Htc F406 Hc Hg Hlo Hs24 Hu HV Hab Har Hout Harg HSt Hvt Hinv HI H12 HW HL Ht0 Ht8 Hp Hpre Hh
      iintro %l2' %hl' %F' %h' %hpost Hc Hg Hlo Hs24 Hu HV Har Hout Harg HSt Hvt Hinv HI H12 HW HL HT Hp Hpre Hh
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat - 480) (k1 := SP - 400) (k2 := 480) (k := 80 + SP)
        (by omega) (by omega) $$ [Hx Hlo]
      · iframe Hx Hlo
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat) (k1 := 80 + SP) (k2 := 24) (k := 80 + SP + 24)
        (by omega) rfl $$ [X Hs24]
      · iframe X Hs24
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 24) (k1 := 80 + SP + 24) (k2 := 16)
        (k := 80 + SP + 40) (by omega) rfl $$ [X H24]
      · iframe X H24
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 40) (k1 := 80 + SP + 40) (k2 := 16)
        (k := 80 + SP + 56) (by omega) rfl $$ [X Hu]
      · iframe X Hu
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 56) (k1 := 80 + SP + 56) (k2 := 12)
        (k := 80 + SP + 68) (by omega) rfl $$ [X HV]
      · iframe X HV
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 68) (k1 := 80 + SP + 68) (k2 := 4)
        (k := 80 + SP + 72) (by omega) rfl $$ [X H68]
      · iframe X H68
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 72) (k1 := 80 + SP + 72) (k2 := 24)
        (k := 80 + SP + 96) (by omega) rfl $$ [X Har]
      · iframe X Har
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 96) (k1 := 80 + SP + 96) (k2 := 16)
        (k := 80 + SP + 112) (by omega) rfl $$ [X H96]
      · iframe X H96
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 112) (k1 := 80 + SP + 112) (k2 := 12)
        (k := 80 + SP + 124) (by omega) rfl $$ [X Hout]
      · iframe X Hout
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 124) (k1 := 80 + SP + 124) (k2 := 4)
        (k := 80 + SP + 128) (by omega) rfl $$ [X H124]
      · iframe X H124
      ihave X := stkJ (a := sp.toNat - 80 - SP) (b := sp.toNat + 128) (k1 := 80 + SP + 128) (k2 := 16)
        (k := 80 + SP + 144) (by omega) rfl $$ [X Harg]
      · iframe X Harg
      iapply Wok $$ %l2' %hl' %F' %h' %hpost Hc Hg X HSt Hvt Hinv HI H12 HW HL HPS HH HD HM HT Hp Hpre Hh
    · rw [if_neg hno2]
      have S406 := f406_sup (GF := GF) cfg lim (d + 1) types[38]! inst mi e A n g ta mx hm D (by omega) Cg gt sp self
        pp pc pl (sp + 56) ap (UInt32.ofNat ab.length) (UInt32.ofNat ab.length) l3 l2 t0 t1 x0 x1 aidx maxP hl live F
        hF pre ab SP hSP hs hal hthis hpre hal'.symm (by omega) hpl hl0 hpp (by omega) (by omega) hroom hno1 hno2 h st
        hview hacc hcanon hlink hproof hbud hlim hvlim hreg hsome hfitS hovS C lpc Dp K879 H879
      ihave #S406' := S406 $$ [H406c F879 HC]
      · iframe H406c F879 HC
      ihave HIR : ifaceR n ta A $$ [HI H12]
      · iunfold ifaceR; iframe HI H12
      simp only [seg406, List.cons_append, List.nil_append]
      mstep; mstep; mstep; mstep; mstep; mstep
      iapply mwpi_cons
      iapply (PanicStr.mwpi_callT' (i := 406) (a := A 406) (type := types[38]!) (inst := inst) (mi := mi)
        (code := f406) [.i32 self, .i32 (sp + 56), .i64 l3, .i64 l2])
      isplitr
      · iexact S406'
      isplitr
      · iexact F406
      isplitr
      · iexact Hi
      isplitr
      · ipureintro; exact ⟨rfl, ha406, rfl, by omega⟩
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; rw [activation406]; mstep_norm_full; omega
      isplitl [Hg Hlo HIR HW Hvt Hinv Ht0 Ht8 Hp Hpre HV Hab Hh Hx HH HPS HD]
      · iframe HH HPS HD
        isplitr [Hx]
        · iunfold pre406
          iframe Hg Hlo HIR HW Hvt Hinv Ht0 Ht8 Hp Hpre HV Hab Hh
          ipureintro; rfl
        · iapply stkA (by omega) $$ Hx
      inext
      isplit
      · iintro %rs - HF
        iexfalso
        iexact HF
      · iintro HT
        simp only [Post.mseq_trap]
        icases HT with ⟨%h2, %hq2, HT⟩
        iapply Wsup $$ %h2 %hq2 HT
  · rw [if_neg hno1]
    have S406 := f406_bal (GF := GF) cfg lim (d + 1) types[38]! inst mi e A n g ta mx hm (by omega) Cg gt sp self
      pp pc pl (sp + 56) ap (UInt32.ofNat ab.length) (UInt32.ofNat ab.length) l3 l2 t0 t1 x0 x1 aidx maxP hl live F
      hF pre ab (by omega) hal hthis hpre hal'.symm (by omega) hpl hl0 hpp (by omega) (by omega)
      (WNear.Binary.InternalDeposit.heapRoom_mono hroom (by omega)) hno1 h st hacc hcanon hlink hproof
      (by unfold writeProofCost at hbud; omega) hlim hreg hsome hfit16 hov16
    ihave #S406' := S406 $$ [H406c F521 F448 HIC HPC]
    · iframe H406c F521 F448 HIC HPC
    ihave HIR : ifaceR n ta A $$ [HI H12]
    · iunfold ifaceR; iframe HI H12
    simp only [seg406, List.cons_append, List.nil_append]
    mstep; mstep; mstep; mstep; mstep; mstep
    iapply mwpi_cons
    iapply (PanicStr.mwpi_callT' (i := 406) (a := A 406) (type := types[38]!) (inst := inst) (mi := mi)
      (code := f406) [.i32 self, .i32 (sp + 56), .i64 l3, .i64 l2])
    isplitr
    · iexact S406'
    isplitr
    · iexact F406
    isplitr
    · iexact Hi
    isplitr
    · ipureintro; exact ⟨rfl, ha406, rfl, by omega⟩
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; rw [activation406]; mstep_norm_full; omega
    isplitl [Hg Hlo HIR HW Hvt Hinv Ht0 Ht8 Hp Hpre HV Hab Hh HPS HM]
    · iframe HPS HM
      iunfold pre406
      iframe Hg Hlo HIR HW Hvt Hinv Ht0 Ht8 Hp Hpre HV Hab Hh
      ipureintro; rfl
    inext
    isplit
    · iintro %rs - HF
      iexfalso
      iexact HF
    · iintro HT
      simp only [Post.mseq_trap]
      icases HT with ⟨%h1, %hq1, HT⟩
      iapply Wbal $$ %h1 %hq1 HT

end Spec

end WNear.Binary.DepositSegAll
