import Bridge.Functions.InternalDeposit
import Bridge.Functions.PanicStr
import Bridge.Functions.DepositSeg
import Bridge.Functions.DepositPanicSpec
import Bridge.Methods.NearDepositPanics

/-!
# `internal_deposit` (406) on its two overflows (M8)

```wat
;; 406 internal_deposit(this, acct, lo, hi): sp -= 80
;;     405(sp + 48, this, acct)                       the balance B
;;     B + a overflows → panic_str("Balance overflow" (1053000, 16))     521
;;     401(sp + 24, this + 24, acct, sp + 64)         insert(acct, B + a)
;;     363(sp + 8, (T + a overflows) ^ 1, lo', hi', 1053040)
;; 363 Option::expect(out, tag, lo, hi, loc): tag = 0 → expect_failed("Total supply overflow"
;;     (1053016, 21), loc)                             879
```

* `f406_bal`: the balance overflows: it traps through `panic_str` (`f521_spec`), the host after
  the read of the balance (`StorageReadPost`) panicked with `"Balance overflow"`.
* `f363_none`: `Option::expect` on `None`: it calls 879 and traps as 879 does (879's
  specification a premise).
* `f406_sup`: the balance fits, the supply overflows: the new balance is written
  (`Post406`'s chain) and it traps through 363 and 879 (879's specification, `Spec879D`, a
  premise of the shape of `NearDepositPanics.Spec879`, with what the caller owns at the call).
-/

namespace WNear.Binary.InternalDepositOverflow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.InternalDeposit (code406 code405 pre406 pre405 post405 cost405 Post406 heapRoom_mono ld64)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.NewBody (keep keep_of_erase keep_acc keep_storageReadRegs sameCost_of_keep chargesUse_congr)

/-! ## The message -/

/-- `"Balance overflow"`, the 16 bytes at 1053000. -/
def balMsg : List UInt8 := [66, 97, 108, 97, 110, 99, 101, 32, 111, 118, 101, 114, 102, 108, 111, 119]

theorem balMsg_eq : balMsg = "Balance overflow".toUTF8.toList := by decide +kernel

theorem balMsg_data :
    (List.range 16).map (fun k => wNearSource.read (159306 + (1053000 - 1048576) + k)) = balMsg := by
  decide

theorem balMsg_length : balMsg.length = 16 := rfl

theorem balMsg_valid : validUtf8 balMsg = true := by decide

theorem balMsg_utf8String : utf8String balMsg = "Balance overflow" := by decide +kernel

theorem panicUtf8Use_congr {x y : NearState} (h : NewBody.SameCost x y) (k : Nat) :
    panicUtf8Use x k = panicUtf8Use y k := chargesUse_congr h _

theorem keep_readPost {h h1 : NearState} {k : List UInt8} {st : Near.TrieOverlay.State}
    (hq : StorageReadPost h k 0 st h1) : keep h1 = keep h := by
  obtain ⟨s2, -, -, he⟩ := hq
  rw [keep_of_erase he, keep_storageReadRegs, keep_acc]

theorem LogFits.of_keep {h h' : NearState} {k : Nat} (hk : keep h' = keep h) (hf : LogFits h k) : LogFits h' k := by
  have hc : h'.config = h.config := congrArg NewBody.Keep.config hk
  have hl : h'.logs = h.logs := congrArg NewBody.Keep.logs hk
  intro limit hlim; rw [hl]; exact hf limit (by rw [← hc]; exact hlim)

/-! ## The balance overflow -/

section Bal

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of 406 on the balance overflow, activation excluded. -/
def cost406bal (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k old : List UInt8) : Nat :=
  400 * cfg.regularOpCost + cost405 cfg F pl L h k old + panicUtf8Use h 16

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- **`FungibleToken::internal_deposit`** (406) when the balance `B + a` overflows: it traps
through `panic_str("Balance overflow")`, the host after the read of the balance panicked. -/
theorem f406_bal (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s this pp pc pl v p c L : UInt32) (lo hi t0 t1 x0 x1 : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key : List UInt8)
    (hs : 480 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hthis : this.toNat + 36 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 7 len maxP)
    (hov1 : ¬ (x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128))
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key)))
        (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8))
    (hfit : LogFits h 16) (hov : h.extCosts.cost "read_memory_byte" * 16 < 2 ^ 64) :
    code406 e n maxP inst mi A mx ∗ A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗
      A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ ifaceCode e inst mi A n mx ∗ panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f406 Cg
        (fun args => iprop(pre406 n g ta A gt s this pp pc pl v p c L lo hi t0 t1 idx maxP len live F pre key h args ∗
          panicSlot n ta A ∗ n ↦[wms][ 1053000 ] balMsg))
        (fun _ => cost406bal cfg F pl L h (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8))
        (fun _ _ => iprop(False))
        (fun _ => iprop(∃ h1, ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h1⌝ ∗ panicked Cg h1 balMsg)) := by
  iintro ⟨#Hk, #F521, #F448, #HIC, #HPC⟩
  iunfold code406 at Hk
  icases Hk with ⟨#H405c, #H401c, #F405, #F401, #F363⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code405, LookupMapGet.code399, LookupMapGet.code400, DropVec.dropCode at H405c
    icases H405c with ⟨⟨⟨-, ⟨#H, -⟩, -⟩, -⟩, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha405 := hm.funcs 405 (by decide)
  have ha521 := hm.funcs 521 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h80 : (s - 80).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have S405 := InternalDeposit.f405_some (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm
    (by omega) Cg gt (s - 80) (s - 80 + 48) this pp pc pl v p c L idx maxP len live F hF pre key
    (storeBytes (.i64 x0) 8) (storeBytes (.i64 x1) 8)
  generalize hK405 : cost405 cfg F pl L h (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) = K405
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  unfold cost406bal
  rw [hK405]
  icases HP with ⟨HP, HPS, HM⟩
  iunfold pre406 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Ht0, Ht8, Hm, Hp, Hv, Hkey, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 480) 400 80 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 480 + 400 = s.toNat - 80 by omega]
  icases stk_split n (s.toNat - 80) 8 72 $$ Fr with ⟨U0, Fr⟩
  icases stk_split n (s.toNat - 80 + 8) 16 56 $$ Fr with ⟨T, Fr⟩
  icases stk_split n (s.toNat - 80 + 8 + 16) 24 32 $$ Fr with ⟨I, Fr⟩
  icases stk_split n (s.toNat - 80 + 8 + 16 + 24) 16 16 $$ Fr with ⟨B, N⟩
  iunfold stk at B
  icases B with ⟨%bb, %hbb, B⟩
  ihave B := memBytes_addr (show s.toNat - 80 + 8 + 16 + 24 = (s - 80 + 48).toNat by simp [UInt32.toNat_add, h80]; omega) $$ B
  simp only [f406]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 405: the balance
  mstep; mstep; mstep; mstep; mstep
  mcall (S405 bb (by omega) (by omega) hbb (by simp [UInt32.toNat_add, h80]; omega) (by omega) hpre hkey
      (by simp) (by simp) hL hpl hl0 hpp hv hp (heapRoom_mono hroom (by omega)) h st hacc hlim hcanon.1 hcanon.2 (hlink _) hproof
      (by unfold readProofCost at hbud; omega) hreg hsome)
      using [Hg Lo HI Hvt Hinv Hm Hp Hv Hkey B Hhost] with (rw [hK405]; mstep_norm_full; omega)
  · iunfold pre405
    ihave Lo := stk_addr (show s.toNat - 480 = (s - 80).toNat - 400 by omega) $$ Lo
    iframe Hg Lo HI Hvt Hinv Hm Hp Hv Hkey B Hhost
    ipureintro; rfl
  rw [hK405]
  iunfold post405 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, ⟨%l1, %hl1, Hinv⟩, Hm, Hp, Hv, Hkey, B0, B8, ⟨%h1, %hq1, Hhost⟩⟩
  subst hrs
  -- the checked add
  mstep; mstep; mstep [B0]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep [B8]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply FmtGrow.mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega, trivial⟩
  inext
  iintro Hc
  mctrl_norm
  rw [← apply_ite Value.i32, Add128.add128_flag x0 x1 lo hi, if_neg hov1]
  mstep; mstep
  mstep_not_taken
  -- panic_str(1053000, 16)
  have hk1 := keep_readPost hq1
  icases ReadRegister.iface_of_ifaceR n ta A $$ HI with ⟨HI, -⟩
  icases stk_split n ((s - 80).toNat - 400) 368 32 $$ Lo with ⟨-, L32⟩
  icases stk_split n ((s - 80).toNat - 400 + 368) 16 16 $$ L32 with ⟨F16, L32⟩
  icases stk_split n ((s - 80).toNat - 400 + 368 + 16) 8 8 $$ L32 with ⟨-, L32⟩
  icases stk_split n ((s - 80).toNat - 400 + 368 + 16 + 8) 4 4 $$ L32 with ⟨C0, C4⟩
  icases ReadRegister.stk4_word n _ $$ C0 with ⟨%c0, C0⟩
  icases ReadRegister.stk4_word n _ $$ C4 with ⟨%c4, C4⟩
  have e96 : (s - 80 - 16).toNat = s.toNat - 96 := by
    rw [StorageBalanceBounds.tsub' _ _ (by simp [h80]; omega), h80]; simp; omega
  have e32 : (s - 80 - 16 - 16).toNat = (s - 80).toNat - 400 + 368 := by
    rw [StorageBalanceBounds.tsub' _ _ (by simp [e96]; omega), e96, h80]; simp; omega
  icases ReadRegister.stk_frame4 n _ (s - 80 - 16 - 16) e32 $$ F16 with ⟨%w0, %w4, %w8, %w12, F16⟩
  mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 521) (a := A 521) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f521) [.i32 1053000, .i32 16])
  isplitr
  · iapply (PanicStr.f521_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 80)⟩ (s - 80) rfl (by omega) (by omega) 1053000 16 balMsg rfl (by decide)
      balMsg_valid c0 c4 w0 w4 w8 w12 h1 (LogFits.of_keep hk1 hfit)
      (by rw [show h1.extCosts = h.extCosts from congrArg NewBody.Keep.extCosts hk1]; exact hov))
    iframe F448 HIC HPC
  isplitr
  · iexact F521
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha521, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro
    rw [panicUtf8Use_congr (sameCost_of_keep hk1)]
    mstep_norm_full; omega
  isplitl [Hg HI HPS C0 C4 F16 HM Hhost]
  · iunfold PanicStr.pre
    ihave C0 := memBytes_addr (b := (s - 80 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 80 - 16).toNat + 12) (by omega) $$ C4
    ihave HM := memBytes_addr (a := 1053000) (b := (1053000 : UInt32).toNat) rfl $$ HM
    iframe Hg HI HPS C0 C4 F16 HM Hhost
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexists h1
    iframe HT
    ipureintro; exact hq1

end Bal

/-! ## `Option::expect` (363) on `None` -/

section S363

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent)

theorem activation879 (c : Nat) (a b l : UInt32) :
    activationGas c (entryLocals f879 [.i32 a, .i32 b, .i32 l]) =
      activationGas c (entryLocals f879 [.i32 0, .i32 0, .i32 0]) := by
  simp [activationGas, entryLocals, f879, ValType.default]

/-- **`Option::<u128>::expect`** (363) on `None` (`tag = 0`): it calls
`expect_failed("Total supply overflow", loc)` (879) and traps as 879 does. -/
theorem f363_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (a879 : Nat) (ha : mi.funcAddrs[879]? = some a879)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (out : UInt32) (tag lo hi : UInt64) (loc : UInt32)
    (htag : tag.toUInt32 = 0) (P : IProp GF) (K : Nat) (T : IProp GF) :
    a879 ↪[wf] FuncInst.wasm types[31]! inst f879 ∗ inst ↪[inst] mi ∗
      MFunSpecT cfg lim (d + 1) types[31]! inst mi f879 Cg
        (fun args => iprop(⌜args = [.i32 1053016, .i32 21, .i32 loc]⌝ ∗ P)) (fun _ => K)
        (fun _ _ => iprop(False)) (fun _ => T)
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f363 Cg
        (fun args => iprop(⌜args = [.i32 out, .i64 tag, .i64 lo, .i64 hi, .i32 loc]⌝ ∗ P))
        (fun _ => 10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f879 [.i32 0, .i32 0, .i32 0]) + K)
        (fun _ _ => iprop(False)) (fun _ => T) := by
  iintro ⟨#F879, #Hi, #S879⟩
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f363]
  mstep; mstep; mstep
  rw [htag]
  mstep_not_taken
  mstep; mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 879) (a := a879) (type := types[31]!) (inst := inst) (mi := mi)
    (code := f879) [.i32 1053016, .i32 21, .i32 loc])
  isplitr
  · iexact S879
  isplitr
  · iexact F879
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha, rfl, hd⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [activation879]; mstep_norm_full; omega
  isplitl [HP]
  · iframe HP
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT

end S363

/-! ## The supply overflow -/

section Sup

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent hookRes pPre PanicSpecD)
open WNear.Binary.LookupMapInsertSome (cost401s code401s pre401s post401s)
open WNear.Binary.StorageWrite (wslot evictedRegister)
open WNear.Binary.DepositSeg (cost401s_congr)

/-- The text of the supply overflow: the model's message in UTF-8. -/
abbrev textSupply : List UInt8 := NearDepositPanics.textSupply

/-- The cost of 406 on the supply overflow, activation excluded: 879's `K879 F' kp` on the free
cells and the host's costs at the call. -/
noncomputable def cost406sup (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k old : List UInt8)
    (K879 : Nat → NewBody.Keep → Nat) : Nat :=
  400 * cfg.regularOpCost + cost405 cfg F pl L h k old + cost401s cfg (F + 3) pl L h k old +
    activationGas cfg.regularOpCost (entryLocals f879 [.i32 0, .i32 0, .i32 0]) + K879 (F + 7) (keep h)

theorem activation363 (c : Nat) (a : UInt32) (x y z : UInt64) (l : UInt32) :
    activationGas c (entryLocals f363 [.i32 a, .i64 x, .i64 y, .i64 z, .i32 l]) =
      activationGas c (entryLocals f363 [.i32 0, .i64 0, .i64 0, .i64 0, .i32 0]) := by
  simp [activationGas, entryLocals, f363]

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **`FungibleToken::internal_deposit`** (406) when the balance fits and the supply `T + a`
overflows: the balance `B + a` written (the host as `Post406`), then `expect` on `None` (363) and
`expect_failed` (879, `PanicSpecD`) trap, the host panicked with "Total supply overflow". -/
theorem f406_sup (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hd : d + 19 + D < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s this pp pc pl v p c L : UInt32) (lo hi t0 t1 x0 x1 : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key : List UInt8)
    (SP : Nat) (hSP : 400 ≤ SP) (hs : 80 + SP ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hthis : this.toNat + 36 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 15 len maxP)
    (hno1 : x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128)
    (hov2 : ¬ (t0.toNat + 2 ^ 64 * t1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128))
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key)))
        (h.storage (pre ++ (bytes32 L ++ key))) +
      writeProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key)))
        (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8))
    (hfit : LogFits h textSupply.length) (hov : h.extCosts.cost "read_memory_byte" * textSupply.length < 2 ^ 64)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K879 : Nat → NewBody.Keep → Nat)
    (H879 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f879 SP Dp D 1053016 21 1053040 K879 textSupply) :
    code406 e n maxP inst mi A mx ∗ A 879 ↪[wf] FuncInst.wasm types[31]! inst f879 ∗ C
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f406 Cg
        (fun args => iprop(pre406 n g ta A gt s this pp pc pl v p c L lo hi t0 t1 idx maxP len live F pre key h args ∗
          stk n (s.toNat - 80 - SP) (SP - 400) ∗ hookRes n ta A lpc ∗ panicSlot n ta A ∗ Dp ∗
          n ↦[wms][ 1070974 ] FmtDigits.lut))
        (fun _ => cost406sup cfg F pl L h (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) K879)
        (fun _ _ => iprop(False))
        (fun _ => iprop(∃ h2, ⌜Post406 e h (pre ++ (bytes32 L ++ key))
            (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat))) st bud h2⌝ ∗
          panicked Cg h2 textSupply)) := by
  iintro ⟨#Hk, #F879, #HC⟩
  iunfold code406 at Hk
  icases Hk with ⟨#H405c, #H401c, #F405, #F401, #F363⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code405, LookupMapGet.code399, LookupMapGet.code400, DropVec.dropCode at H405c
    icases H405c with ⟨⟨⟨-, ⟨#H, -⟩, -⟩, -⟩, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha405 := hm.funcs 405 (by decide)
  have ha401 := hm.funcs 401 (by decide)
  have ha363 := hm.funcs 363 (by decide)
  have ha879 := hm.funcs 879 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have t49 : types[49]!.params.length = 5 := by rfl
  have hlt := s.toNat_lt
  have h80 : (s - 80).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have S405 := InternalDeposit.f405_some (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega)
    Cg gt (s - 80) (s - 80 + 48) this pp pc pl v p c L idx maxP len live F hF pre key
    (storeBytes (.i64 x0) 8) (storeBytes (.i64 x1) 8)
  generalize hK405 : cost405 cfg F pl L h (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) = K405
  generalize hK401 : cost401s cfg (F + 3) pl L h (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) = K401
  generalize hK9 : K879 (F + 7) (keep h) = K9
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  unfold cost406sup
  rw [hK405, hK401, hK9]
  icases HP with ⟨HP, Hx, HH, HPS, HD, HLut⟩
  iunfold pre406 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Ht0, Ht8, Hm, Hp, Hv, Hkey, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 480) 400 80 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 480 + 400 = s.toNat - 80 by omega]
  icases stk_split n (s.toNat - 80) 8 72 $$ Fr with ⟨U0, Fr⟩
  icases stk_split n (s.toNat - 80 + 8) 16 56 $$ Fr with ⟨T, Fr⟩
  icases stk_split n (s.toNat - 80 + 8 + 16) 24 32 $$ Fr with ⟨I, Fr⟩
  icases stk_split n (s.toNat - 80 + 8 + 16 + 24) 16 16 $$ Fr with ⟨B, N⟩
  iunfold stk at T I B N
  icases T with ⟨%tb, %htb, T⟩
  icases I with ⟨%ib, %hib, I⟩
  icases B with ⟨%bb, %hbb, B⟩
  icases N with ⟨%nb, %hnb, N⟩
  ihave B := memBytes_addr (show s.toNat - 80 + 8 + 16 + 24 = (s - 80 + 48).toNat by simp [UInt32.toNat_add, h80]; omega) $$ B
  simp only [f406]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 405: the balance
  mstep; mstep; mstep; mstep; mstep
  mcall (S405 bb (by omega) (by omega) hbb (by simp [UInt32.toNat_add, h80]; omega) (by omega) hpre hkey
      (by simp) (by simp) hL hpl hl0 hpp hv hp (heapRoom_mono hroom (by omega)) h st hacc hlim hcanon.1 hcanon.2 (hlink _) hproof
      (by unfold readProofCost writeProofCost at hbud; omega) hreg hsome)
      using [Hg Lo HI Hvt Hinv Hm Hp Hv Hkey B Hhost] with (rw [hK405]; mstep_norm_full; omega)
  · iunfold pre405
    ihave Lo := stk_addr (show s.toNat - 480 = (s - 80).toNat - 400 by omega) $$ Lo
    iframe Hg Lo HI Hvt Hinv Hm Hp Hv Hkey B Hhost
    ipureintro; rfl
  rw [hK405]
  iunfold post405 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, ⟨%l1, %hl1, Hinv⟩, Hm, Hp, Hv, Hkey, B0, B8, ⟨%h1, %hq1, Hhost⟩⟩
  subst hrs
  -- the checked add
  mstep; mstep; mstep [B0]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep [B8]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply FmtGrow.mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega, trivial⟩
  inext
  iintro Hc
  mctrl_norm
  rw [← apply_ite Value.i32, Add128.add128_flag x0 x1 lo hi, if_pos hno1]
  mstep; mstep
  mstep_taken
  -- the new balance at sp + 64
  ihave N := U128From.memBytes_split n (s.toNat - 80 + 8 + 16 + 24 + 16) 8 nb (by omega) $$ N
  icases N with ⟨N0, N8⟩
  have hn0 : (nb.take 8).length = 8 := by simp; omega
  have hn8 : (nb.drop 8).length = 8 := by simp; omega
  ihave N0 := memBytes_addr (show s.toNat - 80 + 8 + 16 + 24 + 16 = (s - 80).toNat + 64 by omega) $$ N0
  ihave N8 := memBytes_addr (show s.toNat - 80 + 8 + 16 + 24 + 16 + 8 = (s - 80).toNat + 72 by omega) $$ N8
  mstep; mstep; mstep [N0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [N8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  -- 401: insert the new balance
  have hk1 := (StorageReadPost.next hq1 hcanon hlink hproof (by simp only [readProofCost, writeProofCost] at hbud ⊢; omega))
  obtain ⟨s1, hacc1, hcan1, hlink1, hp1, he1⟩ := hk1
  have hst1 : h1.storage = h.storage :=
    (erase_field he1 NearState.storage fun _ => rfl).trans
      (storageReadRegs_field NearState.storage (fun _ _ _ => rfl) _ _ _)
  have hcfg1 : h1.config = h.config :=
    (erase_field he1 NearState.config fun _ => rfl).trans
      (storageReadRegs_field NearState.config (fun _ _ _ => rfl) _ _ _)
  have hview1 : h1.context.isView = false :=
    ((erase_field he1 (fun x : NearState => x.context.isView) fun _ => rfl).trans
      (storageReadRegs_field (fun x : NearState => x.context.isView) (fun _ _ _ => rfl) _ _ _)).trans hview
  have hid1 : h1.context.currentAccountId = h.context.currentAccountId :=
    (erase_field he1 (fun x : NearState => x.context.currentAccountId) fun _ => rfl).trans
      (storageReadRegs_field (fun x : NearState => x.context.currentAccountId) (fun _ _ _ => rfl) _ _ _)
  have hkp1 : keep h1 = keep h := by rw [keep_of_erase he1, keep_storageReadRegs, keep_acc]
  have hl1' : LenIn len 3 l1 := hl1
  have S401 := LookupMapInsertSome.f401_some (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi e A n g ta mx hm
    (by omega) Cg gt (s - 80) (s - 80 + 24) (this + 24) pp pc pl v p c L (s - 80 + 64) idx maxP l1 live (F + 3)
    (by unfold okG at hF ⊢; omega) pre key (storeBytes (.i64 (x0 + lo)) 8)
    (storeBytes (.i64 (x1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + lo) x0)).toUInt64)) 8)
    (storeBytes (.i64 x0) 8) (storeBytes (.i64 x1) 8) ib (by omega) (by omega) hib
    (by simp [UInt32.toNat_add, h80]; omega) hpre hkey (by simp) (by simp) (by simp) (by simp) hL hpl hl0 hpp hv hp
    (by simp [UInt32.toNat_add, h80]; omega) (MeasureUsage.heapRoom_shift hroom hl1' (by omega)) h1 s1 hview1 hacc1
    (by rw [hcfg1, show (pre ++ (bytes32 L ++ key)).length = (pre ++ (bytes32 L ++ key)).length from rfl]; exact hlim)
    (by rw [hcfg1]; simpa using hvlim) hcan1.1 hcan1.2 (hlink1 _) hp1
    (by rw [hid1, hst1]; simp only [readProofCost, writeProofCost] at hbud ⊢; omega) (by rw [hcfg1]; exact hreg)
    (by rw [hst1]; exact hsome)
  have hK1 : cost401s cfg (F + 3) pl L h1 (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) = K401 := by
    rw [← hK401]
    exact cost401s_congr cfg (F + 3) pl L (sameCost_of_keep hkp1) (by rw [hst1]) _
  rw [hK1] at S401
  ihave I := memBytes_addr (show s.toNat - 80 + 8 + 16 = (s - 80 + 24).toNat by simp [UInt32.toNat_add, h80]; omega) $$ I
  ihave N0 := memBytes_addr (show (s - 80).toNat + 64 = (s - 80 + 64).toNat by simp [UInt32.toNat_add, h80]; omega) $$ N0
  ihave N8 := memBytes_addr (show (s - 80).toNat + 72 = (s - 80 + 64).toNat + 8 by simp [UInt32.toNat_add, h80]; omega) $$ N8
  ihave #H401 := S401 $$ H401c
  icases stk_split n ((s - 80).toNat - 400) 80 320 $$ Lo with ⟨Lo80, Lo⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall H401 using [Hg Lo HI HW Hvt Hinv Hm Hp Hv Hkey N0 N8 I Hhost] with (mstep_norm_full; omega)
  · iunfold pre401s
    ihave Lo := stk_addr (show (s - 80).toNat - 400 + 80 = (s - 80).toNat - 320 by omega) $$ Lo
    iframe Hg Lo HI HW Hvt Hinv Hm Hp Hv Hkey N0 N8 I Hhost
    ipureintro; rfl
  iunfold post401s at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, HW, Hvt, ⟨%l2, %hl2, Hinv⟩, Hm, Hp, Hv, Hkey, N0, N8, I, ⟨%h2, %hq2, Hhost⟩⟩
  subst hrs
  have hpost : Post406 e h (pre ++ (bytes32 L ++ key))
      (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat))) st bud h2 := by
    have hBs : StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat)) =
        storeBytes (.i64 (x0 + lo)) 8 ++
          storeBytes (.i64 (x1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + lo) x0)).toUInt64)) 8 := by
      refine (StorageBalanceBounds.u128Bytes_eq_u128Of _ _ _ ?_).symm
      have := Add128.add128_words x0 x1 lo hi
      omega
    rw [hBs]
    exact ⟨h1, s1, hq1, hacc1, hcan1, hlink1, hp1, he1, hq2⟩
  have hkp2 : keep h2 = keep h := DepositSeg.Post406.keep hpost
  -- the checked add of the total supply
  mstep; mstep; mstep
  mstep; mstep [Ht0]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep [Ht8]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply FmtGrow.mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega, trivial⟩
  inext
  iintro Hc
  mctrl_norm
  rw [← apply_ite Value.i32, Add128.add128_flag t0 t1 lo hi, if_neg hov2]
  mstep; mstep; mstep
  mstep; mstep; mstep
  -- 363 on `None`, then 879
  have hroom2 : HeapRoomK 8 l2 maxP :=
    MeasureUsage.heapRoom_shift hroom (MeasureUsage.lenIn_trans hl1' hl2) (by omega)
  have S879 := H879 (d + 2) Cg (s - 80) h2 l2 live (F + 7) idx (by omega) (by omega) (by omega) (by omega) hroom2
    (by unfold okG at hF ⊢; omega) (LogFits.of_keep hkp2 hfit)
    (by rw [show h2.extCosts = h.extCosts from congrArg NewBody.Keep.extCosts hkp2]; exact hov)
  rw [hkp2, hK9] at S879
  ihave Hinv : heapInv n maxP l2 live (F + 7) $$ [Hinv]
  · rw [show F + 7 = F + 3 + 4 by omega]; iexact Hinv
  ihave #S879' := S879 $$ HC
  ihave #S363 := f363_none (GF := GF) cfg lim (d + 1) types[49]! inst mi (A 879) ha879 (by omega) Cg (s - 80 + 8)
    ((1 : UInt32) ^^^ 1).toUInt64 (t0 + lo)
    (t1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (t0 + lo) t0)).toUInt64) 1053040 (by decide)
    (pPre n g ta A gt lpc SP Dp (s - 80) maxP l2 live (F + 7) idx h2) K9
    (panicked Cg h2 textSupply) $$ [F879 Hi S879']
  · iframe F879 Hi S879'
  icases ReadRegister.iface_of_ifaceR n ta A $$ HI with ⟨HI, -⟩
  ihave Lo := stk_join n ((s - 80).toNat - 400) 80 320 $$ [Lo80 Lo]
  · iframe Lo80
    iapply stk_addr _ $$ Lo; omega
  ihave Lo : stk n ((s - 80).toNat - SP) SP $$ [Hx Lo]
  · iapply BorshFT.stkJ (n := n) (a := (s - 80).toNat - SP) (b := (s - 80).toNat - 400) (k1 := SP - 400)
      (k2 := 80 + 320) (k := SP) (by omega) (by omega)
    isplitl [Hx]
    · iapply BorshFT.stkA (by omega) $$ Hx
    · iapply BorshFT.stkA (by omega) $$ Lo
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 363) (a := A 363) (type := types[49]!) (inst := inst) (mi := mi)
    (code := f363) [.i32 (s - 80 + 8), .i64 ((1 : UInt32) ^^^ 1).toUInt64, .i64 (t0 + lo),
      .i64 (t1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (t0 + lo) t0)).toUInt64), .i32 1053040])
  isplitr
  · iexact S363
  isplitr
  · iexact F363
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha363, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [activation363]; mstep_norm_full; omega
  isplitl [Hg Lo HH HI HPS Hinv Hvt HD HLut Hhost]
  · isplitr
    · ipureintro; rfl
    iunfold pPre
    iframe Hg HH HI HPS Hinv Hvt HD HLut Hhost
    iexact Lo
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexists h2
    iframe HT
    ipureintro; exact hpost

end Sup

end WNear.Binary.InternalDepositOverflow
