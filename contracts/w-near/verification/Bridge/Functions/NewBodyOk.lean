import Bridge.Methods.StaticsNew
import Bridge.Functions.NewHost

/-!
# The body of `new` (function 290): the success path

```wat
;; bodyA290: sp0 = sp - 64, setup_panic_hook, set_blockchain_interface
attached_deposit(sp0 + 8)                       ;; 529: no deposit
state_exists() → false                          ;; 552: STATE absent
Contract::new(sp0 + 24)                         ;; 289: the token, measure_account_storage_usage
state_write(sp0 + 24)                           ;; 220: STATE := borsh(token)
drop(sp0 + 48)                                  ;; 68: the prefix Vec freed
sp += 64; return
```

`body290New`: with no deposit, `STATE` and the dummy record absent, the host goes through
`storage_has_key`, the write and removal of the dummy record and the write of `STATE`
(`NewPost`), and the body returns with the stack pointer restored, at `costNew290`.

`codeNewS`: the code the success path adds to `codeNewP` (289 and 220 with what they call).
-/

namespace WNear.Binary.NewBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply
open WNear.Binary.Interface (IfaceMod iface ifaceCode dataWord iface_of_setup)
open WNear.Binary.ReadRegister (ifaceR ifaceR_of_iface iface_of_ifaceR)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells frames)
open WNear.Binary.SetupPanicHook (hookCells)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BorshFT (join64' split64' joinB splitB stkJ stkW stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.FtTotalSupply (stk4_word)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.EnvGetters (dslot dCode depLo depHi)
open WNear.Binary.StorageHasKey (hslot hCode)
open WNear.Binary.ContractNew (code289 pre289 post289)
open WNear.Binary.StateWrite (swCode pre220 post220 stateBytes)
open WNear.Binary.MeasureUsage (mKey mVal cost404)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_zero)
open WNear.Binary.MeasureUsage (heapRoom_shift)
open WNear.Binary.DropVec (pre747 post747)
open WNear.Binary.VecWithCap (costAllocF)
open WNear.Binary.BorshSer (cost48 ftAt)
open WNear.Binary.StorageWrite (evictedRegister)

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code the success path adds (persistent): `Contract::new` (289) and `state_write` (220),
with what they call. -/
def codeNewS (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code289 e n maxP inst mi A mx ∗ swCode e n maxP inst mi A mx ∗
    A 289 ↪[wf] FuncInst.wasm types[0]! inst f289 ∗ A 220 ↪[wf] FuncInst.wasm types[0]! inst f220)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (codeNewS (GF := GF) e n maxP inst mi A mx) := by
  unfold codeNewS; infer_instance

end Res

/-- The cost of `Contract::new` (289) on the host `h`. -/
def cost289N (cfg : WasmConfig) (h : NearState) : Nat :=
  500 * cfg.regularOpCost + costAllocF cfg 1 1 + cost404 cfg 1 h (k2New cfg h)

/-- The cost of `state_write` (220) of `new`'s state, on the host `h`. -/
def cost220N (cfg : WasmConfig) (h : NearState) : Nat :=
  100 * cfg.regularOpCost +
    (70 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAllocF cfg 8 1024)) +
      (30 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost48 cfg 1))) +
    (51 * cfg.regularOpCost + (257 * cfg.regularOpCost + storageWriteUse h StateRead.stateKey 5 29)) +
    315 * cfg.regularOpCost

/-- The cost of the success path, activation excluded, `return` included. -/
def costNew290 (cfg : WasmConfig) (h : NearState) : Nat :=
  475 * cfg.regularOpCost + 1200 * cfg.regularOpCost + attachedDepositUse h +
    storageHasKeyUse h StateRead.stateKey 5 + cost289N cfg h + cost220N cfg h + 315 * cfg.regularOpCost

section New

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **`new` on an uninitialized contract, no deposit** (290): `state_exists` is false,
`Contract::new` builds the token (measuring the account usage with the dummy record), and
`state_write` stores it; the body returns with the stack pointer restored, the host as `NewPost`. -/
theorem body290New (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 idx : UInt32) (maxP len : Nat) (hroom : HeapRoomK 9 len maxP)
    (h : NearState) (hview : h.context.isView = false)
    (hdep : depLo h ||| depHi h = 0) (hS : h.storage StateRead.stateKey = none) (hM : h.storage mKey = none)
    (st : Near.TrieOverlay.State) {b : Nat} (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st b)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey) +
      (writeProofCost (contractKey h.context.currentAccountId mKey) none +
        removeProofCost (contractKey h.context.currentAccountId mKey) (some mVal)) +
      writeProofCost (contractKey h.context.currentAccountId StateRead.stateKey) none ≤ b)
    (hlim5 : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hlim69 : withinLimit h.config.maxStorageKeyLen 69 = true)
    (hvlim16 : withinLimit h.config.maxStorageValueLen 16 = true)
    (hvlim29 : withinLimit h.config.maxStorageValueLen 29 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hU : h.context.storageUsage.toNat + (85 + e) < 2 ^ 64) (Φ : Post NearState GF) :
    codeNewP e inst mi A n mx ∗ codeNewS e n maxP inst mi A mx ∗ credits Cg (costNew290 cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗ staticsNewP n ta A old k3 ∗
      staticsNewS n ta A idx maxP len ∗ mhostPt h ∗
      (∀ h4, ⌜NewPost e h h4⌝ -∗ credits Cg (cfg.regularOpCost + R) -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ mhostPt h4 -∗
        Φ.ret [] ⟨#[.i32 (s - 64)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f290.body Φ := by
  iintro ⟨#Hk, #HkS, Hc, Hg, Stk, HS, HSS, Hh, W⟩
  iunfold codeNewP at Hk
  icases Hk with ⟨#KA, #HIC, #HD, #F444, #F529, #HHC, #F436, #F551, #F552, #F521, #F448, #HPC⟩
  iunfold codeNewS at HkS
  icases HkS with ⟨#H289c, #HSW, #F289, #F220⟩
  ihave #Hdrop : DropVec.dropCode inst mi A $$ []
  · iunfold swCode at HSW
    icases HSW with ⟨-, #H, -⟩
    iexact H
  ihave #F68 : A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 $$ []
  · iunfold swCode at HSW
    icases HSW with ⟨-, -, -, -, -, -, -, #H⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at HPC
    icases HPC with ⟨-, -, #Hi⟩
    iexact Hi
  iunfold staticsNewP at HS
  icases HS with ⟨HH0, Hkey, T116, T106, HBI, HV, DS, HSl, -, -, -, K2⟩
  iunfold staticsNewS at HSS
  icases HSS with ⟨HW, HR, HU, Hvt, Hinv, KEY, Ha, Hz⟩
  have hlt := s.toNat_lt
  have hn := hm.mem
  have hg := hm.glob
  have e0 : (s - 64).toNat = s.toNat - 64 := by rw [tsub _ _ (by simp; omega)]; simp
  have e8 : (s - 64 + 8).toNat = s.toNat - 56 := by simp [UInt32.toNat_add, e0]; omega
  have e16 : (s - 64 + 16).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, e0]; omega
  have e24 : (s - 64 + 24).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, e0]; omega
  have e48 : (s - 64 + 48).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  icases stkSp 304 432 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 288 144 rfl $$ Stk with ⟨M288, Stk⟩
  icases stkSp 80 64 rfl $$ Stk with ⟨L2, Fr⟩
  icases stkSp 8 56 rfl $$ Fr with ⟨-, Fr⟩
  icases stkSp 8 48 rfl $$ Fr with ⟨O0, Fr⟩
  icases stkSp 8 40 rfl $$ Fr with ⟨O8, Fr⟩
  icases stkSp 36 4 rfl $$ Fr with ⟨FT, -⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O8 with ⟨%ob8, %hob8, O8⟩
  icases stk_bytes' $$ FT with ⟨%obF, %hobF, FT⟩
  -- the costs, on `h`
  generalize hKD : attachedDepositUse h = KD
  generalize hKH : storageHasKeyUse h StateRead.stateKey 5 = KH
  generalize hK289 : cost289N cfg h = K289
  generalize hK220 : cost220N cfg h = K220
  rw [f290_body]
  iapply segA290 cfg lim d inst mi A n g ta hm (by omega) Cg
    (1200 * cfg.regularOpCost + KD + KH + K289 + K220 + 315 * cfg.regularOpCost + R) gt s hs hal old k3
    bodyB290 Φ
  ihave L2 := stkA (b := s.toNat - 144) (by omega) $$ L2
  iframe KA Hg L2 HH0 Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by unfold costNew290; omega) $$ Hc
  iintro Hc Hg L2 HI
  icases iface_of_ifaceR n ta A $$ HI with ⟨HI, H12⟩
  icases stkSp 48 32 rfl $$ L2 with ⟨L48, L32⟩
  have t0 : types[0]!.params.length = 1 := rfl
  have ha529 := hm.funcs 529 (by decide)
  simp only [bodyB290]
  mstep; mstep; mstep
  mcall (EnvGetters.f529_spec_host cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 64) (by omega) (by omega) (s - 64 + 8) ob0 ob8 hob0 hob8 h hview) using [Hg HI DS L32 O0 O8 Hh]
  · iunfold EnvGetters.pre529
    ihave L32 := stkA (b := (s - 64).toNat - 32) (by omega) $$ L32
    ihave O0 := memBytes_addr (b := (s - 64 + 8).toNat) (by omega) $$ O0
    ihave O8 := memBytes_addr (b := (s - 64 + 8).toNat + 8) (by omega) $$ O8
    iframe Hg HI DS L32 O0 O8 Hh
    ipureintro; rfl
  iunfold EnvGetters.post529 at HQ
  icases HQ with ⟨%hrs, Hg, HI, DS, L32, O0, O8, Hh⟩
  subst hrs
  ihave O0 := memBytes_addr (b := (s - 64).toNat + 8) (by omega) $$ O0
  ihave O8 := memBytes_addr (b := (s - 64 + 16).toNat + 0) (by omega) $$ O8
  mstep
  mstep
  mstep; mstep [O0] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep; mstep [O8] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep
  rw [hdep]
  mstep
  -- state_exists()
  have t1 : types[1]!.params.length = 0 := rfl
  have ha552 := hm.funcs 552 (by decide)
  mcall (StorageHasKey.f552_spec_host cfg lim (d + 1) types[1]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 64) (by omega) (by omega) h st hacc hlim5 hcanon.1 hcanon.2 (hlink _) hproof (by omega))
      using [Hg HI HSl L32 K2 Hh]
  · iunfold StorageHasKey.pre552
    ihave L32 := stkA (b := (s - 64).toNat - 32) (by omega) $$ L32
    iframe Hg HI HSl L32 K2 Hh
    ipureintro; rfl
  iunfold StorageHasKey.post552 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HSl, L32, K2, ⟨%h2, %hq2, Hh⟩⟩
  subst hrs
  rw [hS]
  simp only [StorageRead.foundU64, show UInt64.toUInt32 0 = 0 from rfl]
  mstep
  -- the host after `storage_has_key`
  obtain ⟨st2, hacc2, hcanon2, hlink2, hproof2, he2⟩ := StorageHasKeyPost.next hq2 hcanon hlink hproof (by omega)
  have hk2 : keep h2 = keep h := (keep_of_erase he2).trans (keep_acc h _)
  have hsto2 : h2.storage = h.storage := erase_field he2 NearState.storage fun _ => rfl
  have hus2 : h2.context.storageUsage = h.context.storageUsage :=
    erase_field he2 (fun x : NearState => x.context.storageUsage) fun _ => rfl
  have hid2 : h2.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hk2
  have hcfg2 : h2.config = h.config := congrArg Keep.config hk2
  have hc2 : SameCost h2 h := sameCost_of_keep hk2
  have hc404 : cost404 cfg 1 h2 (k2New cfg h) = cost404 cfg 1 h (k2New cfg h) :=
    cost404_congr cfg 1 hc2 (by rw [hsto2]) _
  have hK289' : 500 * cfg.regularOpCost + costAllocF cfg 1 1 + cost404 cfg 1 h2 (k2New cfg h) = K289 := by
    rw [hc404, ← hK289]; rfl
  -- Contract::new(sp0 + 24)
  ihave M288 := stkA (b := s.toNat - 432) (by omega) $$ M288
  ihave X := stkJ (a := s.toNat - 432) (b := s.toNat - 144) (k1 := 288) (k2 := 48) (k := 336) (by omega) rfl
    $$ [M288 L48]
  · iframe M288 L48
  ihave X := stkJ (a := s.toNat - 432) (b := (s - 64).toNat - 32) (k1 := 336) (k2 := 32) (k := 368) (by omega)
    rfl $$ [X L32]
  · iframe X L32
  ihave X := stkA (b := (s - 64).toNat - 368) (by omega) $$ X
  ihave FT := memBytes_addr (b := (s - 64 + 24).toNat) (by omega) $$ FT
  ihave HIR : ifaceR n ta A $$ [HI H12]
  · iunfold ifaceR; iframe HI H12
  have ha289 := hm.funcs 289 (by decide)
  have ha220 := hm.funcs 220 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  ihave #S289 := ContractNew.f289_spec cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 64) (s - 64 + 24) idx maxP len [] 1 (by decide) obF (by omega) (by omega) hobF (by omega)
    (heapRoom_shift hroom (lenIn_zero len hroom.1) (by omega)) h2 st2
    (bud := b - lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey))
    ((congrArg Keep.isView hk2).trans hview) hacc2 hcanon2 hlink2 hproof2 (by rw [hid2]; omega)
    (by rw [hcfg2]; exact hlim69) (by rw [hcfg2]; exact hvlim16) (by rw [hcfg2]; exact hreg)
    (by rw [hsto2]; exact hM) (by rw [hus2]; exact hU) (k2New cfg h) (hK2_of cfg e h h2 hc2) $$ H289c
  mstep; mstep; mstep
  mcall S289 using [Hg X HIR HU HW HR Hvt Hinv Ha Hz FT Hh]
  · iunfold pre289
    iframe Hg X HIR HU HW HR Hvt Hinv Ha Hz FT Hh
    ipureintro; rfl
  iunfold post289 at HQ
  icases HQ with ⟨%hrs, Hg, X, HIR, HU, HW, HR, Hvt, Ha, Hz, ⟨%q, %len', %⟨hq0, hqb, hl'⟩, Hinv, Hft, Hq⟩,
    ⟨%h3, %hq3, Hh⟩⟩
  subst hrs
  mcredits (300 * cfg.regularOpCost + K220 + 315 * cfg.regularOpCost + R)
  -- the host after `measure_account_storage_usage`
  obtain ⟨h1, s1, st3, he1, he3, hacc3, hcanon3, hlink3, hproof3⟩ := after404 hq3 (by rw [hid2]; omega)
  have hk3 : keep h3 = keep h := (keep_after404 he1 he3).trans hk2
  have hsto3 : h3.storage StateRead.stateKey = none := by
    rw [storage_after404 he1 he3, if_neg stateKey_ne_mKey, hsto2, hS]
  have hid3 : h3.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hk3
  have hcfg3 : h3.config = h.config := congrArg Keep.config hk3
  have hc3 : SameCost h3 h := sameCost_of_keep hk3
  have hcW : storageWriteUse h3 WNear.stateKey 5 29 =
      storageWriteUse h StateRead.stateKey 5 29 := by rw [← StateRead.stateKey_eq]; exact storageWriteUse_congr hc3 (by rw [hsto3, hS]) _ _
  have hK220' : 100 * cfg.regularOpCost +
      (70 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAllocF cfg 8 1024)) +
        (30 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost48 cfg 1))) +
      (51 * cfg.regularOpCost + (257 * cfg.regularOpCost +
        storageWriteUse h3 WNear.stateKey 5 29)) + 315 * cfg.regularOpCost = K220 := by
    rw [hcW, ← hK220]; rfl
  -- state_write(sp0 + 24)
  icases stkSp 224 144 rfl $$ X with ⟨X224, X144⟩
  ihave X144 := stkA (b := (s - 64).toNat - 144) (by omega) $$ X144
  icases iface_of_ifaceR n ta A $$ HIR with ⟨HI, H12⟩
  ihave #S220 := StateWrite.f220_spec cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 64) (s - 64 + 24) q 1 idx maxP len' [(q.toNat, 1)] 8 (by decide) (List.replicate 8 0)
    (List.replicate 8 0) (storeBytes (.i64 (UInt64.ofNat (85 + e))) 8) [97] (by omega) (by omega) (by simp)
    (by simp) (U128From.storeBytes_length _ _) rfl (by decide) (by omega) (by simp; omega)
    (roomFor_ofK 1024 (by decide) hroom hl' (by omega)) h3 st3
    (b := b - lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey) -
      (writeProofCost (contractKey h2.context.currentAccountId mKey) none +
        removeProofCost (contractKey h2.context.currentAccountId mKey) (some mVal)))
    ((congrArg Keep.isView hk3).trans hview) hacc3 (by rw [hcfg3]; exact hlim5) (by rw [hcfg3]; exact hvlim29)
    hcanon3.1 hcanon3.2 (hlink3 _) hproof3 (by simp only [← StateRead.stateKey_eq] at *; rw [hid3, hsto3, hid2]; omega)
    (by intro v hv; simp only [← StateRead.stateKey_eq] at hv; rw [hsto3] at hv; cases hv) $$ HSW
  mstep; mstep; mstep
  ihave KEY : n ↦[wms][ 1049788 ] WNear.stateKey $$ [KEY]
  · rw [← StateRead.stateKey_eq]; iexact KEY
  mcall S220 using [Hg X144 HI HW Hvt Hinv Hft Hq KEY Hh]
  · iunfold pre220
    iframe Hg X144 HI HW Hvt Hinv Hft Hq KEY Hh
    ipureintro; rfl
  iunfold post220 at HQ
  icases HQ with ⟨%hrs, Hg, X144, HI, HW, Hvt, ⟨%len'', %hl'', Hinv⟩, Hft, Hq, KEY, ⟨%h4, %hq4, Hh⟩⟩
  subst hrs
  obtain ⟨s4', -, -, he4⟩ := hq4
  have hpost : NewPost e h h4 := by
    refine ⟨h2, h1, h3, st2, s1, st3, s4'.set (contractKey h3.context.currentAccountId WNear.stateKey) (newBytes e),
      he2, he1, he3, ?_⟩
    rw [StateRead.stateKey_eq]; exact he4
  -- drop(sp0 + 48): the prefix `Vec` freed
  iunfold ftAt at Hft
  icases Hft with ⟨F0, F8, F16, F24⟩
  ihave F24 := BorshFT.splitB (n := n) (a := (s - 64 + 24).toNat + 24) (b := (s - 64 + 24).toNat + 24 + 4)
    (bytes32 q) (bytes32 1 ++ bytes32 1) (by simp [bytes32]) $$ F24
  icases F24 with ⟨P0, P48⟩
  ihave P48 := KeyGet.split64 n ((s - 64 + 24).toNat + 24 + 4) 1 1 $$ P48
  icases P48 with ⟨P4, P8⟩
  ihave Blk : AllocInv.block n q.toNat 1 $$ [Hq]
  · iunfold AllocInv.block
    iexists [97]
    iframe Hq
    ipureintro; rfl
  mstep; mstep; mstep
  mcall (DropVec.f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len''
      [(q.toNat, UInt32.toNat 1)] 9 (s - 64 + 48) q 1 1 (by decide) (by omega)) using [P0 P4 P8 Hinv Blk]
  · iunfold pre747
    ihave P0 := memBytes_addr (b := (s - 64 + 48).toNat) (by omega) $$ P0
    ihave P4 := memBytes_addr (b := (s - 64 + 48).toNat + 4) (by omega) $$ P4
    ihave P8 := memBytes_addr (b := (s - 64 + 48).toNat + 8) (by omega) $$ P8
    simp only [UInt32.reduceToNat]
    iframe P0 P4 P8 Hinv Blk
    ipureintro; exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, Hinv⟩
  subst hrs
  -- sp += 64; return
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 64 + 64 = s by simp]
  mcredits (cfg.regularOpCost + R)
  mstep
  iapply W $$ %h4 %hpost Hc Hg Hh

end New

end WNear.Binary.NewBody
