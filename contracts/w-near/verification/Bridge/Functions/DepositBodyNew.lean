import Bridge.Functions.DepositBody
import Bridge.Functions.Cmp128

/-!
# `near_deposit` (232) on an account not registered (M8)

After `contains_key` is false, 232 reads the bounds (418) and compares the deposit with the
minimum `N = account_storage_usage · 10^19`:

* below it: `begin_panic("ERR_DEPOSIT_TOO_SMALL")` (664, `PanicSpecD`), the host after
  `contains_key`;
* otherwise: `internal_register_account` (409, the record `0u128` written), the bounds again, the
  amount `deposit - N` (no borrow: `Cmp128.sub128_flag`), then `seg406_all` on the balance 0.

`body232_unreg`: both, by the comparison.
-/

namespace WNear.Binary.DepositBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA join64' split64' stkW stkB)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.ReadRegister (ifaceR RegOk)
open WNear.Binary.StorageWrite (wslot evictedRegister)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn cost401)
open WNear.Binary.InternalDeposit (code406 code409 Post406 zeroAt)
open WNear.Binary.DepositTail (tailCode tailStat tail232 logText)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent hookRes pPre PanicSpecD)
open WNear.Binary.DepositSeg (seg406 LenUp)
open WNear.Binary.DepositSegAll (codeSeg costSegAll seg406_all)
open WNear.Binary.InternalDepositOverflow (balMsg textSupply)
open WNear.Binary.NewBody (keep keep_of_erase keep_acc keep_storageWriteHost)
open WNear.Binary.EnvGetters (dslot dCode depLo depHi)
open WNear.Binary.EnvPredecessor (pslot)
open WNear.Binary.StorageHasKey (hslot)
open WNear.Binary.PredecessorId (code526 strAt cost526)
open WNear.Binary.LookupMapContains (code394 cost394)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.StorageBalanceBounds (xOf boundsBytes u128Of)

/-- The minimum, from the `account_storage_usage` bytes `xb`. -/
abbrev minOf (xb : List UInt8) : Nat := (xOf xb).toNat * 10000000000000000000

/-- The minimum's words. -/
abbrev mloOf (xb : List UInt8) : UInt64 := UInt64.ofNat (minOf xb)
abbrev mhiOf (xb : List UInt8) : UInt64 := UInt64.ofNat (minOf xb / 18446744073709551616)

/-- The amount's words: `deposit - minimum`. -/
abbrev aloOf (h : NearState) (xb : List UInt8) : UInt64 := depLo h - mloOf xb
abbrev ahiOf (h : NearState) (xb : List UInt8) : UInt64 :=
  depHi h - mhiOf xb - (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (depLo h) (mloOf xb))).toUInt64

theorem minOf_words (xb : List UInt8) : (mloOf xb).toNat + 2 ^ 64 * (mhiOf xb).toNat = minOf xb := by
  have := StorageBalanceBounds.mul_price_lt (xOf xb)
  simp only [mloOf, mhiOf, minOf]
  simp
  omega

/-- The host with `v` stored under `k`. -/
def withVal (h : NearState) (k v : List UInt8) : NearState :=
  { h with storage := fun k' => if k' = k then some v else h.storage k' }

theorem keep_withVal (h : NearState) (k v : List UInt8) : keep (withVal h k v) = keep h := rfl

/-- The zero `u128` the registration stores. -/
abbrev zeros : List UInt8 := List.replicate 8 0 ++ List.replicate 8 0

theorem zeros_eq : zeros = storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8 := by decide

/-- The cost of 232 on an account not registered, activation excluded, the function's exit
included. -/
noncomputable def costUnreg (cfg : WasmConfig) (F : Nat) (pl : UInt32) (h : NearState) (key : List UInt8)
    (xb : List UInt8) (t0 t1 : UInt64) (ab : List UInt8) (K879 K664 : Nat → NewBody.Keep → Nat) : Nat :=
  1800 * cfg.regularOpCost + attachedDepositUse h + cost526 cfg F h +
    cost394 cfg F pl (UInt32.ofNat ab.length) (predecessorHost h 0) key +
    if depOf h < minOf xb then K664 (F + 2) (keep h)
    else 1500 * cfg.regularOpCost +
      cost401 cfg (F + 2) pl (UInt32.ofNat ab.length) h key +
      costSegAll cfg (F + 5) pl (UInt32.ofNat ab.length) (withVal h key zeros) key 0 0 t0 t1 (aloOf h xb)
        (ahiOf h xb) ab K879

open Near.TrieOverlay in
/-- What 232 leaves of the host on an account not registered: `contains_key` (`h2`), the record
written (`h3`), 406 (`h4`), the log. -/
def PostNew (e : Nat) (h : NearState) (key nv : List UInt8) (st : Near.TrieOverlay.State) (bud : Nat)
    (text : List UInt8) (h' : NearState) : Prop :=
  ∃ (h2 : NearState) (s2 : Near.TrieOverlay.State) (h3 : NearState) (s3 : Near.TrieOverlay.State) (h4 : NearState),
    StorageHasKeyPost (predecessorHost h 0) key st h2 ∧ h2.storageAccounting = some s2 ∧ Canon s2 ∧
    StorageLink h2 s2 ∧ ProofBudget h2 s2 (bud - lookupProofBound (contractKey h.context.currentAccountId key)) ∧
    erase h2 = erase { predecessorHost h 0 with storageAccounting := some s2 } ∧
    StorageWritePost e h2 key zeros evictedRegister s2 h3 ∧ h3.storageAccounting = some s3 ∧ Canon s3 ∧
    StorageLink h3 s3 ∧
    ProofBudget h3 s3 (bud - lookupProofBound (contractKey h.context.currentAccountId key) -
      writeProofCost (contractKey h.context.currentAccountId key) none) ∧
    erase h3 = erase (storageWriteHost e h2 key zeros evictedRegister s3) ∧
    Post406 e h3 key nv s3 (bud - lookupProofBound (contractKey h.context.currentAccountId key) -
      writeProofCost (contractKey h.context.currentAccountId key) none) h4 ∧
    h' = LogStr.logged h4 text

theorem dcase_small_text (dep m T : Nat) (hd : dep ≠ 0) (hs : dep < m) :
    (dcase dep none m T).text = NearDepositPanics.textTooSmall := by
  unfold dcase
  rw [if_neg hd, if_pos ⟨rfl, hs⟩]; rfl

theorem dcase_small_eq (dep m T : Nat) (hd : dep ≠ 0) (hs : dep < m) : dcase dep none m T = .small := by
  unfold dcase
  rw [if_neg hd, if_pos ⟨rfl, hs⟩]

theorem dcase_new_ok (dep m T : Nat) (hd : dep ≠ 0) (hs : ¬ dep < m) (h1 : 0 + (dep - m) < 2 ^ 128)
    (h2 : T + (dep - m) < 2 ^ 128) : dcase dep none m T = .ok := by
  unfold dcase amountOf
  rw [if_neg hd, if_neg (fun h => hs h.2), Option.getD_none, if_neg (Nat.not_le.mpr h1), if_neg (Nat.not_le.mpr h2)]

theorem dcase_new_text (dep m T : Nat) (hd : dep ≠ 0) (hs : ¬ dep < m)
    (hno : ¬ (0 + (dep - m) < 2 ^ 128 ∧ T + (dep - m) < 2 ^ 128)) :
    (dcase dep none m T).text = if 0 + (dep - m) < 2 ^ 128 then textSupply else balMsg := by
  unfold dcase amountOf
  rw [if_neg hd, if_neg (fun h => hs h.2), Option.getD_none]
  by_cases h1 : 0 + (dep - m) < 2 ^ 128
  · have h2 : ¬ (T + (dep - m) < 2 ^ 128) := fun h2 => hno ⟨h1, h2⟩
    rw [if_neg (Nat.not_le.mpr h1), if_pos (Nat.le_of_not_lt h2), if_pos h1]; rfl
  · rw [if_pos (Nat.le_of_not_lt h1), if_neg h1]; rfl

theorem dcase_new_nok (dep m T : Nat) (hd : dep ≠ 0) (hs : ¬ dep < m)
    (hno : ¬ (0 + (dep - m) < 2 ^ 128 ∧ T + (dep - m) < 2 ^ 128)) : dcase dep none m T ≠ .ok := by
  intro hc
  have := dcase_new_text dep m T hd hs hno
  rw [hc] at this
  by_cases h1 : 0 + (dep - m) < 2 ^ 128
  · rw [if_pos h1] at this; exact absurd this (by decide +kernel)
  · rw [if_neg h1] at this; exact absurd this (by decide +kernel)

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem boundsBytes_split (n a N : Nat) :
    n ↦[wms][ a ] boundsBytes N ⊢ (n ↦[wms][ a ] storeBytes (.i64 (UInt64.ofNat N)) 8 ∗
      n ↦[wms][ a + 8 ] storeBytes (.i64 (UInt64.ofNat (N / 2 ^ 64))) 8 ∗
      n ↦[wms][ a + 16 ] (storeBytes (.i64 1) 8 ++ u128Of N) : IProp GF) := by
  iintro H
  iunfold boundsBytes, u128Of, u128Bytes at H
  rw [List.append_assoc, List.append_assoc] at *
  icases splitB (a := a) (b := a + 8) (storeBytes (.i64 (UInt64.ofNat N)) 8) _ (by simp) $$ H with ⟨H0, H⟩
  icases splitB (a := a + 8) (b := a + 16) (storeBytes (.i64 (UInt64.ofNat (N / 2 ^ 64))) 8) _ (by simp) $$ H
    with ⟨H8, H⟩
  iframe H0 H8
  iunfold u128Of, u128Bytes
  iexact H

theorem boundsBytes_join (n a N : Nat) :
    (n ↦[wms][ a ] storeBytes (.i64 (UInt64.ofNat N)) 8 ∗
      n ↦[wms][ a + 8 ] storeBytes (.i64 (UInt64.ofNat (N / 2 ^ 64))) 8 ∗
      n ↦[wms][ a + 16 ] (storeBytes (.i64 1) 8 ++ u128Of N) : IProp GF) ⊢ n ↦[wms][ a ] boundsBytes N := by
  iintro ⟨H0, H8, H⟩
  iunfold boundsBytes
  iunfold u128Of, u128Bytes
  rw [List.append_assoc, List.append_assoc]
  iapply joinB (a := a) (b := a + 8) (storeBytes (.i64 (UInt64.ofNat N)) 8) _ (by simp)
  iframe H0
  iapply joinB (a := a + 8) (b := a + 16) (storeBytes (.i64 (UInt64.ofNat (N / 2 ^ 64))) 8) _ (by simp)
  iframe H8
  iunfold u128Of, u128Bytes at H
  iexact H

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **232 on an account not registered**: the deposit, the predecessor, `contains_key` false, the
bounds; below the minimum `begin_panic` (664), otherwise the registration, the amount
`deposit - minimum`, then `seg406_all` on the balance 0. -/
theorem body232_unreg (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat)
    (hd : d + 27 + D < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s self : UInt32) (SP : Nat) (hSP : 400 ≤ SP)
    (hs : 144 + 80 + SP ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hal : s.toNat % 8 = 0)
    (hthis : self.toNat + 40 ≤ 2 ^ 32) (pp pc pl : UInt32) (pre : List UInt8)
    (hpre : pre.length = pl.toNat) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
    (t0 t1 : UInt64) (xb : List UInt8) (hxb : xb.length = 8) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (hroom : HeapRoomK 21 hl maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlimR : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true)
    (hutf : Utf8.utf8Ok h.context.predecessorAccountId = true)
    (hab : h.context.predecessorAccountId.length ≤ 64) (hab0 : 0 < h.context.predecessorAccountId.length)
    (hlim : withinLimit h.config.maxStorageKeyLen
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hbud : 4 * lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) + 48 ≤ bud)
    (hnone : h.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
      h.context.predecessorAccountId)) = none)
    (hdep : depLo h ||| depHi h ≠ 0)
    (hlog : ∀ lo hi : UInt64, LogStr.LogOk h (logText lo hi h.context.predecessorAccountId)
      (logText lo hi h.context.predecessorAccountId).length)
    (hfit16 : LogFits h 16) (hov16 : h.extCosts.cost "read_memory_byte" * 16 < 2 ^ 64)
    (hfitS : LogFits h textSupply.length) (hovS : h.extCosts.cost "read_memory_byte" * textSupply.length < 2 ^ 64)
    (hfitT : LogFits h NearDepositPanics.textTooSmall.length)
    (hovT : h.extCosts.cost "read_memory_byte" * NearDepositPanics.textTooSmall.length < 2 ^ 64)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K879 K664 : Nat → NewBody.Keep → Nat)
    (H879 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f879 SP Dp D 1053016 21 1053040 K879 textSupply)
    (H664 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f664 SP Dp D 1050556 21 1050580 K664
      NearDepositPanics.textTooSmall)
    (Φ : Post NearState GF) :
    code232 e n maxP inst mi A mx ∗ C ∗
      credits Cg (costUnreg cfg F pl h
        (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))
        xb t0 t1 h.context.predecessorAccountId K879 K664 + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (224 + SP)) (224 + SP) ∗
      selfCells n self (storeBytes (.i64 t0) 8 ++ storeBytes (.i64 t1) 8) xb pp pc pl pre ∗
      stat232 n ta A lpc Dp aidx ∗ heapInv n maxP hl live F ∗ mhostPt h ∗
      (∀ (hl' F' : Nat) (h' : NearState) (f' : Frame),
        ⌜F' ≤ F + 16 ∧ LenUp hl 16 hl' ∧
          PostNew e h (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
              h.context.predecessorAccountId))
            (StorageBalanceBounds.u128Of (0 + 2 ^ 64 * 0 + ((aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat))) st bud
            (logText (aloOf h xb) (ahiOf h xb) h.context.predecessorAccountId) h' ∧
          dcase (depOf h) none (minOf xb) (t0.toNat + 2 ^ 64 * t1.toNat) = .ok⌝ -∗
        credits Cg (cfg.regularOpCost + R) -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗
        stk n (s.toNat - (224 + SP)) (224 + SP) -∗
        selfCells n self (StorageBalanceBounds.u128Of (t0.toNat + 2 ^ 64 * t1.toNat +
          ((aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat))) xb pp pc pl pre -∗
        stat232 n ta A lpc Dp aidx -∗ heapInv n maxP hl' live F' -∗ mhostPt h' -∗ Φ.ret [] f') ∗
      (∀ hX, ⌜keep hX = keep h ∧ dcase (depOf h) none (minOf xb) (t0.toNat + 2 ^ 64 * t1.toNat) ≠ .ok⌝ -∗
        panicked Cg hX (dcase (depOf h) none (minOf xb) (t0.toNat + 2 ^ 64 * t1.toNat)).text -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 self, .i32 0, .i64 0, .i64 0, .i32 0, .i64 0, .i64 0], inst, mi⟩ [] f232.body Φ := by
  iintro ⟨#Hk, #HC, Hc, Hg, Stk, HS, HT, Hinv, Hh, Wok, Wtr⟩
  iunfold code232 at Hk
  icases Hk with ⟨#Hseg, #HD, #F444, #F529, #H526c, #F526, #H394c, #F394, #F418, #F553, #F954, #F566, #H409c,
    #F409, #F664⟩
  ihave #HIC : ifaceCode e inst mi A n mx $$ []
  · iunfold codeSeg, tailCode at Hseg
    icases Hseg with ⟨-, ⟨-, -, -, #H, -⟩, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold Interface.ifaceCode at HIC
    icases HIC with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  iunfold stat232 at HT
  icases HT with ⟨HI, H12, HDs, HPs, HHs, HWs, HLs, HPS, HH, HDp, HM, HZ, HSt, HU8, Hvt⟩
  iunfold selfCells at HS
  icases HS with ⟨HTb, HX, HP, HPre⟩
  icases splitB (a := self.toNat) (b := self.toNat + 8) (storeBytes (.i64 t0) 8) _ (by simp) $$ HTb with ⟨Ht0, Ht8⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hLn : (UInt32.ofNat h.context.predecessorAccountId.length).toNat = h.context.predecessorAccountId.length := by
    simp; omega
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [StorageBalanceBounds.tsub' _ _ (by simp; omega)]; simp
  have e24 : (s - 144 + 24).toNat = s.toNat - 120 := by simp [UInt32.toNat_add, e0]; omega
  have e32 : (s - 144 + 32).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have e40 : (s - 144 + 40).toNat = s.toNat - 104 := by simp [UInt32.toNat_add, e0]; omega
  have e48 : (s - 144 + 40 + 8).toNat = s.toNat - 96 := by simp [UInt32.toNat_add, e0]; omega
  have e56 : (s - 144 + 56).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, e0]; omega
  have e72 : (s - 144 + 72).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  have e80 : (s - 144 + 72 + 8).toNat = s.toNat - 64 := by simp [UInt32.toNat_add, e0]; omega
  have es24 : (self + 24).toNat = self.toNat + 24 := by simp [UInt32.toNat_add]; omega
  -- the frame
  icases stkSp (80 + SP) 144 (by omega) $$ Stk with ⟨Lo, Fr⟩
  icases stkSp 24 120 rfl $$ Fr with ⟨F0, Fr⟩
  icases stkSp 8 112 rfl $$ Fr with ⟨O0, Fr⟩
  icases stkSp 8 104 rfl $$ Fr with ⟨O8, Fr⟩
  icases stkSp 8 96 rfl $$ Fr with ⟨U0, Fr⟩
  icases stkSp 8 88 rfl $$ Fr with ⟨U8, Fr⟩
  icases stkSp 12 76 rfl $$ Fr with ⟨V, Fr⟩
  icases stkSp 4 72 rfl $$ Fr with ⟨F68, Fr⟩
  icases stkSp 40 32 rfl $$ Fr with ⟨F72, Fr⟩
  icases stkSp 12 20 rfl $$ Fr with ⟨F112, Fr⟩
  icases stkSp 4 16 rfl $$ Fr with ⟨F124, F128⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O8 with ⟨%ob8, %hob8, O8⟩
  icases stk_bytes' $$ U0 with ⟨%ub0, %hub0, U0⟩
  icases stk_bytes' $$ U8 with ⟨%ub8, %hub8, U8⟩
  icases stk_bytes' $$ V with ⟨%vb, %hvb, V⟩
  icases stk_bytes' $$ F72 with ⟨%obb, %hobb, F72⟩
  iunfold costUnreg at Hc
  generalize hKD : attachedDepositUse h = KD
  generalize hK526 : cost526 cfg F h = K526
  generalize hK394 : cost394 cfg F pl (UInt32.ofNat h.context.predecessorAccountId.length) (predecessorHost h 0) (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) = K394
  generalize hK401 : cost401 cfg (F + 2) pl (UInt32.ofNat h.context.predecessorAccountId.length) h (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) = K401
  generalize hKS : costSegAll cfg (F + 5) pl (UInt32.ofNat h.context.predecessorAccountId.length) (withVal h (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) zeros) (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) 0 0 t0 t1 (aloOf h xb) (ahiOf h xb) h.context.predecessorAccountId K879 = KS
  generalize hK664 : K664 (F + 2) (keep h) = K6
  simp only [f232]
  -- the prologue
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 529: the deposit at sp + 24
  have t0' : types[0]!.params.length = 1 := rfl
  have ha529 := hm.funcs 529 (by decide)
  have ha526 := hm.funcs 526 (by decide)
  have ha394 := hm.funcs 394 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  icases stkSp (80 + SP - 32) 32 (by omega) $$ Lo with ⟨Lo, L32⟩
  mstep; mstep; mstep
  mcall (EnvGetters.f529_spec_host cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 144) (by omega) (by omega) (s - 144 + 24) ob0 ob8 hob0 hob8 h hview) using [Hg HI HDs L32 O0 O8 Hh]
  · iunfold EnvGetters.pre529
    ihave L32 := stkA (b := (s - 144).toNat - 32) (by omega) $$ L32
    ihave O0 := memBytes_addr (b := (s - 144 + 24).toNat) (by omega) $$ O0
    ihave O8 := memBytes_addr (b := (s - 144 + 24).toNat + 8) (by omega) $$ O8
    iframe Hg HI HDs L32 O0 O8 Hh
    ipureintro; rfl
  iunfold EnvGetters.post529 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HDs, L32, O0, O8, Hh⟩
  subst hrs
  ihave O0 := memBytes_addr (b := (s - 144).toNat + 24) (by omega) $$ O0
  ihave O8 := memBytes_addr (b := (s - 144 + 32).toNat + 0) (by omega) $$ O8
  ihave U0 := memBytes_addr (b := (s - 144).toNat + 40) (by omega) $$ U0
  ihave U8 := memBytes_addr (b := (s - 144).toNat + 48) (by omega) $$ U8
  mstep; mstep; mstep; mstep; mstep [O8] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [U8] with simp
  mstep; mstep; mstep [O0] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [U0] with simp
  -- the blocks, the test of the deposit
  mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (simp [Numeric.bool, Numeric.irelop64, hdep])
  -- 526: the predecessor at sp + 56
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L32
  icases stkSp (80 + SP - 208) 208 (by omega) $$ Lo with ⟨Lo, L208⟩
  ihave HIR : ifaceR n ta A $$ [HI H12]
  · iunfold ifaceR; iframe HI H12
  have hroomR : roomFor hl maxP (UInt32.ofNat h.context.predecessorAccountId.length) :=
    LookupMapOps.roomFor_ofK (k := 21) (UInt32.ofNat h.context.predecessorAccountId.length) (by omega) hroom
      (LookupMapOps.lenIn_zero hl hroom.1) (by omega)
  mstep; mstep; mstep
  mcall (PredecessorId.f526_spec cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt (s - 144)
      (s - 144 + 56) (by omega) (by omega) (by omega) aidx maxP hl live F hF vb hvb h hview hvalid hlimR
      ⟨hab0, by omega, hroomR⟩ hutf) using [Hg HIR HPs L208 Hvt Hinv V HU8 Hh]
      with (rw [hK526]; mstep_norm_full; omega)
  · iunfold PredecessorId.pre526
    ihave L208 := stkA (b := (s - 144).toNat - 208) (by omega) $$ L208
    ihave V := memBytes_addr (b := (s - 144 + 56).toNat) (by omega) $$ V
    iframe Hg HIR HPs L208 Hvt Hinv V HU8 Hh
    ipureintro; rfl
  iunfold PredecessorId.post526 at HQ
  icases HQ with ⟨%hrs, Hg, HIR, HPs, L208, Hvt, HSA, HU8, Hh⟩
  subst hrs
  iunfold strAt at HSA
  icases HSA with ⟨%p, %hl1, %⟨hp0, hhl1⟩, Hinv, Hab, V0, V4, V8⟩
  have hlen1 : LenIn hl 1 hl1 := LookupMapOps.lenIn_step (UInt32.ofNat h.context.predecessorAccountId.length)
    (by omega) (LookupMapOps.lenIn_zero hl hroom.1) hhl1
  icases AllocZeroed.heapInv_bound n maxP hl1 _ F $$ Hinv with ⟨%⟨hbnd, -⟩, Hinv⟩
  have hpb : p.toNat + h.context.predecessorAccountId.length ≤ 2 ^ 32 := by
    have := hbnd p.toNat h.context.predecessorAccountId.length List.mem_cons_self
    have := hroom.2.2.2
    have := hlen1.2.1
    omega
  ihave V := joinB (a := (s - 144 + 56).toNat) (b := (s - 144 + 56).toNat + 4) (bytes32 p) _ (by simp [bytes32])
    $$ [V0 V4 V8]
  · iframe V0
    iapply join64' (a := (s - 144 + 56).toNat + 4) (b := (s - 144 + 56).toNat + 4 + 4) _ _ rfl
    iframe V4 V8
  -- the host after 526
  have hk1 : keep (predecessorHost h 0) = keep h := keep_predecessorHost h
  have f1 : (predecessorHost h 0).storageAccounting = h.storageAccounting ∧ (predecessorHost h 0).config = h.config ∧
      (predecessorHost h 0).storage = h.storage ∧ (predecessorHost h 0).context = h.context ∧
      (predecessorHost h 0).storageProofSize = h.storageProofSize := by
    simp [predecessorHost, u64Max, NearState.setRegister]
  obtain ⟨f1a, f1c, f1s, f1x, f1p⟩ := f1
  -- 394: contains_key
  icases stkSp 32 176 rfl $$ L208 with ⟨L32', L176⟩
  icases ReadRegister.iface_of_ifaceR n ta A $$ HIR with ⟨HI, H12⟩
  mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapContains.f394_spec cfg lim (d + 1) types[13]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 144) (self + 24) pp pc pl (s - 144 + 56) p (UInt32.ofNat h.context.predecessorAccountId.length)
      (UInt32.ofNat h.context.predecessorAccountId.length) aidx maxP hl1
      ((p.toNat, h.context.predecessorAccountId.length) :: live) F hF pre h.context.predecessorAccountId
      (by omega) (by omega) hpre hLn.symm (by omega) hpl hl0 hpp (by omega) (by omega)
      (MeasureUsage.heapRoom_shift hroom hlen1 (by omega)) (predecessorHost h 0) st (by rw [f1a]; exact hacc)
      (by rw [f1c]; exact hlim) hcanon.1 hcanon.2 (by rw [f1s, f1x]; exact hlink _) (hproof.congr f1p f1c)
      (by rw [f1x]; omega)) using [Hg L176 HI HHs Hvt Hinv HP HPre V Hab Hh]
      with (simp only [t13]; rw [hK394]; mstep_norm_full; omega)
  · iunfold LookupMapContains.pre394
    ihave L176 := stkA (b := (s - 144).toNat - 176) (by omega) $$ L176
    iframe Hg L176 HI HHs Hvt Hinv HP HPre V Hab Hh
    ipureintro; rfl
  iunfold LookupMapContains.post394 at HQ
  icases HQ with ⟨%hrs, Hg, L176, HI, HHs, Hvt, ⟨%hl2, %hlen2, Hinv⟩, HP, HPre, V, Hab, ⟨%h2, %hq2, Hh⟩⟩
  subst hrs
  rw [show (predecessorHost h 0).storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
    h.context.predecessorAccountId)) = h.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
    h.context.predecessorAccountId)) by rw [f1s], hnone]
  simp only [StorageRead.foundU64]
  mstep_not_taken with (rfl)
  -- the host after 394
  obtain ⟨s2, hacc2, hcan2, hlink2, hp2, he2⟩ := StorageHasKeyPost.next hq2 hcanon
    (by intro k; rw [f1s, f1x]; exact hlink k) (hproof.congr f1p f1c) (by rw [f1x]; omega)
  have hk2 : keep h2 = keep h := by rw [keep_of_erase he2, keep_acc, hk1]
  have hs2 : h2.storage = h.storage := by rw [erase_field he2 NearState.storage fun _ => rfl]; exact f1s
  have hc2 : h2.config = h.config := by rw [erase_field he2 NearState.config fun _ => rfl]; exact f1c
  have hid2 : h2.context.currentAccountId = h.context.currentAccountId := by
    rw [erase_field he2 (fun x : NearState => x.context.currentAccountId) fun _ => rfl]; rw [f1x]
  have hv2 : h2.context.isView = h.context.isView := by
    rw [erase_field he2 (fun x : NearState => x.context.isView) fun _ => rfl]; rw [f1x]
  have hx2' : h2.extCosts = h.extCosts := congrArg NewBody.Keep.extCosts hk2
  have hb2 : bud - lookupProofBound (contractKey (predecessorHost h 0).context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) =
      bud - lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) := by
    rw [f1x]
  rw [hb2] at hp2
  have hlen12 : LenIn hl 3 hl2 := MeasureUsage.lenIn_trans hlen1 hlen2
  -- 418: the bounds at sp + 72
  have ha418 := hm.funcs 418 (by decide)
  have h418 : StorageBalanceBounds.cost418 cfg = 314 * cfg.regularOpCost := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  icases stkSp 96 80 rfl $$ L176 with ⟨L96, L80⟩
  mstep; mstep; mstep; mstep
  mcall (StorageBalanceBounds.f418_spec cfg lim (d + 1) types[14]! rfl inst mi n g (A 553) (A 954) (A 566) hn hg
      (hm.funcs 553 (by decide)) (hm.funcs 954 (by decide)) (hm.funcs 566 (by decide)) (by omega) Cg gt (s - 144)
      (s - 144 + 72) self (by omega) (by omega) obb xb hobb hxb) using [Hg L80 F72 HX]
      with (simp only [StorageBalanceBounds.cost418]; mstep_norm_full; omega)
  · iunfold StorageBalanceBounds.pre418
    ihave L80 := stkA (b := (s - 144).toNat - 80) (by omega) $$ L80
    ihave F72 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ F72
    iframe Hg L80 F72 HX
    ipureintro; rfl
  iunfold StorageBalanceBounds.post418 at HQ
  icases HQ with ⟨%hrs, Hg, L80, Hb, HX⟩
  subst hrs
  -- the comparison of the deposit with the minimum
  have hmw := minOf_words xb
  icases boundsBytes_split n _ _ $$ Hb with ⟨B0, B8, Brest⟩
  ihave B0 := memBytes_addr (b := (s - 144).toNat + 72) (by omega) $$ B0
  ihave B8 := memBytes_addr (b := (s - 144 + 72 + 8).toNat + 0) (by omega) $$ B8
  mstep; mstep; mstep [B0] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [B8] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep
  mstep; mstep; mstep
  iapply mwpi_cons
  iapply FmtGrow.mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega, trivial⟩
  inext
  iintro Hc
  mctrl_norm
  rw [← apply_ite Value.i32, Cmp128.ge128_flag (depLo h) (depHi h)
    (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000))
    (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000 / 18446744073709551616)), hmw]
  have hdep0 : depOf h ≠ 0 := by
    intro h0
    apply hdep
    exact (EnvGetters.u64_or_eq_zero _ _).2 h0
  -- the stack below the frame, whole
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L32'
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L96
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L80
  by_cases hsm : minOf xb ≤ (depLo h).toNat + 2 ^ 64 * (depHi h).toNat
  swap
  · -- below the minimum: `begin_panic("ERR_DEPOSIT_TOO_SMALL")`
    rw [if_neg hsm]
    mstep
    mstep_taken with (first | decide | simp [Numeric.bool])
    mstep; mstep; mstep
    have hsm' : depOf h < minOf xb := by simp only [depOf]; omega
    have S664 := H664 (d + 1) Cg (s - 144) h2 hl2 ((p.toNat, h.context.predecessorAccountId.length) :: live)
      (F + 2) aidx (by omega) (by omega) (by omega) (by omega) (MeasureUsage.heapRoom_shift hroom hlen12 (by omega))
      (by unfold okG at hF ⊢; omega) (InternalDepositOverflow.LogFits.of_keep hk2 hfitT) (by rw [hx2']; exact hovT)
    rw [hk2, hK664] at S664
    ihave #S664' := S664 $$ HC
    icases stkSp 80 SP (by omega) $$ Lo with ⟨-, Lo⟩
    iapply mwpi_cons
    iapply (PanicStr.mwpi_callT' (i := 664) (a := A 664) (type := types[31]!) (inst := inst) (mi := mi)
      (code := f664) [.i32 1050556, .i32 21, .i32 1050580])
    isplitr
    · iexact S664'
    isplitr
    · iexact F664
    isplitr
    · iexact Hi
    isplitr
    · ipureintro; exact ⟨rfl, hm.funcs 664 (by decide), rfl, by omega⟩
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; rw [if_pos hsm']; mstep_norm_full; omega
    isplitl [Hg Lo HH HI HPS Hinv Hvt HDp Hh]
    · isplitr
      · ipureintro; rfl
      iunfold pPre
      iframe Hg HH HI HPS Hinv Hvt HDp Hh
      iapply stkA2 (by omega) (by omega) $$ Lo
    inext
    isplit
    · iintro %rs - HF
      iexfalso
      iexact HF
    · iintro HT
      simp only [Post.mseq_trap, Post.mblock]
      iapply Wtr $$ %h2 %⟨hk2, by rw [dcase_small_eq _ _ _ hdep0 hsm']; exact fun h => DCase.noConfusion h⟩
      iapply panicked_conv ?_ $$ HT
      exact (dcase_small_text _ _ _ hdep0 hsm').symm
  -- the minimum is paid: `internal_register_account`
  rw [if_pos hsm]
  mstep
  mstep_not_taken with (first | rfl | decide | simp [Numeric.bool])
  have hsm' : ¬ depOf h < minOf xb := by simp only [depOf]; omega
  rw [if_neg hsm']
  have ha409 := hm.funcs 409 (by decide)
  have hK401' : cost401 cfg (F + 2) pl (UInt32.ofNat h.context.predecessorAccountId.length) h2
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) = K401 := by
    rw [← hK401]
    simp only [cost401, NewBody.storageWriteUse_congr (NewBody.sameCost_of_keep hk2) (by rw [hs2])]
  icases stkSp (80 + SP - 304) 304 (by omega) $$ Lo with ⟨Lo, L304⟩
  mstep; mstep; mstep; mstep
  mcall (InternalDeposit.f409_ok cfg lim (d + 1) types[14]! rfl inst mi e A n g ta mx hm (by omega) Cg gt (s - 144)
      self pp pc pl (s - 144 + 56) p (UInt32.ofNat h.context.predecessorAccountId.length)
      (UInt32.ofNat h.context.predecessorAccountId.length) aidx maxP hl2
      ((p.toNat, h.context.predecessorAccountId.length) :: live) (F + 2) (by unfold okG at hF ⊢; omega) pre
      h.context.predecessorAccountId (by omega) (by omega) (by omega) hpre hLn.symm (by omega) hpl hl0 hpp
      (by omega) (by omega) (MeasureUsage.heapRoom_shift hroom hlen12 (by omega)) h2 s2 (by rw [hv2]; exact hview)
      hacc2 (by rw [hc2]; exact hlim) (by rw [hc2]; exact hvlim) hcan2.1 hcan2.2 (hlink2 _) hp2
      (by rw [hid2, hs2, hnone]; simp only [writeProofCost, Option.map_none, Option.getD_none]; omega)
      (by rw [hs2]; exact hnone)) using [Hg L304 HI HWs Hvt Hinv HP HPre V Hab HZ Hh]
      with (rw [hK401']; mstep_norm_full; omega)
  · iunfold InternalDeposit.pre409
    ihave L304 := stkA (b := (s - 144).toNat - 304) (by omega) $$ L304
    iframe Hg L304 HI HWs Hvt Hinv HP HPre V Hab HZ Hh
    ipureintro; rfl
  iunfold InternalDeposit.post409 at HQ
  icases HQ with ⟨%hrs, Hg, L304, HI, HWs, Hvt, ⟨%hl3, %hlen3, Hinv⟩, HP, HPre, V, Hab, HZ, ⟨%h3, %hq3, Hh⟩⟩
  subst hrs
  -- the host after 409
  obtain ⟨s3, hacc3, hcan3, hlink3, hp3, he3⟩ := StorageWritePost.next hq3 hcan2 hlink2 hp2
    (by rw [hid2, hs2, hnone]; simp only [writeProofCost, Option.map_none, Option.getD_none]; omega)
  have hk3 : keep h3 = keep h := by rw [keep_of_erase he3, keep_storageWriteHost, hk2]
  have hs3 : ∀ k, h3.storage k = if k = (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
      h.context.predecessorAccountId)) then some zeros else h.storage k := by
    intro k
    rw [erase_field he3 NearState.storage fun _ => rfl, storageWriteHost_storage, hs2]
  have hc3 : h3.config = h.config := congrArg NewBody.Keep.config hk3
  have hid3 : h3.context.currentAccountId = h.context.currentAccountId :=
    (congrArg NewBody.Keep.id hk3)
  have hv3 : h3.context.isView = h.context.isView := congrArg NewBody.Keep.isView hk3
  have hx3' : h3.extCosts = h.extCosts := congrArg NewBody.Keep.extCosts hk3
  have hlen123 : LenIn hl 6 hl3 := MeasureUsage.lenIn_trans hlen12 hlen3
  -- 418 again
  ihave Hb := boundsBytes_join n _ _ $$ [B0 B8 Brest]
  · ihave B0 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ B0
    ihave B8 := memBytes_addr (b := (s - 144 + 72).toNat + 8) (by omega) $$ B8
    iframe B0 B8 Brest
  icases stkSp 224 80 (by omega) $$ L304 with ⟨L224, L80⟩
  mstep; mstep; mstep; mstep
  mcall (StorageBalanceBounds.f418_spec cfg lim (d + 1) types[14]! rfl inst mi n g (A 553) (A 954) (A 566) hn hg
      (hm.funcs 553 (by decide)) (hm.funcs 954 (by decide)) (hm.funcs 566 (by decide)) (by omega) Cg gt (s - 144)
      (s - 144 + 72) self (by omega) (by omega) (boundsBytes ((xOf xb).toNat * 10000000000000000000)) xb (by simp) hxb)
      using [Hg L80 Hb HX]
      with (simp only [StorageBalanceBounds.cost418]; mstep_norm_full; omega)
  · iunfold StorageBalanceBounds.pre418
    ihave L80 := stkA (b := (s - 144).toNat - 80) (by omega) $$ L80
    iframe Hg L80 Hb HX
    ipureintro; rfl
  iunfold StorageBalanceBounds.post418 at HQ
  icases HQ with ⟨%hrs, Hg, L80, Hb, HX⟩
  subst hrs
  icases boundsBytes_split n _ _ $$ Hb with ⟨B0, B8, Brest⟩
  ihave B0 := memBytes_addr (b := (s - 144).toNat + 72) (by omega) $$ B0
  ihave B8 := memBytes_addr (b := (s - 144 + 72 + 8).toNat + 0) (by omega) $$ B8
  -- the amount: deposit - minimum
  ihave U8 := memBytes_addr (b := (s - 144 + 40 + 8).toNat + 0) (by omega) $$ U8
  mstep; mstep [U0] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep [B0] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep [U8] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep [B8] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  have hle : (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000)).toNat + 2 ^ 64 *
      (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000 / 18446744073709551616)).toNat ≤
      (depLo h).toNat + 2 ^ 64 * (depHi h).toNat := by
    have := hmw; simp only [mloOf, mhiOf, minOf] at this hsm; omega
  iapply mwpi_cons
  iapply FmtGrow.mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega, trivial⟩
  inext
  iintro Hc
  mctrl_norm
  rw [← apply_ite Value.i32, Cmp128.sub128_flag (depLo h) (depHi h)
    (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000))
    (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000 / 18446744073709551616)) hle]
  mstep_not_taken with (first | rfl | decide)
  -- the amount at sp + 40
  ihave U8 := memBytes_addr (b := (s - 144).toNat + 48) (by omega) $$ U8
  mstep; mstep; mstep [U0] with simp
  mstep; mstep; mstep [U8] with simp
  -- the segment
  have hb3 : bud - lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) -
      writeProofCost (contractKey h2.context.currentAccountId
        (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)))
        (h2.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) =
      bud - lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) -
      writeProofCost (contractKey h.context.currentAccountId
        (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) none := by
    rw [hid2, hs2, hnone]
  rw [hb3] at hp3
  have hsome3 : h3.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
      h.context.predecessorAccountId)) = some (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) := by
    rw [hs3, if_pos rfl, zeros_eq]
  have hKS' : costSegAll cfg (F + 5) pl (UInt32.ofNat h.context.predecessorAccountId.length) h3
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) 0 0 t0 t1
      (aloOf h xb) (ahiOf h xb) h.context.predecessorAccountId K879 = KS := by
    rw [← hKS]
    exact DepositCosts.costSegAll_congr cfg _ pl _ (hk3.trans (keep_withVal h _ _).symm)
      (by rw [hs3, if_pos rfl]; simp [withVal]) _ _ _ _ _ _ _ _
  have hlenU : LenUp hl 6 hl3 := DepositSeg.lenUp_of_lenIn hlen123 hroom.2.1
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L224
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L80
  ihave Lo := stkA2 (b := (s - 144).toNat - 80 - SP) (k' := 80 + SP) (by omega) (by omega) $$ Lo
  ihave F0 := stkA (b := (s - 144).toNat) (by omega) $$ F0
  ihave O0 := stk_u64 (GF := GF) n _ _ $$ O0
  ihave O8 := stk_u64 (GF := GF) n _ _ $$ O8
  ihave H24 := stkJ (a := (s - 144).toNat + 24) (b := (s - 144 + 32).toNat + 0) (k1 := 8) (k2 := 8) (k := 16)
    (by omega) rfl $$ [O0 O8]
  · iframe O0 O8
  ihave Hu := joinB (a := (s - 144 + 40).toNat) (b := (s - 144).toNat + 48) (storeBytes (.i64 (aloOf h xb)) 8) _
    (by simp; omega) $$ [U0 U8]
  · iframe U8
    iapply memBytes_addr (by omega) $$ U0
  ihave Hu : n ↦[wms][ (s - 144 + 40).toNat ] u128Bytes (aloOf h xb) (ahiOf h xb) $$ [Hu]
  · simp only [u128Bytes]; iexact Hu
  icases splitB (a := (s - 144 + 72).toNat + 16) (b := (s - 144 + 72).toNat + 16 + 8) (storeBytes (.i64 1) 8) _
    (by simp) $$ Brest with ⟨Br8, Br16⟩
  ihave B0 := stk_u64 (GF := GF) n _ _ $$ B0
  ihave B8 := stk_u64 (GF := GF) n _ _ $$ B8
  ihave Br8 := stk_u64 (GF := GF) n _ _ $$ Br8
  ihave F72 := stkJ2 ((s - 144).toNat + 72) (by omega) (by omega) $$ B0 B8
  ihave F72 := stkJ2 ((s - 144).toNat + 72) (by omega) (by omega) $$ F72 Br8
  ihave F96 := stkB (b := (s - 144).toNat + 96) (k := 16) _ (by omega) (by simp) $$ Br16
  ihave F68 := stkA (b := (s - 144).toNat + 68) (by omega) $$ F68
  ihave F112 := stkA (b := (s - 144).toNat + 112) (by omega) $$ F112
  ihave F124 := stkA (b := (s - 144).toNat + 124) (by omega) $$ F124
  ihave F128 := stkA (b := (s - 144).toNat + 128) (by omega) $$ F128
  have hw := Cmp128.sub128_words (depLo h) (depHi h)
    (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000))
    (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000 / 18446744073709551616)) hle
  have hw' : (depLo h - UInt64.ofNat ((xOf xb).toNat * 10000000000000000000)).toNat + 2 ^ 64 *
      (depHi h - UInt64.ofNat ((xOf xb).toNat * 10000000000000000000 / 18446744073709551616) -
        (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (depLo h)
          (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000)))).toUInt64).toNat = depOf h - minOf xb := by
    rw [hw]; have := hmw; simp only [mloOf, mhiOf, minOf] at this; simp only [depOf, minOf]; omega
  have z0 : UInt64.toNat 0 = 0 := rfl
  iapply mwpi_code_eq (code' := seg406 ++ tail232) ?_
  · rfl
  iapply seg406_all cfg lim d e inst mi A n g ta mx hm D (by omega) Cg (cfg.regularOpCost + R) gt (s - 144) self
    _ _ _ _ _ SP hSP (by omega) (by omega) (by omega) (by omega) pp pc pl t0 t1 0 0 aidx maxP hl3
    ((p.toNat, h.context.predecessorAccountId.length) :: live) (F + 5) (by unfold okG at hF ⊢; omega) pre p
    h.context.predecessorAccountId hpre hab hab0 hpl hl0 hpp hpb
    List.mem_cons_self (DepositSeg.heapRoom_up hroom hlenU (by omega)) h3 s3
    (by rw [hv3]; exact hview) hacc3 hcan3 hlink3 hp3
    (by rw [hid3, hsome3]; simp [readProofCost, writeProofCost]; omega)
    (by rw [hc3]; exact hlim) (by rw [hc3]; exact hvlim) (by rw [hc3]; exact hreg) hsome3
    (fun _ _ => DepositSeg.LogOk.of_keep hk3 (hlog _ _))
    (InternalDepositOverflow.LogFits.of_keep hk3 hfit16) (by rw [hx3']; exact hov16)
    (InternalDepositOverflow.LogFits.of_keep hk3 hfitS) (by rw [hx3']; exact hovS) C lpc Dp K879 H879 _
  rw [hKS']
  iframe Hseg HC Hg Lo F0 H24 Hu V Hab F68 F72 F96 F112 F124 F128 HSt Hvt Hinv HI H12 HWs HLs HPS HH HDp HM Ht0 Ht8
    HP HPre Hh
  isplitl [Hc]
  · iapply credits_mono (by omega) $$ Hc
  isplitl [Wok HX HDs HPs HHs HZ HU8]
  · iintro %l2' %hl' %F' %h' %⟨hF', hup, hpost, hok1, hok2⟩ Hc Hg Lo HSt Hvt Hinv HI H12 HWs HLs HPS HH HDp HM HT HP HPre Hh
    ihave Lo := stkA2 (b := s.toNat - (224 + SP)) (k' := 224 + SP) (by omega) (by omega) $$ Lo
    rw [show s - 144 + 144 = s by simp, List.erase_cons_head]
    ihave HS : selfCells n self (StorageBalanceBounds.u128Of (t0.toNat + 2 ^ 64 * t1.toNat +
        ((aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat))) xb pp pc pl pre $$ [HT HX HP HPre]
    · iunfold selfCells; iframe HT HX HP HPre
    ihave HB : stat232 n ta A lpc Dp aidx $$ [HI H12 HDs HPs HHs HWs HLs HPS HH HDp HM HZ HSt HU8 Hvt]
    · iunfold stat232; iframe HI H12 HDs HPs HHs HWs HLs HPS HH HDp HM HZ HSt HU8 Hvt
    have hpost' := hpost
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at hpost'
    simp only [Post.mblock, Post.mseq, List.nil_append]
    iapply Wok $$ %hl' %F' %(LogStr.logged h' (logText (aloOf h xb) (ahiOf h xb) h.context.predecessorAccountId))
      %⟨#[.i32 self, .i32 (s - 144), .i64 l2', .i64 (aloOf h xb), .i32 (s - 144 + 72 + 8),
        .i64 (UInt64.ofNat ((xOf xb).toNat * 10000000000000000000)), .i64 (depHi h)], inst, mi⟩
      %⟨by omega, (hlenU.trans hup).mono (by omega),
        ⟨h2, s2, h3, s3, h', hq2, hacc2, hcan2, hlink2, hp2, he2, hq3, hacc3, hcan3, hlink3, hp3, he3, hpost', rfl⟩,
        dcase_new_ok _ _ _ hdep0 hsm' (by omega) (by omega)⟩
      Hc Hg Lo HS HB Hinv Hh
  · iintro %hX %⟨hkX, hno⟩ HTr
    simp only [Post.mblock, Post.mseq_trap]
    have hno' : ¬ (0 + (depOf h - minOf xb) < 2 ^ 128 ∧ t0.toNat + 2 ^ 64 * t1.toNat + (depOf h - minOf xb) < 2 ^ 128) :=
      fun ⟨a, b⟩ => hno ⟨by omega, by omega⟩
    iapply Wtr $$ %hX %⟨hkX.trans hk3, dcase_new_nok _ _ _ hdep0 hsm' hno'⟩
    iapply panicked_conv ?_ $$ HTr
    refine Eq.trans ?_ (dcase_new_text (depOf h) (minOf xb) (t0.toNat + 2 ^ 64 * t1.toNat) hdep0 hsm' hno').symm
    simp only [z0, Nat.mul_zero, Nat.zero_add, hw']

end Body

end WNear.Binary.DepositBody
