import Bridge.Functions.DepositTail
import Bridge.Functions.InternalDeposit
import Bridge.Functions.NewHost

/-!
# `near_deposit` (232) from the call of `internal_deposit` to the end (M8)

Both paths of 232 (the account registered, or registered just now) meet at

```
406(self, sp + 56, l3, l2)            internal_deposit(&account, amount)
… tail232                             the log, the drops, sp += 144, return
```

`seg406` is that call; `seg406_ok` composes `InternalDeposit.f406_ok` and `DepositTail.tail232_spec`
with any postcondition (the segment ends in `return`), so it serves under the blocks of 232.

* `LenUp`: a heap length after at most `k` one-page grows (an upper bound, aligned, positive);
  `heapRoom_up`: the room left.
* `Post406.keep`, `LogOk.of_keep`, `costTail_congr`, `cost401s_congr`: what the storage calls of
  406 keep of the host, for the log and the costs.
-/

namespace WNear.Binary.DepositSeg

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod iface)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA join64' split64' stkW stkB)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StorageWrite (wslot evictedRegister)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.InternalDeposit (code406 pre406 post406 Post406 cost405)
open WNear.Binary.LookupMapInsertSome (cost401s)
open WNear.Binary.DepositTail (tailCode tailStat costTail tail232 tail232_spec logText)
open WNear.Binary.DepositLog (logW)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtStrPad (strW)
open WNear.Binary.NewBody (Keep keep keep_of_erase keep_acc keep_storageReadRegs keep_storageWriteHost SameCost
  sameCost_of_keep chargesUse_congr storageWriteUse_congr)

/-! ## Heap lengths -/

/-- A heap length `b` after at most `k` one-page grows from `a`. -/
def LenUp (a k b : Nat) : Prop := b ≤ a + k * 65536 ∧ b % 65536 = 0 ∧ 0 < b

theorem lenUp_of_lenIn {a k b : Nat} (h : LenIn a k b) (ha : 0 < a) : LenUp a k b :=
  ⟨h.2.1, h.2.2, Nat.lt_of_lt_of_le ha h.1⟩

theorem LenUp.trans {a b c j k : Nat} (h1 : LenUp a j b) (h2 : LenUp b k c) : LenUp a (j + k) c := by
  obtain ⟨a1, -, -⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  refine ⟨?_, b2, b3⟩
  rw [Nat.add_mul]; omega

theorem LenUp.mono {a j k b : Nat} (h : LenUp a j b) (hjk : j ≤ k) : LenUp a k b :=
  ⟨Nat.le_trans h.1 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hjk) _), h.2.1, h.2.2⟩

theorem lenUp_refl {a : Nat} (h0 : a % 65536 = 0) (hp : 0 < a) : LenUp a 0 a := ⟨by simp, h0, hp⟩

theorem heapRoom_up {k k' j a b maxP : Nat} (hr : HeapRoomK k a maxP) (hl : LenUp a j b) (hj : j + k' ≤ k) :
    HeapRoomK k' b maxP := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  obtain ⟨l1, l2, l3⟩ := hl
  have m1 : (j + k') * 65536 ≤ k * 65536 := Nat.mul_le_mul_right _ hj
  have m2 : (j + (k' + 1)) * 65536 ≤ (k + 1) * 65536 := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at m1 m2
  exact ⟨l2, l3, by omega, by omega⟩

/-! ## What 406 keeps of the host -/

theorem Post406.keep {e : Nat} {h h2 : NearState} {k nv : List UInt8} {st : Near.TrieOverlay.State} {bud : Nat}
    (hp : Post406 e h k nv st bud h2) : keep h2 = keep h := by
  obtain ⟨h1, s1, -, -, -, -, -, he1, ⟨s1', -, -, he2⟩⟩ := hp
  rw [keep_of_erase he2, keep_storageWriteHost, keep_of_erase he1, keep_storageReadRegs, keep_acc]

theorem LogOk.of_keep {h h' : NearState} {bs : List UInt8} {k : Nat} (hk : keep h' = keep h)
    (hok : LogStr.LogOk h bs k) : LogStr.LogOk h' bs k := by
  have hc : h'.config = h.config := congrArg Keep.config hk
  have hl : h'.logs = h.logs := congrArg Keep.logs hk
  have hx : h'.extCosts = h.extCosts := congrArg Keep.extCosts hk
  obtain ⟨a, b, c, d, f, g⟩ := hok
  refine ⟨a, b, c, ?_, ?_, ?_⟩
  · intro limit hlim; rw [hl]; exact d limit (by rw [← hc]; exact hlim)
  · intro limit hlim; rw [hl]; exact f limit (by rw [← hc]; exact hlim)
  · rw [hx]; exact g

theorem logUtf8Use_congr {x y : NearState} (h : SameCost x y) (k : Nat) : logUtf8Use x k = logUtf8Use y k :=
  chargesUse_congr h _

theorem costTail_congr (cfg : WasmConfig) (F : Nat) (lo hi : UInt64) (ab : List UInt8) {x y : NearState}
    (h : SameCost x y) : costTail cfg F lo hi ab x = costTail cfg F lo hi ab y := by
  simp only [costTail, logUtf8Use_congr h]

theorem cost401s_congr (cfg : WasmConfig) (F : Nat) (pl L : UInt32) {x y : NearState} (h : SameCost x y)
    {k : List UInt8} (hk : x.storage k = y.storage k) (b : List UInt8) :
    cost401s cfg F pl L x k b = cost401s cfg F pl L y k b := by
  have hc := chargesUse_congr (h.setRegister evictedRegister.toNat b)
  have hr : ∀ z : NearState, (z.setRegister evictedRegister.toNat b).registers evictedRegister.toNat = some b := by
    intro z; simp [NearState.setRegister]
  simp only [cost401s, storageWriteUse_congr h hk, ReadRegisterF.cost523F, registerLenUse, hc, hr,
    ReadRegisterF.costRestF, readRegisterUse]

/-! ## The segment -/

/-- 232's call of `internal_deposit(self, &account, amount)`. -/
def seg406 : List Instr :=
  [.local_get 0, .local_get 1, .i32_const 56, .i32_binop .add, .local_get 3, .local_get 2, .call 406]

/-- `seg406 ++ tail232` is 232's code after the inner block (the paths meet there). -/
theorem seg406_eq : (match f232.body.drop 21 with
    | .block _ b :: _ => (match b with
      | .block _ b2 :: _ => (match b2.drop 10 with
        | .block _ b3 :: _ => b3.drop 1
        | _ => [])
      | _ => [])
    | _ => []) = seg406 ++ tail232 := rfl

/-- The cost of the segment, the callees' activations included: 406 on the host `h` it starts
from, and the tail on the same costs. -/
noncomputable def costSeg (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k old : List UInt8)
    (lo hi : UInt64) (ab : List UInt8) : Nat :=
  20 * cfg.regularOpCost +
    (activationGas cfg.regularOpCost (entryLocals f406 [.i32 0, .i32 0, .i64 0, .i64 0]) +
      (300 * cfg.regularOpCost + cost405 cfg F pl L h k old + cost401s cfg (F + 3) pl L h k old)) +
    costTail cfg (F + 7) lo hi ab h

theorem activation406 (c : Nat) (a b : UInt32) (x y : UInt64) :
    activationGas c (entryLocals f406 [.i32 a, .i32 b, .i64 x, .i64 y]) =
      activationGas c (entryLocals f406 [.i32 0, .i32 0, .i64 0, .i64 0]) := by
  simp [activationGas, entryLocals, f406, ValType.default]

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem stk_u128 (n a : Nat) (lo hi : UInt64) : n ↦[wms][ a ] u128Bytes lo hi ⊢ stk (GF := GF) n a 16 :=
  stkB _ rfl (by simp [u128Bytes, storeBytes])

theorem stk_strW (n : Nat) (sv : UInt32) (p c l : UInt32) :
    strW (GF := GF) n sv p c l ⊢ stk n sv.toNat 12 := by
  iintro H
  iunfold strW at H
  icases H with ⟨W0, W4, W8⟩
  ihave W0 := stkW (b := sv.toNat) _ rfl $$ W0
  ihave W4 := stkW (b := sv.toNat + 4) _ rfl $$ W4
  ihave W8 := stkW (b := sv.toNat + 8) _ rfl $$ W8
  ihave X := stkJ (a := sv.toNat + 4) (b := sv.toNat + 4 + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [W4 W8]
  · iframe W4 W8
  iapply stkJ (a := sv.toNat) (b := sv.toNat + 4) (k1 := 4) (k2 := 8) (k := 12) rfl rfl
  iframe W0 X

theorem strW_of (n : Nat) (sv p l : UInt32) :
    n ↦[wms][ sv.toNat ] (bytes32 p ++ (bytes32 l ++ bytes32 l)) ⊢ strW (GF := GF) n sv p l l := by
  iintro H
  icases splitB (a := sv.toNat) (b := sv.toNat + 4) (bytes32 p) _ (by simp [bytes32]) $$ H with ⟨W0, H⟩
  icases split64' (a := sv.toNat + 4) (b := sv.toNat + 4 + 4) _ _ rfl $$ H with ⟨W4, W8⟩
  iunfold strW
  iframe W0 W4 W8

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **232 from the call of `internal_deposit` to its `return`**, no overflow: the balance
`B + a` and the supply `T + a` (`f406_ok`), then the log, the drops and the epilogue
(`tail232_spec`). The account's `String` `(ap, |ab|, |ab|)` at `sp + 56`, the amount
`(l3, l2)` at `sp + 40`. -/
theorem seg406_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 26 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp self : UInt32) (l2 l3 l5 l6 : UInt64) (l4 : UInt32)
    (hs : 480 ≤ sp.toNat) (hs2 : sp.toNat + 144 ≤ 2 ^ 32 - 16) (hal : sp.toNat % 8 = 0)
    (hthis : self.toNat + 36 ≤ 2 ^ 32) (pp pc pl : UInt32) (t0 t1 x0 x1 : UInt64) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre : List UInt8)
    (ap : UInt32) (ab : List UInt8)
    (hpre : pre.length = pl.toNat) (hab : ab.length ≤ 64) (hab0 : 0 < ab.length)
    (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
    (hap : ap.toNat + ab.length ≤ 2 ^ 32) (hlive : (ap.toNat, ab.length) ∈ live)
    (hroom : HeapRoomK 10 hl maxP)
    (hno1 : x0.toNat + 2 ^ 64 * x1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat) < 2 ^ 128)
    (hno2 : t0.toNat + 2 ^ 64 * t1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat) < 2 ^ 128)
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
    (hok : LogStr.LogOk h (logText l3 l2 ab) (logText l3 l2 ab).length)
    (Φ : Post NearState GF) :
    code406 e n maxP inst mi A mx ∗ tailCode e n maxP inst mi A mx ∗
      A 406 ↪[wf] FuncInst.wasm types[38]! inst f406 ∗
      credits Cg (costSeg cfg F pl (UInt32.ofNat ab.length) h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))
        (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) l3 l2 ab + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 480) 480 ∗ stk n sp.toNat 24 ∗
      n ↦[wms][ (sp + 40).toNat ] u128Bytes l3 l2 ∗
      n ↦[wms][ (sp + 56).toNat ] (bytes32 ap ++ (bytes32 (UInt32.ofNat ab.length) ++ bytes32 (UInt32.ofNat ab.length))) ∗
      n ↦[wms][ ap.toNat ] ab ∗
      stk n (sp.toNat + 72) 24 ∗ stk n (sp.toNat + 112) 12 ∗ stk n (sp.toNat + 128) 16 ∗
      tailStat n ta A ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
      iface n ta A ∗ Interface.slot n ta 12 38 (A 240) ∗ wslot n ta A ∗ LogStr.lslot n ta A ∗
      n ↦[wms][ self.toNat ] storeBytes (.i64 t0) 8 ∗ n ↦[wms][ self.toNat + 8 ] storeBytes (.i64 t1) 8 ∗
      prefixAt n (self + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ mhostPt h ∗
      (∀ (l2' : UInt64) (hl' F' : Nat) (h' : NearState),
        ⌜F' ≤ F + 11 ∧ LenUp hl 10 hl' ∧
          Post406 e h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))
            (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat))) st bud h'⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ stk n (sp.toNat - 480) 480 -∗ stk n sp.toNat 24 -∗
        stk n (sp.toNat + 40) 16 -∗ stk n (sp.toNat + 56) 12 -∗
        stk n (sp.toNat + 72) 24 -∗ stk n (sp.toNat + 112) 12 -∗ stk n (sp.toNat + 128) 16 -∗
        tailStat n ta A -∗ vt n 1057464 aidx ta (A 578) -∗
        heapInv n maxP hl' (live.erase (ap.toNat, ab.length)) F' -∗
        iface n ta A -∗ Interface.slot n ta 12 38 (A 240) -∗ wslot n ta A -∗ LogStr.lslot n ta A -∗
        n ↦[wms][ self.toNat ] StorageBalanceBounds.u128Of (t0.toNat + 2 ^ 64 * t1.toNat + (l3.toNat + 2 ^ 64 * l2.toNat)) -∗
        prefixAt n (self + 24) pp pc pl -∗ n ↦[wms][ pp.toNat ] pre -∗
        mhostPt (LogStr.logged h' (logText l3 l2 ab)) -∗
        Φ.ret [] ⟨#[.i32 self, .i32 sp, .i64 l2', .i64 l3, .i32 l4, .i64 l5, .i64 l6], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 self, .i32 sp, .i64 l2, .i64 l3, .i32 l4, .i64 l5, .i64 l6], inst, mi⟩ []
          (seg406 ++ tail232) Φ := by
  iintro ⟨#H406c, #Htc, #F406, Hc, Hg, Hlo, Hs24, Hu, HV, Hab, Har, Hout, Harg, HSt, Hvt, Hinv, HI, H12, HW, HL,
    Ht0, Ht8, Hp, Hpre, Hh, W⟩
  have hn := hm.mem
  have ha406 := hm.funcs 406 (by decide)
  have t38 : types[38]!.params.length = 4 := by rfl
  have hlt := sp.toNat_lt
  have e56 : (sp + 56).toNat = sp.toNat + 56 := by rw [UInt32.toNat_add]; simp; omega
  have e40 : (sp + 40).toNat = sp.toNat + 40 := by rw [UInt32.toNat_add]; simp; omega
  have hal' : (UInt32.ofNat ab.length).toNat = ab.length := by simp; omega
  have hhl : 0 < hl := hroom.2.1
  have S406 := InternalDeposit.f406_ok (GF := GF) cfg lim (d + 1) types[38]! rfl inst mi e A n g ta mx hm
    (by omega) Cg gt sp self pp pc pl (sp + 56) ap (UInt32.ofNat ab.length) (UInt32.ofNat ab.length)
    l3 l2 t0 t1 x0 x1 aidx maxP hl live F hF pre ab hs hal hthis hpre hal'.symm (by omega) hpl hl0 hpp
    (by omega) (by omega) (WNear.Binary.InternalDeposit.heapRoom_mono hroom (by omega)) hno1 hno2 h st
    hview hacc hcanon hlink hproof hbud hlim hvlim hreg hsome
    (cost401s cfg (F + 3) pl (UInt32.ofNat ab.length) h (pre ++ (bytes32 (UInt32.ofNat ab.length) ++ ab))
      (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8))
    (fun h1 s1 he1 => by
      refine le_of_eq (cost401s_congr cfg (F + 3) pl _ (sameCost_of_keep ?_) ?_ _)
      · rw [keep_of_erase he1, keep_storageReadRegs, keep_acc]
      · rw [erase_field he1 NearState.storage fun _ => rfl, storageReadRegs_field NearState.storage (fun _ _ _ => rfl)])
  ihave #H406 := S406 $$ H406c
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold tailCode, Interface.ifaceCode at Htc
    icases Htc with ⟨-, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  icases stkSp 208 272 rfl $$ Hlo with ⟨Lo208, Lo272⟩
  ihave HIR : ifaceR n ta A $$ [HI H12]
  · iunfold ifaceR; iframe HI H12
  ihave Lo := stkJ (a := sp.toNat - 480) (b := sp.toNat - 480 + 208) (k1 := 208) (k2 := 272) (k := 480) rfl rfl
    $$ [Lo208 Lo272]
  · iframe Lo208 Lo272
  iunfold costSeg at Hc
  simp only [seg406, List.cons_append, List.nil_append]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall H406 using [Hg Lo HIR HW Hvt Hinv Ht0 Ht8 Hp Hpre HV Hab Hh]
    with (rw [activation406]; mstep_norm_full; omega)
  · iunfold pre406
    iframe Hg Lo HIR HW Hvt Hinv Ht0 Ht8 Hp Hpre HV Hab Hh
    ipureintro; rfl
  iunfold post406 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HIR, HW, Hvt, ⟨%l1, %hl1, Hinv⟩, HT, Hp, Hpre, HV, Hab, ⟨%h', %hq', Hh⟩⟩
  subst hrs
  icases ReadRegister.iface_of_ifaceR n ta A $$ HIR with ⟨HI, H12⟩
  have hk' := Post406.keep hq'
  have hok' := LogOk.of_keep hk' hok
  have hct : costTail cfg (F + 7) l3 l2 ab h = costTail cfg (F + 7) l3 l2 ab h' :=
    costTail_congr cfg (F + 7) l3 l2 ab (sameCost_of_keep hk'.symm)
  have hroom1 : HeapRoomK 3 l1 maxP := heapRoom_up hroom (lenUp_of_lenIn hl1 hhl) (by omega)
  obtain ⟨r1, r2, r3, r4⟩ := hroom1
  icases stkSp 208 272 rfl $$ Lo with ⟨Lo208, Lo272⟩
  ihave Lo272 := stkA (b := sp.toNat - 272) (by omega) $$ Lo272
  ihave HV := strW_of n (sp + 56) ap (UInt32.ofNat ab.length) $$ HV
  iapply tail232_spec cfg lim d e inst mi A n g ta mx hm (by omega) Cg R gt sp self l2 l3 l5 l6 l4 (by omega)
    hs2 hal maxP l1 live (F + 7) aidx (by omega) (by omega)
    (LookupMapOps.roomFor_ofK (k := 3) _ (by decide) ⟨r1, r2, r3, r4⟩ (LookupMapOps.lenIn_zero l1 r1) (by omega))
    (by unfold okG at hF ⊢; omega) l3 l2 ap ab hab hab0 hap hlive h' hok' Φ
  mcredits (costTail cfg (F + 7) l3 l2 ab h' + R)
  iframe Htc Hc Hg Lo272 Hs24 Hu HV Hab Har Hout Harg HSt Hvt Hinv HI HL Hh
  iintro %l2' %hl' %F' %hfin Hc Hg Lo272 Hs24 Hu HV Har Hout Harg HSt Hvt Hinv HI HL Hh
  ihave Lo := stkJ (a := sp.toNat - 480) (b := sp.toNat - 480 + 208) (k1 := 208) (k2 := 272) (k := 480) rfl rfl
    $$ [Lo208 Lo272]
  · iframe Lo208
    iapply stkA (by omega) $$ Lo272
  ihave Hu := stk_u128 n _ l3 l2 $$ Hu
  ihave HV := stk_strW n (sp + 56) _ _ _ $$ HV
  ihave Hu := stkA (b := sp.toNat + 40) (by omega) $$ Hu
  ihave HV := stkA (b := sp.toNat + 56) (by omega) $$ HV
  have hup : LenUp hl 10 hl' := by
    have a := lenUp_of_lenIn hl1 hhl
    obtain ⟨f1, f2, f3, f4⟩ := hfin
    exact (LenUp.trans a ⟨f2, f3, f4⟩).mono (by omega)
  iapply W $$ %l2' %hl' %F' %h' %⟨by omega, hup, hq'⟩ Hc Hg Lo Hs24 Hu HV Har Hout Harg HSt Hvt Hinv HI H12 HW HL HT
    Hp Hpre Hh

end Spec

end WNear.Binary.DepositSeg
