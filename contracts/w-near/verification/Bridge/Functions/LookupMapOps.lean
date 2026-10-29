import Bridge.Functions.LookupMapRemove
import Bridge.Functions.BorshU128From

/-!
# `LookupMap<String, u128>::insert` (401) and `::remove` (402)

```wat
;; 401 insert(out, map, k, v): sp -= 112
;;     395(sp + 64, k); 779(sp + 40, sp + 64)      ;; the Borsh key, (ptr, len)
;;     397(sp + 80, v); 779(sp + 32, sp + 80)      ;; the Borsh value, (ptr, len)
;;     391(sp + 48, map, kp, kl, vp, vl)           ;; insert_raw: None (not Some: not on our path)
;;     321(sp + 80); 321(sp + 64)                  ;; both freed
;;     out+16 := 0; out+8 := 0; out := 0 (None)   ;; i64 words
;;     sp += 112
;; 402 remove(out, map, k): sp -= 80
;;     395(sp + 48, k); 779(sp + 24, sp + 48)      ;; the Borsh key, (ptr, len)
;;     393(sp + 32, map, kp, kl)                   ;; remove_raw: Some(vec)
;;     [sp+64..76] := vec; 779(sp + 16, sp + 64); 398(sp, ptr, len)   ;; the u128
;;     321(sp + 64); 321(sp + 48)                  ;; both freed
;;     out+16 := hi; out+8 := lo; out := 1 (Some) ;; i64 words
;;     sp += 80
```

* `f401_none`: `insert(k, v)` on a key absent from storage: the host as `StorageWritePost` of
  `storage_write(pre ++ borsh(k), borsh(v))`, `None` at `out`, the heap with three more free cells.
-/

namespace WNear.Binary.LookupMapOps

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages cellPages_toNat cellBytes_toNat)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.VecWithCap (vecCode2 costAllocF okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.StorageWrite (wslot wCode pre547 post547 evictedRegister)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (code392 prefixAt pre392 post392 cost510)
open WNear.Binary.LookupMapInsert (code391 pre391 post391)
open WNear.Binary.LookupMapBorsh (code395 pre395 post395 cost395 code397 pre397 post397 cost397 code398 pre398
  post398)
open WNear.Binary.StateWrite (stkJ stkL memBytes_disjoint)

/-! ## Room on the heap for `k` grows -/

/-- Room for `k` grows of one page each, under the limit `maxP` and `2^32`. -/
def HeapRoomK (k len maxP : Nat) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + k * 65536 ≤ maxP * 65536 ∧ len + (k + 1) * 65536 ≤ 2 ^ 32

/-- A memory length after at most `k` one-page grows from `len`. -/
def LenIn (len k L : Nat) : Prop := len ≤ L ∧ L ≤ len + k * 65536 ∧ L % 65536 = 0

theorem cellPages_le4096 (size : UInt32) (h : size.toNat ≤ 4096) : (cellPages (wordsOf size) 1).toNat = 1 := by
  have hw : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  rw [cellPages_toNat _ _ (by omega) (by decide), cellBytes_toNat _ _ (by omega) (by decide), hw]
  simp only [UInt32.reduceToNat]
  omega

theorem grownLen_le4096 (L : Nat) (size : UInt32) (h : size.toNat ≤ 4096) : grownLen L size = L + 65536 := by
  simp [grownLen, cellPages_le4096 size h]

theorem roomFor_ofK {k len maxP L : Nat} (size : UInt32) (h : size.toNat ≤ 4096) (hr : HeapRoomK k len maxP)
    (hL : LenIn len j L) (hj : j + 1 ≤ k) : roomFor L maxP size := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  obtain ⟨l1, l2, l3⟩ := hL
  have : (j + 1) * 65536 ≤ k * 65536 := Nat.mul_le_mul_right _ hj
  refine ⟨l3, by omega, ?_, ?_⟩ <;> rw [cellPages_le4096 size h] <;> omega

/-- One more grow (or none) of a block of at most 4096 bytes. -/
theorem lenIn_step {len j L L' : Nat} (size : UInt32) (h : size.toNat ≤ 4096) (hL : LenIn len j L)
    (h' : L' = L ∨ L' = grownLen L size) : LenIn len (j + 1) L' := by
  obtain ⟨l1, l2, l3⟩ := hL
  have e : len + (j + 1) * 65536 = (len + j * 65536) + 65536 := by rw [Nat.succ_mul, Nat.add_assoc]
  rcases h' with h1 | h1 <;> subst h1
  · exact ⟨l1, by rw [e]; exact Nat.le_add_right_of_le l2, l3⟩
  · rw [grownLen_le4096 L size h]
    exact ⟨Nat.le_add_right_of_le l1, by rw [e]; exact Nat.add_le_add_right l2 _, by rw [Nat.add_mod_right]; exact l3⟩

theorem lenIn_zero (len : Nat) (h : len % 65536 = 0) : LenIn len 0 len := ⟨le_refl _, by simp, h⟩

theorem lenIn_mono {len j k L : Nat} (hL : LenIn len j L) (h : j ≤ k) : LenIn len k L := by
  obtain ⟨l1, l2, l3⟩ := hL
  exact ⟨l1, Nat.le_trans l2 (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _), l3⟩

/-! ## `insert` (401) on an absent key -/

section S401

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 401 (persistent). -/
def code401 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code391 e n maxP inst mi A mx ∗ code395 n maxP inst mi A ∗ code397 n maxP inst mi A ∗
    A 395 ↪[wf] FuncInst.wasm types[14]! inst f395 ∗ A 397 ↪[wf] FuncInst.wasm types[14]! inst f397 ∗
    A 391 ↪[wf] FuncInst.wasm types[36]! inst f391)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code401 (GF := GF) e n maxP inst mi A mx) := by
  unfold code401; infer_instance

def pre401 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L w : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 v, .i32 w]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 272) 272 ∗ iface n ta A ∗ wslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ w.toNat ] b0 ∗ n ↦[wms][ w.toNat + 8 ] b1 ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

/-- `None` at `out` (24 zero bytes), the heap after at most three grows with three more free cells. -/
def post401 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L w : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 272) 272 ∗ iface n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 3 len'⌝ ∗ heapInv n maxP len' live (F + 3)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ w.toNat ] b0 ∗ n ↦[wms][ w.toNat + 8 ] b1 ∗ n ↦[wms][ out.toNat ] List.replicate 24 0 ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 401, activation excluded. -/
def cost401 (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k : List UInt8) : Nat :=
  1712 * cfg.regularOpCost + cost395 cfg F L + cost397 cfg F + cost510 cfg F pl (0 + 4 + L) +
    storageWriteUse h k (pl + (0 + 4 + L)).toNat 16

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`LookupMap::insert`** (401) of the `u128` `b0 ++ b1` at `w` under the `String` `key` at `v`,
absent from storage: the storage key `pre ++ borsh(key)`, the value `borsh(u128)`; `None` at `out`. -/
theorem f401_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L w : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key b0 b1 ob : List UInt8)
    (hs : 272 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 24) (hout : out.toNat + 24 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hw : w.toNat + 16 ≤ 2 ^ 32) (hroom : HeapRoomK 3 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen (b0 ++ b1).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : writeProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key)))
      (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hnone : h.storage (pre ++ (bytes32 L ++ key)) = none) :
    code401 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f401 Cg
        (pre401 n g ta A gt s out m pp pc pl v p c L w idx maxP len live F pre key b0 b1 ob h)
        (fun _ => cost401 cfg F pl L h (pre ++ (bytes32 L ++ key)))
        (post401 n g ta A gt s out m pp pc pl v p c L w idx maxP len live F pre key b0 b1
          (StorageWritePost e h (pre ++ (bytes32 L ++ key)) (b0 ++ b1) evictedRegister st)) := by
  iintro #Hk
  iunfold code401 at Hk
  icases Hk with ⟨#H391c, #H395c, #H397c, #F395, #F397, #F391⟩
  ihave #Hdrop : dropCode inst mi A $$ []
  · iunfold code391 at H391c; icases H391c with ⟨-, #H, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code391, code392 at H391c; icases H391c with ⟨⟨-, -, #H⟩, -⟩; iexact H
  ihave #F321 : A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 $$ []
  · iunfold code391 at H391c; icases H391c with ⟨-, -, -, -, -, -, -, #H⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha395 := hm.funcs 395 (by decide)
  have ha397 := hm.funcs 397 (by decide)
  have ha391 := hm.funcs 391 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t36 : types[36]!.params.length = 6 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h112 : (s - 112).toNat = s.toNat - 112 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hk4 : (0 + 4 + L).toNat = 4 + L.toNat := by simp [UInt32.toNat_add]; omega
  have hKL : (bytes32 L ++ key).length = (0 + 4 + L).toNat := by simp [bytes32, hkey, hk4]; omega
  unfold cost401
  generalize hK395 : cost395 cfg F L = K395
  generalize hK397 : cost397 cfg F = K397
  generalize hKw : storageWriteUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat 16 = Kw
  generalize hK510 : cost510 cfg F pl (0 + 4 + L) = K510
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre401 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Hm, Hp, Hv, Hkey, B0, B1, Ho, Hhost⟩
  subst hargs
  -- the callees' 160, then the frame
  icases stk_split n (s.toNat - 272) 160 112 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 272 + 160 = s.toNat - 112 by omega]
  icases stk_split n (s.toNat - 112) 32 80 $$ Fr with ⟨U0, Fr⟩
  rw [show s.toNat - 112 + 32 = s.toNat - 80 by omega]
  icases stk_split n (s.toNat - 80) 8 72 $$ Fr with ⟨D2, Fr⟩
  rw [show s.toNat - 80 + 8 = s.toNat - 72 by omega]
  icases stk_split n (s.toNat - 72) 8 64 $$ Fr with ⟨D1, Fr⟩
  rw [show s.toNat - 72 + 8 = s.toNat - 64 by omega]
  icases stk_split n (s.toNat - 64) 4 60 $$ Fr with ⟨O, Fr⟩
  rw [show s.toNat - 64 + 4 = s.toNat - 60 by omega]
  icases stk_split n (s.toNat - 60) 12 48 $$ Fr with ⟨U52, Fr⟩
  rw [show s.toNat - 60 + 12 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 12 36 $$ Fr with ⟨V1, Fr⟩
  rw [show s.toNat - 48 + 12 = s.toNat - 36 by omega]
  icases stk_split n (s.toNat - 36) 4 32 $$ Fr with ⟨U76, Fr⟩
  rw [show s.toNat - 36 + 4 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 12 20 $$ Fr with ⟨V2, U92⟩
  rw [show s.toNat - 32 + 12 = s.toNat - 20 by omega]
  iunfold stk at V1 V2 D1 D2 O
  icases V1 with ⟨%v1b, %hv1b, V1⟩
  icases V2 with ⟨%v2b, %hv2b, V2⟩
  icases D1 with ⟨%d1b, %hd1b, D1⟩
  icases D2 with ⟨%d2b, %hd2b, D2⟩
  icases O with ⟨%obb, %hobb, O⟩
  icases stk_split n (s.toNat - 272) 32 128 $$ Lo with ⟨Lo32, Lo⟩
  rw [show s.toNat - 272 + 32 = s.toNat - 240 by omega]
  simp only [f401]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 395: the Borsh key
  mstep; mstep; mstep; mstep
  mcall (LookupMapBorsh.f395_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 112)
      (s - 112 + 64) v p c L idx maxP len live F hF key v1b (by omega) hkey (by omega) hv1b
      (by simp [UInt32.toNat_add, h112]; omega) hv hp (roomFor_ofK 1024 (by decide) hroom (lenIn_zero len hroom.1) (by omega)))
      using [Hg Lo Hvt Hinv Hv Hkey V1] with (rw [hK395]; mstep_norm_full; omega)
  · iunfold pre395
    ihave Lo := stk_addr (show s.toNat - 240 = (s - 112).toNat - 128 by omega) $$ Lo
    ihave V1 := memBytes_addr (show s.toNat - 48 = (s - 112 + 64).toNat by simp [UInt32.toNat_add, h112]; omega) $$ V1
    iframe Hg Lo Hvt Hinv Hv Hkey V1
    ipureintro; rfl
  rw [hK395]
  iunfold post395 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hv, Hkey, %q1, %rest1, %⟨hq10, hq1b, hrest1⟩, Hgr1, V10, V14, V18, Wk, Rest1⟩
  subst hrs
  -- 779: (q1, 4 + L)
  ihave VV1 := KeyGet.join64 n (s - 112 + 64).toNat q1 1024 $$ [V10 V14]
  · iframe V10 V14
  ihave VV1 := BorshFT.joinB (n := n) (a := (s - 112 + 64).toNat) (b := (s - 112 + 64).toNat + 8)
    (bytes32 q1 ++ bytes32 1024) (bytes32 (0 + 4 + L)) (by simp [bytes32]) $$ [VV1 V18]
  · iframe VV1 V18
  ihave D1 := memBytes_addr (show s.toNat - 72 = (s - 112 + 40).toNat by simp [UInt32.toNat_add, h112]; omega) $$ D1
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 112 + 40) (s - 112 + 64) d1b
      (bytes32 q1 ++ bytes32 1024 ++ bytes32 (0 + 4 + L)) hd1b (by simp [bytes32])) using [D1 VV1]
  · iunfold VecDeref.pre
    iframe D1 VV1
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D1, VV1⟩
  subst hrs
  have hpl1 : (bytes32 q1 ++ (bytes32 1024 ++ bytes32 (0 + 4 + L))).take 4 ++
      (bytes32 q1 ++ (bytes32 1024 ++ bytes32 (0 + 4 + L))).drop 8 = bytes32 q1 ++ bytes32 (0 + 4 + L) := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 q1), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl1]; clear hpl1
  ihave D1 := KeyGet.split64 n (s - 112 + 40).toNat q1 (0 + 4 + L) $$ D1
  icases D1 with ⟨D10, D14⟩
  ihave D10 := memBytes_addr (show (s - 112 + 40).toNat = (s - 112).toNat + 40 by simp [UInt32.toNat_add, h112]; omega) $$ D10
  ihave D14 := memBytes_addr (show (s - 112 + 40).toNat + 4 = (s - 112).toNat + 44 by simp [UInt32.toNat_add, h112]; omega) $$ D14
  mstep; mstep [D14] with (simp [bytes32, loadWidth, NumType.byteWidth]); mstep
  mstep; mstep [D10] with (simp [bytes32, loadWidth, NumType.byteWidth]); mstep
  -- 397: the Borsh value
  iunfold grown at Hgr1
  icases Hgr1 with ⟨%l1, %hl1, Hinv⟩
  have hL1 : LenIn len 1 l1 := lenIn_step 1024 (by decide) (lenIn_zero len hroom.1) hl1
  ihave V2 := memBytes_addr (show s.toNat - 32 = (s - 112 + 80).toNat by simp [UInt32.toNat_add, h112]; omega) $$ V2
  mstep; mstep; mstep; mstep
  mcall (LookupMapBorsh.f397_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 112)
      (s - 112 + 80) w idx maxP l1 ((q1.toNat, 1024) :: live) F hF b0 b1 v2b (by omega) hb0 hb1 hv2b
      (by simp [UInt32.toNat_add, h112]; omega) hw (roomFor_ofK 1024 (by decide) hroom hL1 (by omega)))
      using [Hg Lo Hvt Hinv B0 B1 V2] with (rw [hK397]; mstep_norm_full; omega)
  · iunfold pre397
    iframe Hg Lo Hvt Hinv B0 B1 V2
    ipureintro; rfl
  rw [hK397]
  iunfold post397 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, B0, B1, %q2, %rest2, %⟨hq20, hq2b, hrest2⟩, Hgr2, V20, V24, V28, Wv, Rest2⟩
  subst hrs
  -- 779: (q2, 16)
  ihave VV2 := KeyGet.join64 n (s - 112 + 80).toNat q2 1024 $$ [V20 V24]
  · iframe V20 V24
  ihave VV2 := BorshFT.joinB (n := n) (a := (s - 112 + 80).toNat) (b := (s - 112 + 80).toNat + 8)
    (bytes32 q2 ++ bytes32 1024) (bytes32 (0 + 16)) (by simp [bytes32]) $$ [VV2 V28]
  · iframe VV2 V28
  ihave D2 := memBytes_addr (show s.toNat - 80 = (s - 112 + 32).toNat by simp [UInt32.toNat_add, h112]; omega) $$ D2
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 112 + 32) (s - 112 + 80) d2b
      (bytes32 q2 ++ bytes32 1024 ++ bytes32 (0 + 16)) hd2b (by simp [bytes32])) using [D2 VV2]
  · iunfold VecDeref.pre
    iframe D2 VV2
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D2, VV2⟩
  subst hrs
  have hpl2 : (bytes32 q2 ++ (bytes32 1024 ++ bytes32 (0 + 16))).take 4 ++
      (bytes32 q2 ++ (bytes32 1024 ++ bytes32 (0 + 16))).drop 8 = bytes32 q2 ++ bytes32 (0 + 16) := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 q2), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl2]; clear hpl2
  ihave D2 := KeyGet.split64 n (s - 112 + 32).toNat q2 (0 + 16) $$ D2
  icases D2 with ⟨D20, D24⟩
  ihave D20 := memBytes_addr (show (s - 112 + 32).toNat = (s - 112).toNat + 32 by simp [UInt32.toNat_add, h112]; omega) $$ D20
  ihave D24 := memBytes_addr (show (s - 112 + 32).toNat + 4 = (s - 112).toNat + 36 by simp [UInt32.toNat_add, h112]; omega) $$ D24
  -- 391: insert_raw
  iunfold grown at Hgr2
  icases Hgr2 with ⟨%l2, %hl2, Hinv⟩
  have hL2 : LenIn len 2 l2 := lenIn_step 1024 (by decide) hL1 hl2
  ihave O := memBytes_addr (show s.toNat - 64 = (s - 112 + 48).toNat by simp [UInt32.toNat_add, h112]; omega) $$ O
  ihave Lo := stk_addr (show (s - 112).toNat - 128 = s.toNat - 240 by omega) $$ Lo
  ihave Lo := stkJ (n := n) (show s.toNat - 240 = s.toNat - 272 + 32 by omega) $$ [Lo32 Lo]
  · iframe Lo32 Lo
  ihave Lo := stk_addr (show s.toNat - 272 = (s - 112).toNat - 160 by omega) $$ Lo
  have hplk : (pl + (0 + 4 + L)).toNat = pl.toNat + (4 + L.toNat) := by simp [UInt32.toNat_add]; omega
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep [D20] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D24] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall (LookupMapInsert.f391_none cfg lim (d + 1) types[36]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 112) (s - 112 + 48) m pp pc pl q1 (0 + 4 + L) q2 (0 + 16) idx maxP l2
      ((q2.toNat, 1024) :: (q1.toNat, 1024) :: live) F hF pre (bytes32 L ++ key) (b0 ++ b1) obb
      (by omega) (by rw [h112]; omega) hobb (by simp [UInt32.toNat_add, h112]; omega) hpre hKL
      (by simp [hb0, hb1]) (by decide) (by rw [hk4]; omega) (by rw [hk4]; omega) hpp (by rw [hk4]; omega)
      (roomFor_ofK _ (by rw [hplk]; omega) hroom hL2 (by omega))
      h st hview hacc hlim hvlim hb hz hlink hproof hbud (by intro x hx; rw [hnone] at hx; cases hx) hnone)
      using [Hg Lo HI HW Hvt Hinv Hm Hp Wk Wv O Hhost]
      with (rw [show ((0:UInt32) + 16).toNat = 16 from rfl, hKw, hK510]; mstep_norm_full; omega)
  · iunfold pre391
    iframe Hg Lo HI HW Hvt Hinv Hm Hp Wk Wv O Hhost
    ipureintro; rfl
  rw [show ((0:UInt32) + 16).toNat = 16 from rfl, hKw, hK510]
  iunfold post391 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, HW, Hvt, ⟨%l3, %hl3, Hinv⟩, Hm, Hp, Wk, Wv, O, Hhost⟩
  subst hrs
  have hL3 : LenIn len 3 l3 := lenIn_step _ (by rw [hplk]; omega) hL2 hl3
  ihave O := memBytes_addr (show (s - 112 + 48).toNat = (s - 112).toNat + 48 by simp [UInt32.toNat_add, h112]; omega) $$ O
  mstep; mstep; mstep; mstep [O]; mstep; mstep; mstep; mstep
  -- 321(sp + 80): the value's buffer
  ihave VV2 := BorshFT.splitB (n := n) (a := (s - 112 + 80).toNat) (b := (s - 112 + 80).toNat + 4) (bytes32 q2)
    (bytes32 1024 ++ bytes32 (0 + 16)) (by simp [bytes32]) $$ VV2
  icases VV2 with ⟨P0, VV2⟩
  ihave VV2 := KeyGet.split64 n ((s - 112 + 80).toNat + 4) 1024 (0 + 16) $$ VV2
  icases VV2 with ⟨P4, P8⟩
  ihave Blk2 : AllocInv.block n q2.toNat (1024 : UInt32).toNat $$ [Wv Rest2]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := q2.toNat) (b := q2.toNat + 16) (b0 ++ b1) rest2
      (by simp [hb0, hb1]) $$ [Wv Rest2]
    · iframe Wv Rest2
    iframe X
    ipureintro; simp [hb0, hb1, hrest2]
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP l3
      ((q2.toNat, 1024) :: (q1.toNat, 1024) :: live) (F + 1) (s - 112 + 80) q2 1024 (0 + 16)
      (by decide) (by simp [UInt32.toNat_add, h112]; omega)) using [P0 P4 P8 Hinv Blk2]
  · iunfold pre747
    ihave P8 := memBytes_addr (show (s - 112 + 80).toNat + 4 + 4 = (s - 112 + 80).toNat + 8 by omega) $$ P8
    simp only [UInt32.reduceToNat]
    iframe P0 P4 P8 Hinv Blk2
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, Hinv⟩
  subst hrs
  -- 321(sp + 64): the key's buffer
  ihave VV1 := BorshFT.splitB (n := n) (a := (s - 112 + 64).toNat) (b := (s - 112 + 64).toNat + 4) (bytes32 q1)
    (bytes32 1024 ++ bytes32 (0 + 4 + L)) (by simp [bytes32]) $$ VV1
  icases VV1 with ⟨K0, VV1⟩
  ihave VV1 := KeyGet.split64 n ((s - 112 + 64).toNat + 4) 1024 (0 + 4 + L) $$ VV1
  icases VV1 with ⟨K4, K8⟩
  ihave Blk1 : AllocInv.block n q1.toNat (1024 : UInt32).toNat $$ [Wk Rest1]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := q1.toNat) (b := q1.toNat + (4 + L.toNat)) (bytes32 L ++ key) rest1
      (by simp [bytes32, hkey]) $$ [Wk Rest1]
    · iframe Wk Rest1
    iframe X
    ipureintro; simp [bytes32, hkey, hrest1]; omega
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP l3
      ((q1.toNat, 1024) :: live) (F + 1 + 1) (s - 112 + 64) q1 1024 (0 + 4 + L)
      (by decide) (by simp [UInt32.toNat_add, h112]; omega)) using [K0 K4 K8 Hinv Blk1]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 112 + 64).toNat + 4 + 4 = (s - 112 + 64).toNat + 8 by omega) $$ K8
    simp only [UInt32.reduceToNat]
    iframe K0 K4 K8 Hinv Blk1
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  -- None at out
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8) 8 (ob.drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨Q8, Q16⟩
  have hq0 : (ob.take 8).length = 8 := by simp; omega
  have hq8 : ((ob.drop 8).take 8).length = 8 := by simp; omega
  have hq16 : ((ob.drop 8).drop 8).length = 8 := by simp; omega
  have ho16 : (out + 16).toNat = out.toNat + 16 := by simp [UInt32.toNat_add]; omega
  ihave Q16 := memBytes_addr (show out.toNat + 8 + 8 = (out + 16).toNat by simp [UInt32.toNat_add]; omega) $$ Q16
  mstep; mstep; mstep; mstep; mstep [Q16] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 112 + 112 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post401
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI HW Hvt Hm Hp Hv Hkey B0 B1
  have e80 : (s - 112 + 80).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h112]; omega
  have e64 : (s - 112 + 64).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, h112]; omega
  isplitl [Lo U0 D20 D24 D10 D14 O U52 K0 K4 K8 U76 P0 P4 P8 U92]
  · ihave P8 := BorshFT.stkW (b := s.toNat - 24) _ (by omega) $$ P8
    ihave X := BorshFT.stkJ (a := s.toNat - 24) (b := s.toNat - 20) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [P8 U92]
    · iframe P8 U92
    ihave P4 := BorshFT.stkW (b := s.toNat - 28) _ (by omega) $$ P4
    ihave X := BorshFT.stkJ (a := s.toNat - 28) (b := s.toNat - 24) (k1 := 4) (k2 := 24) (k := 28) (by omega) rfl $$ [P4 X]
    · iframe P4 X
    ihave P0 := BorshFT.stkW (b := s.toNat - 32) _ (by omega) $$ P0
    ihave X := BorshFT.stkJ (a := s.toNat - 32) (b := s.toNat - 28) (k1 := 4) (k2 := 28) (k := 32) (by omega) rfl $$ [P0 X]
    · iframe P0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 36) (b := s.toNat - 32) (k1 := 4) (k2 := 32) (k := 36) (by omega) rfl $$ [U76 X]
    · iframe U76 X
    ihave K8 := BorshFT.stkW (b := s.toNat - 40) _ (by omega) $$ K8
    ihave X := BorshFT.stkJ (a := s.toNat - 40) (b := s.toNat - 36) (k1 := 4) (k2 := 36) (k := 40) (by omega) rfl $$ [K8 X]
    · iframe K8 X
    ihave K4 := BorshFT.stkW (b := s.toNat - 44) _ (by omega) $$ K4
    ihave X := BorshFT.stkJ (a := s.toNat - 44) (b := s.toNat - 40) (k1 := 4) (k2 := 40) (k := 44) (by omega) rfl $$ [K4 X]
    · iframe K4 X
    ihave K0 := BorshFT.stkW (b := s.toNat - 48) _ (by omega) $$ K0
    ihave X := BorshFT.stkJ (a := s.toNat - 48) (b := s.toNat - 44) (k1 := 4) (k2 := 44) (k := 48) (by omega) rfl $$ [K0 X]
    · iframe K0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 60) (b := s.toNat - 48) (k1 := 12) (k2 := 48) (k := 60) (by omega) rfl $$ [U52 X]
    · iframe U52 X
    ihave O := BorshFT.stkW (b := s.toNat - 64) _ (by omega) $$ O
    ihave X := BorshFT.stkJ (a := s.toNat - 64) (b := s.toNat - 60) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [O X]
    · iframe O X
    ihave D14 := BorshFT.stkW (b := s.toNat - 68) _ (by omega) $$ D14
    ihave X := BorshFT.stkJ (a := s.toNat - 68) (b := s.toNat - 64) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [D14 X]
    · iframe D14 X
    ihave D10 := BorshFT.stkW (b := s.toNat - 72) _ (by omega) $$ D10
    ihave X := BorshFT.stkJ (a := s.toNat - 72) (b := s.toNat - 68) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [D10 X]
    · iframe D10 X
    ihave D24 := BorshFT.stkW (b := s.toNat - 76) _ (by omega) $$ D24
    ihave X := BorshFT.stkJ (a := s.toNat - 76) (b := s.toNat - 72) (k1 := 4) (k2 := 72) (k := 76) (by omega) rfl $$ [D24 X]
    · iframe D24 X
    ihave D20 := BorshFT.stkW (b := s.toNat - 80) _ (by omega) $$ D20
    ihave X := BorshFT.stkJ (a := s.toNat - 80) (b := s.toNat - 76) (k1 := 4) (k2 := 76) (k := 80) (by omega) rfl $$ [D20 X]
    · iframe D20 X
    ihave X := BorshFT.stkJ (a := s.toNat - 112) (b := s.toNat - 80) (k1 := 32) (k2 := 80) (k := 112) (by omega) rfl $$ [U0 X]
    · iframe U0 X
    ihave Lo := BorshFT.stkA (b := s.toNat - 272) (by omega) $$ Lo
    iapply BorshFT.stkJ (a := s.toNat - 272) (b := s.toNat - 112) (k1 := 160) (k2 := 112) (k := 272) (by omega) rfl
    iframe Lo X
  isplitl [Hinv]
  · iexists l3
    rw [show F + 1 + 1 + 1 = F + 3 by omega]
    iframe Hinv
    ipureintro; exact hL3
  isplitl [Q0 Q8 Q16]
  · rw [show storeBytes (Value.i64 0) 8 = List.replicate 8 0 from rfl] at *
    ihave Q16 := memBytes_addr (show (out + 16).toNat = out.toNat + 8 + 8 by omega) $$ Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat + 8) (b := out.toNat + 8 + 8) (List.replicate 8 0)
      (List.replicate 8 0) (by simp) $$ [Q8 Q16]
    · iframe Q8 Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat) (b := out.toNat + 8) (List.replicate 8 0)
      (List.replicate 8 0 ++ List.replicate 8 0) (by simp) $$ [Q0 X]
    · iframe Q0 X
    rw [show List.replicate 8 (0 : UInt8) ++ (List.replicate 8 0 ++ List.replicate 8 0) = List.replicate 24 0 from rfl] at *
    iexact X
  iexact Hhost

end S401

/-! ## `remove` (402) on a present key -/

section S402

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StorageRemove (rslot)
open WNear.Binary.LookupMapRemove (code393 pre393 post393)

/-- The code of 402 (persistent). -/
def code402 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code393 e n maxP inst mi A mx ∗ code395 n maxP inst mi A ∗ code398 inst mi A ∗
    A 395 ↪[wf] FuncInst.wasm types[14]! inst f395 ∗ A 393 ↪[wf] FuncInst.wasm types[45]! inst f393 ∗
    A 398 ↪[wf] FuncInst.wasm types[31]! inst f398)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code402 (GF := GF) e n maxP inst mi A mx) := by
  unfold code402; infer_instance

def pre402 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 288) 288 ∗ ifaceR n ta A ∗ rslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

/-- `Some(u128)` at `out`: the word 1 (`i64`), then the 16 bytes `b0 ++ b1` read back. -/
def post402 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 288) 288 ∗ ifaceR n ta A ∗ rslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 3 len'⌝ ∗ heapInv n maxP len' live (F + 3)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] (storeBytes (.i64 1) 8 ++ (b0 ++ b1)) ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 402, activation excluded. -/
def cost402 (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k b : List UInt8) : Nat :=
  2114 * cfg.regularOpCost + cost395 cfg F L + cost510 cfg F pl (0 + 4 + L) +
    storageRemoveUse h k (pl + (0 + 4 + L)).toNat +
    ReadRegisterF.cost523F cfg F (h.setRegister evictedRegister.toNat b) evictedRegister

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- **`LookupMap::remove`** (402) of the `String` `key` at `v`, present in storage with the `u128`
`b0 ++ b1`: `Some(u128)` at `out`, the host as `StorageRemovePost`, both buffers freed. -/
theorem f402_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key b0 b1 ob : List UInt8)
    (hs : 288 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 24) (hout : out.toNat + 24 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 3 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : removeProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key)))
      (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (b0 ++ b1)) :
    code402 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f402 Cg
        (pre402 n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key ob h)
        (fun _ => cost402 cfg F pl L h (pre ++ (bytes32 L ++ key)) (b0 ++ b1))
        (post402 n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key b0 b1
          (StorageRemovePost e h (pre ++ (bytes32 L ++ key)) evictedRegister st)) := by
  iintro #Hk
  iunfold code402 at Hk
  icases Hk with ⟨#H393c, #H395c, #H398c, #F395, #F393, #F398⟩
  ihave #Hdrop : dropCode inst mi A $$ []
  · iunfold code393 at H393c; icases H393c with ⟨-, #H, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code393, code392 at H393c; icases H393c with ⟨⟨-, -, #H⟩, -⟩; iexact H
  ihave #F321 : A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 $$ []
  · iunfold code393 at H393c; icases H393c with ⟨-, -, -, -, -, -, -, -, #H, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha395 := hm.funcs 395 (by decide)
  have ha393 := hm.funcs 393 (by decide)
  have ha398 := hm.funcs 398 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h80 : (s - 80).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hk4 : (0 + 4 + L).toNat = 4 + L.toNat := by simp [UInt32.toNat_add]; omega
  have hKL : (bytes32 L ++ key).length = (0 + 4 + L).toNat := by simp [bytes32, hkey, hk4]; omega
  have hplk : (pl + (0 + 4 + L)).toNat = pl.toNat + (4 + L.toNat) := by simp [UInt32.toNat_add]; omega
  have hv16 : (b0 ++ b1).length = 16 := by simp [hb0, hb1]
  unfold cost402
  generalize hK395 : cost395 cfg F L = K395
  generalize hKr : storageRemoveUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  generalize hK510 : cost510 cfg F pl (0 + 4 + L) = K510
  generalize hK523 : ReadRegisterF.cost523F cfg F (h.setRegister evictedRegister.toNat (b0 ++ b1)) evictedRegister = K523
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre402 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HR, Hvt, Hinv, Hm, Hp, Hv, Hkey, Ho, Hhost⟩
  subst hargs
  -- the callees' 208, then the frame
  icases stk_split n (s.toNat - 288) 208 80 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 288 + 208 = s.toNat - 80 by omega]
  icases stk_split n (s.toNat - 80) 16 64 $$ Fr with ⟨T, Fr⟩
  rw [show s.toNat - 80 + 16 = s.toNat - 64 by omega]
  icases stk_split n (s.toNat - 64) 8 56 $$ Fr with ⟨D2, Fr⟩
  rw [show s.toNat - 64 + 8 = s.toNat - 56 by omega]
  icases stk_split n (s.toNat - 56) 8 48 $$ Fr with ⟨D1, Fr⟩
  rw [show s.toNat - 56 + 8 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 12 36 $$ Fr with ⟨O, Fr⟩
  rw [show s.toNat - 48 + 12 = s.toNat - 36 by omega]
  icases stk_split n (s.toNat - 36) 4 32 $$ Fr with ⟨U44, Fr⟩
  rw [show s.toNat - 36 + 4 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 12 20 $$ Fr with ⟨V1, Fr⟩
  rw [show s.toNat - 32 + 12 = s.toNat - 20 by omega]
  icases stk_split n (s.toNat - 20) 4 16 $$ Fr with ⟨U60, Fr⟩
  rw [show s.toNat - 20 + 4 = s.toNat - 16 by omega]
  icases stk_split n (s.toNat - 16) 12 4 $$ Fr with ⟨Cp, U76⟩
  rw [show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  iunfold stk at V1 D1 D2 O T Cp
  icases V1 with ⟨%v1b, %hv1b, V1⟩
  icases D1 with ⟨%d1b, %hd1b, D1⟩
  icases D2 with ⟨%d2b, %hd2b, D2⟩
  icases O with ⟨%obb, %hobb, O⟩
  icases T with ⟨%tb, %htb, T⟩
  icases Cp with ⟨%cb, %hcb, Cp⟩
  icases stk_split n (s.toNat - 288) 80 128 $$ Lo with ⟨Lo80, Lo⟩
  rw [show s.toNat - 288 + 80 = s.toNat - 208 by omega]
  simp only [f402]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 395: the Borsh key
  mstep; mstep; mstep; mstep
  mcall (LookupMapBorsh.f395_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 80)
      (s - 80 + 48) v p c L idx maxP len live F hF key v1b (by omega) hkey (by omega) hv1b
      (by simp [UInt32.toNat_add, h80]; omega) hv hp (roomFor_ofK 1024 (by decide) hroom (lenIn_zero len hroom.1) (by omega)))
      using [Hg Lo Hvt Hinv Hv Hkey V1] with (rw [hK395]; mstep_norm_full; omega)
  · iunfold pre395
    ihave Lo := stk_addr (show s.toNat - 208 = (s - 80).toNat - 128 by omega) $$ Lo
    ihave V1 := memBytes_addr (show s.toNat - 32 = (s - 80 + 48).toNat by simp [UInt32.toNat_add, h80]; omega) $$ V1
    iframe Hg Lo Hvt Hinv Hv Hkey V1
    ipureintro; rfl
  rw [hK395]
  iunfold post395 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hv, Hkey, %q1, %rest1, %⟨hq10, hq1b, hrest1⟩, Hgr1, V10, V14, V18, Wk, Rest1⟩
  subst hrs
  -- 779: (q1, 4 + L)
  ihave VV1 := KeyGet.join64 n (s - 80 + 48).toNat q1 1024 $$ [V10 V14]
  · iframe V10 V14
  ihave VV1 := BorshFT.joinB (n := n) (a := (s - 80 + 48).toNat) (b := (s - 80 + 48).toNat + 8)
    (bytes32 q1 ++ bytes32 1024) (bytes32 (0 + 4 + L)) (by simp [bytes32]) $$ [VV1 V18]
  · iframe VV1 V18
  ihave D1 := memBytes_addr (show s.toNat - 56 = (s - 80 + 24).toNat by simp [UInt32.toNat_add, h80]; omega) $$ D1
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 80 + 24) (s - 80 + 48) d1b
      (bytes32 q1 ++ bytes32 1024 ++ bytes32 (0 + 4 + L)) hd1b (by simp [bytes32])) using [D1 VV1]
  · iunfold VecDeref.pre
    iframe D1 VV1
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D1, VV1⟩
  subst hrs
  have hpl1 : (bytes32 q1 ++ (bytes32 1024 ++ bytes32 (0 + 4 + L))).take 4 ++
      (bytes32 q1 ++ (bytes32 1024 ++ bytes32 (0 + 4 + L))).drop 8 = bytes32 q1 ++ bytes32 (0 + 4 + L) := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 q1), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl1]; clear hpl1
  ihave D1 := KeyGet.split64 n (s - 80 + 24).toNat q1 (0 + 4 + L) $$ D1
  icases D1 with ⟨D10, D14⟩
  ihave D10 := memBytes_addr (show (s - 80 + 24).toNat = (s - 80).toNat + 24 by simp [UInt32.toNat_add, h80]; omega) $$ D10
  ihave D14 := memBytes_addr (show (s - 80 + 24).toNat + 4 = (s - 80).toNat + 28 by simp [UInt32.toNat_add, h80]; omega) $$ D14
  -- 393: remove_raw
  iunfold grown at Hgr1
  icases Hgr1 with ⟨%l1, %hl1, Hinv⟩
  have hL1 : LenIn len 1 l1 := lenIn_step 1024 (by decide) (lenIn_zero len hroom.1) hl1
  ihave O := memBytes_addr (show s.toNat - 48 = (s - 80 + 32).toNat by simp [UInt32.toNat_add, h80]; omega) $$ O
  ihave Lo := stk_addr (show (s - 80).toNat - 128 = s.toNat - 208 by omega) $$ Lo
  ihave Lo := stkJ (n := n) (show s.toNat - 208 = s.toNat - 288 + 80 by omega) $$ [Lo80 Lo]
  · iframe Lo80 Lo
  ihave Lo := stk_addr (show s.toNat - 288 = (s - 80).toNat - 208 by omega) $$ Lo
  mstep; mstep; mstep; mstep
  mstep; mstep [D10] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D14] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall (LookupMapRemove.f393_some cfg lim (d + 1) types[45]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 80) (s - 80 + 32) m pp pc pl q1 (0 + 4 + L) idx maxP l1
      ((q1.toNat, 1024) :: live) F hF pre (bytes32 L ++ key) obb (b0 ++ b1)
      (by omega) (by rw [h80]; omega) hobb (by simp [UInt32.toNat_add, h80]; omega) hpre hKL
      (by rw [hk4]; omega) (by rw [hk4]; omega) hpp (by rw [hk4]; omega)
      (roomFor_ofK _ (by rw [hplk]; omega) hroom hL1 (by omega)) (by rw [hv16]; decide) (by rw [hv16]; decide)
      (fun l hl => roomFor_ofK _ (by rw [hv16]; decide) hroom
        (lenIn_step _ (by rw [hplk]; omega) hL1 hl) (by omega))
      h st hview hacc hlim hb hz hlink hproof hbud
      (by intro x hx; rw [hsome] at hx; cases hx; rw [hv16]; exact hreg) hsome)
      using [Hg Lo HI HR Hvt Hinv Hm Hp Wk O Hhost]
      with (rw [hKr, hK510, hK523]; mstep_norm_full; omega)
  · iunfold pre393
    iframe Hg Lo HI HR Hvt Hinv Hm Hp Wk O Hhost
    ipureintro; rfl
  rw [hKr, hK510, hK523]
  iunfold post393 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, HR, Hvt, Hm, Hp, Wk, ⟨%pv, %hpv0, P0, P4, P8, Pv, %len1, %len2, %⟨hlen1, hlen2⟩, Hinv⟩, Hhost⟩
  subst hrs
  have hsz : (pl + (0 + 4 + L)).toNat ≤ 4096 := by rw [hplk]; omega
  have hL3 : LenIn len 3 len2 :=
    lenIn_step _ (by rw [hv16]; decide) (lenIn_step _ hsz hL1 hlen1) hlen2
  simp only [hv16]
  rw [show (UInt32.ofNat 16 : UInt32) = 16 from rfl]
  ihave P0 := memBytes_addr (show (s - 80 + 32).toNat = (s - 80).toNat + 32 by simp [UInt32.toNat_add, h80]; omega) $$ P0
  -- the Some branch
  mstep; mstep; mstep; mstep [P0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr
  · ipureintro; exact ⟨rfl, hpv0⟩
  mctrl_norm; mpay
  -- [sp+72] := [sp+40]; [sp+64..72) := [sp+32..40)
  ihave P8 := memBytes_addr (show (s - 80 + 32).toNat + 8 = (s - 80 + 32 + 8).toNat by simp [UInt32.toNat_add, h80]; omega) $$ P8
  ihave Cp := U128From.memBytes_split n (s.toNat - 16) 8 cb (by omega) $$ Cp
  icases Cp with ⟨C0, C8⟩
  have hc8 : (cb.drop 8).length = 4 := by simp; omega
  have hc0 : (cb.take 8).length = 8 := by simp; omega
  ihave C0 := memBytes_addr (show s.toNat - 16 = (s - 80).toNat + 64 by omega) $$ C0
  ihave C8 := memBytes_addr (show s.toNat - 16 + 8 = (s - 80 + 64 + 8).toNat by simp [UInt32.toNat_add, h80]; omega) $$ C8
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [P8] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep [C8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  ihave P0 := memBytes_addr (show (s - 80).toNat + 32 = (s - 80 + 32).toNat by simp [UInt32.toNat_add, h80]; omega) $$ P0
  ihave PP := KeyGet.join64 n (s - 80 + 32).toNat pv 16 $$ [P0 P4]
  · iframe P0 P4
  ihave PP := memBytes_addr (show (s - 80 + 32).toNat = (s - 80).toNat + 32 by simp [UInt32.toNat_add, h80]; omega) $$ PP
  mstep; mstep; mstep [PP] with (simp [bytes32, loadWidth, NumType.byteWidth])
  rw [VecFromElem.ofNat_decode_pair]
  mstep [C0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [VecFromElem.storeBytes_pair64]
  rw [show (UInt32.ofNat 16 : UInt32) = 16 from rfl]
  -- 779(sp + 16, sp + 64): (pv, 16)
  ihave C0 := memBytes_addr (show (s - 80).toNat + 64 = (s - 80 + 64).toNat by simp [UInt32.toNat_add, h80]; omega) $$ C0
  ihave C8 := memBytes_addr (show (s - 80 + 64 + 8).toNat = (s - 80 + 64).toNat + (bytes32 pv ++ bytes32 16).length by simp [bytes32, UInt32.toNat_add, h80]; omega) $$ C8
  ihave CC := BorshFT.joinB (n := n) (a := (s - 80 + 64).toNat) (b := (s - 80 + 64).toNat + (bytes32 pv ++ bytes32 16).length)
    (bytes32 pv ++ bytes32 16) (bytes32 16) rfl $$ [C0 C8]
  · iframe C0 C8
  ihave D2 := memBytes_addr (show s.toNat - 64 = (s - 80 + 16).toNat by simp [UInt32.toNat_add, h80]; omega) $$ D2
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 80 + 16) (s - 80 + 64) d2b
      (bytes32 pv ++ bytes32 16 ++ bytes32 16) hd2b (by simp [bytes32])) using [D2 CC]
  · iunfold VecDeref.pre
    iframe D2 CC
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D2, CC⟩
  subst hrs
  have hpl2 : (bytes32 pv ++ (bytes32 16 ++ bytes32 16)).take 4 ++
      (bytes32 pv ++ (bytes32 16 ++ bytes32 16)).drop 8 = bytes32 pv ++ bytes32 16 := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 pv), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl2]; clear hpl2
  ihave D2 := KeyGet.split64 n (s - 80 + 16).toNat pv 16 $$ D2
  icases D2 with ⟨D20, D24⟩
  ihave D20 := memBytes_addr (show (s - 80 + 16).toNat = (s - 80).toNat + 16 by simp [UInt32.toNat_add, h80]; omega) $$ D20
  ihave D24 := memBytes_addr (show (s - 80 + 16).toNat + 4 = (s - 80).toNat + 20 by simp [UInt32.toNat_add, h80]; omega) $$ D24
  -- 398(sp, pv, 16): the u128
  icases stk_split n ((s - 80).toNat - 208) 64 144 $$ Lo with ⟨Lo64, Lo⟩
  ihave Lo := stk_addr (show (s - 80).toNat - 208 + 64 = (s - 80).toNat - 144 by omega) $$ Lo
  ihave Pv := BorshFT.splitB (n := n) (a := pv.toNat) (b := pv.toNat + 8) b0 b1 (by simp [hb0]) $$ Pv
  icases Pv with ⟨Pv0, Pv8⟩
  ihave T := memBytes_addr (show s.toNat - 80 = (s - 80).toNat by omega) $$ T
  icases FmtSink.heapInv_bound (p := pv.toNat) (s := 16) (by simp) $$ Hinv with ⟨%hpvb, Hinv⟩
  mstep; mstep; mstep [D20] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D24] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall (LookupMapBorsh.f398_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 80)
      (s - 80) pv b0 b1 tb (by omega) hb0 hb1 htb (by omega) (by omega)) using [Hg Lo Pv0 Pv8 T]
  · iunfold pre398
    iframe Hg Lo Pv0 Pv8 T
    ipureintro; rfl
  iunfold post398 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Pv0, Pv8, T0, T8⟩
  subst hrs
  have h72 : (s - 80 + 8).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, h80]; omega
  have hb0n : b0 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hb1n : b1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hw0 : b0.length = loadWidth NumType.i64 none := by simp [hb0, loadWidth, NumType.byteWidth]
  have hw1 : b1.length = loadWidth NumType.i64 none := by simp [hb1, loadWidth, NumType.byteWidth]
  mstep; mstep; mstep; mstep [T8] with (first | (rw [h72, h80]; dsimp only; omega) | (simp [hb1, loadWidth, NumType.byteWidth]) | exact List.ne_nil_of_length_pos (by omega)); mstep
  mstep; mstep [T0] with (first | (simp [UInt32.toNat_add, h80]; omega) | (simp [hb0, loadWidth, NumType.byteWidth]) | exact List.ne_nil_of_length_pos (by omega)); mstep
  -- 321(sp + 64): the value's buffer
  ihave CC := BorshFT.splitB (n := n) (a := (s - 80 + 64).toNat) (b := (s - 80 + 64).toNat + 4) (bytes32 pv)
    (bytes32 16 ++ bytes32 16) (by simp [bytes32]) $$ CC
  icases CC with ⟨C0, CC⟩
  ihave CC := KeyGet.split64 n ((s - 80 + 64).toNat + 4) 16 16 $$ CC
  icases CC with ⟨C4, C8⟩
  ihave Blk2 : AllocInv.block n pv.toNat 16 $$ [Pv0 Pv8]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := pv.toNat) (b := pv.toNat + 8) b0 b1 (by simp [hb0]) $$ [Pv0 Pv8]
    · iframe Pv0 Pv8
    iframe X
    ipureintro; simp [hb0, hb1]
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len2
      ((pv.toNat, 16) :: (q1.toNat, 1024) :: live) (F + 1) (s - 80 + 64) pv 16 16
      (by decide) (by simp [UInt32.toNat_add, h80]; omega)) using [C0 C4 C8 Hinv Blk2]
  · iunfold pre747
    ihave C8 := memBytes_addr (show (s - 80 + 64).toNat + 4 + 4 = (s - 80 + 64).toNat + 8 by omega) $$ C8
    simp only [UInt32.reduceToNat]
    iframe C0 C4 C8 Hinv Blk2
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, C0, C4, C8, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  mstep; mstep
  -- 321(sp + 48): the key's buffer
  ihave VV1 := BorshFT.splitB (n := n) (a := (s - 80 + 48).toNat) (b := (s - 80 + 48).toNat + 4) (bytes32 q1)
    (bytes32 1024 ++ bytes32 (0 + 4 + L)) (by simp [bytes32]) $$ VV1
  icases VV1 with ⟨K0, VV1⟩
  ihave VV1 := KeyGet.split64 n ((s - 80 + 48).toNat + 4) 1024 (0 + 4 + L) $$ VV1
  icases VV1 with ⟨K4, K8⟩
  ihave Blk1 : AllocInv.block n q1.toNat (1024 : UInt32).toNat $$ [Wk Rest1]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := q1.toNat) (b := q1.toNat + (4 + L.toNat)) (bytes32 L ++ key) rest1
      (by simp [bytes32, hkey]) $$ [Wk Rest1]
    · iframe Wk Rest1
    iframe X
    ipureintro; simp [bytes32, hkey, hrest1]; omega
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len2
      ((q1.toNat, 1024) :: live) (F + 1 + 1) (s - 80 + 48) q1 1024 (0 + 4 + L)
      (by decide) (by simp [UInt32.toNat_add, h80]; omega)) using [K0 K4 K8 Hinv Blk1]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 80 + 48).toNat + 4 + 4 = (s - 80 + 48).toNat + 8 by omega) $$ K8
    simp only [UInt32.reduceToNat]
    iframe K0 K4 K8 Hinv Blk1
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  -- Some(u128) at out
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8) 8 (ob.drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨Q8, Q16⟩
  have hq0 : (ob.take 8).length = 8 := by simp; omega
  have hq8 : ((ob.drop 8).take 8).length = 8 := by simp; omega
  have hq16 : ((ob.drop 8).drop 8).length = 8 := by simp; omega
  have ho16 : (out + 16).toNat = out.toNat + 16 := by simp [UInt32.toNat_add]; omega
  ihave Q16 := memBytes_addr (show out.toNat + 8 + 8 = (out + 16).toNat by simp [UInt32.toNat_add]; omega) $$ Q16
  mstep; mstep; mstep; mstep; mstep [Q16] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [BorshLeaves.storeBytes_i64_decode _ hb1]
  mstep; mstep; mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [BorshLeaves.storeBytes_i64_decode _ hb0]
  mstep; mstep; mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 80 + 80 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post402
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI HR Hvt Hm Hp Hv Hkey
  isplitl [Lo64 Lo T0 T8 D20 D24 D10 D14 PP P8 U44 K0 K4 K8 U60 C0 C4 C8 U76]
  · ihave C8 := BorshFT.stkW (b := s.toNat - 8) _ (by simp [UInt32.toNat_add, h80]; omega) $$ C8
    ihave X := BorshFT.stkJ (a := s.toNat - 8) (b := s.toNat - 4) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [C8 U76]
    · iframe C8 U76
    ihave C4 := BorshFT.stkW (b := s.toNat - 12) _ (by simp [UInt32.toNat_add, h80]; omega) $$ C4
    ihave X := BorshFT.stkJ (a := s.toNat - 12) (b := s.toNat - 8) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [C4 X]
    · iframe C4 X
    ihave C0 := BorshFT.stkW (b := s.toNat - 16) _ (by simp [UInt32.toNat_add, h80]; omega) $$ C0
    ihave X := BorshFT.stkJ (a := s.toNat - 16) (b := s.toNat - 12) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [C0 X]
    · iframe C0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 20) (b := s.toNat - 16) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [U60 X]
    · iframe U60 X
    ihave K8 := BorshFT.stkW (b := s.toNat - 24) _ (by simp [UInt32.toNat_add, h80]; omega) $$ K8
    ihave X := BorshFT.stkJ (a := s.toNat - 24) (b := s.toNat - 20) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [K8 X]
    · iframe K8 X
    ihave K4 := BorshFT.stkW (b := s.toNat - 28) _ (by simp [UInt32.toNat_add, h80]; omega) $$ K4
    ihave X := BorshFT.stkJ (a := s.toNat - 28) (b := s.toNat - 24) (k1 := 4) (k2 := 24) (k := 28) (by omega) rfl $$ [K4 X]
    · iframe K4 X
    ihave K0 := BorshFT.stkW (b := s.toNat - 32) _ (by simp [UInt32.toNat_add, h80]; omega) $$ K0
    ihave X := BorshFT.stkJ (a := s.toNat - 32) (b := s.toNat - 28) (k1 := 4) (k2 := 28) (k := 32) (by omega) rfl $$ [K0 X]
    · iframe K0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 36) (b := s.toNat - 32) (k1 := 4) (k2 := 32) (k := 36) (by omega) rfl $$ [U44 X]
    · iframe U44 X
    ihave P8 := BorshFT.stkW (b := s.toNat - 40) _ (by simp [UInt32.toNat_add, h80]; omega) $$ P8
    ihave X := BorshFT.stkJ (a := s.toNat - 40) (b := s.toNat - 36) (k1 := 4) (k2 := 36) (k := 40) (by omega) rfl $$ [P8 X]
    · iframe P8 X
    ihave PP := BorshFT.stkB (b := s.toNat - 48) (k := 8) _ (by omega) (by simp [bytes32]) $$ PP
    ihave X := BorshFT.stkJ (a := s.toNat - 48) (b := s.toNat - 40) (k1 := 8) (k2 := 40) (k := 48) (by omega) rfl $$ [PP X]
    · iframe PP X
    ihave D14 := BorshFT.stkW (b := s.toNat - 52) _ (by omega) $$ D14
    ihave X := BorshFT.stkJ (a := s.toNat - 52) (b := s.toNat - 48) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [D14 X]
    · iframe D14 X
    ihave D10 := BorshFT.stkW (b := s.toNat - 56) _ (by omega) $$ D10
    ihave X := BorshFT.stkJ (a := s.toNat - 56) (b := s.toNat - 52) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [D10 X]
    · iframe D10 X
    ihave D24 := BorshFT.stkW (b := s.toNat - 60) _ (by omega) $$ D24
    ihave X := BorshFT.stkJ (a := s.toNat - 60) (b := s.toNat - 56) (k1 := 4) (k2 := 56) (k := 60) (by omega) rfl $$ [D24 X]
    · iframe D24 X
    ihave D20 := BorshFT.stkW (b := s.toNat - 64) _ (by omega) $$ D20
    ihave X := BorshFT.stkJ (a := s.toNat - 64) (b := s.toNat - 60) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [D20 X]
    · iframe D20 X
    ihave T8 := BorshFT.stkB (b := s.toNat - 72) (k := 8) _ (by omega) hb1 $$ T8
    ihave X := BorshFT.stkJ (a := s.toNat - 72) (b := s.toNat - 64) (k1 := 8) (k2 := 64) (k := 72) (by omega) rfl $$ [T8 X]
    · iframe T8 X
    ihave T0 := BorshFT.stkB (b := s.toNat - 80) (k := 8) _ (by omega) hb0 $$ T0
    ihave X := BorshFT.stkJ (a := s.toNat - 80) (b := s.toNat - 72) (k1 := 8) (k2 := 72) (k := 80) (by omega) rfl $$ [T0 X]
    · iframe T0 X
    ihave Lo := BorshFT.stkA (b := s.toNat - 224) (by omega) $$ Lo
    ihave X := BorshFT.stkJ (a := s.toNat - 224) (b := s.toNat - 80) (k1 := 144) (k2 := 80) (k := 224) (by omega) rfl $$ [Lo X]
    · iframe Lo X
    ihave Lo64 := BorshFT.stkA (b := s.toNat - 288) (by omega) $$ Lo64
    iapply BorshFT.stkJ (a := s.toNat - 288) (b := s.toNat - 224) (k1 := 64) (k2 := 224) (k := 288) (by omega) rfl
    iframe Lo64 X
  isplitl [Hinv]
  · iexists len2
    rw [show F + 1 + 1 + 1 = F + 3 by omega]
    iframe Hinv
    ipureintro; exact hL3
  isplitl [Q0 Q8 Q16]
  · ihave Q16 := memBytes_addr (show (out + 16).toNat = out.toNat + 8 + b0.length by omega) $$ Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat + 8) (b := out.toNat + 8 + b0.length) b0 b1 rfl $$ [Q8 Q16]
    · iframe Q8 Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat) (b := out.toNat + 8) (storeBytes (.i64 1) 8)
      (b0 ++ b1) (by rfl) $$ [Q0 X]
    · iframe Q0 X
    iexact X
  iexact Hhost

end S402

end WNear.Binary.LookupMapOps
