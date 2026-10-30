import Bridge.Functions.LookupMapOps
import Bridge.Functions.MeasureUsageHost
import Bridge.Functions.StrRepeat
import Bridge.Functions.EnvGetters

/-!
# `FungibleToken::measure_account_storage_usage` (404)

```wat
;; 404 measure(c): sp -= 64
;;     before := storage_usage()                         ;; 528
;;     847(sp + 48, "a", 1, 64)                          ;; "a".repeat(64)
;;     401(sp + 24, c + 24, sp + 48, 1052800)            ;; accounts.insert(&key, &0u128): None
;;     after := storage_usage(); d := after - before
;;     d > after → panic "attempt to subtract with overflow" (853, not taken)
;;     c+16 := d                                         ;; account_storage_usage
;;     402(sp, c + 24, sp + 48)                          ;; accounts.remove(&key): Some(0)
;;     321(sp + 48); sp += 64                            ;; the key freed
```

`f404_spec`: on an account whose map holds no `"a" ++ borsh("a" * 64)`, with room in the `u64`
usage counter, the contract's `account_storage_usage` becomes the size of one record of the
map, `69 + 16 + extra`; the host is the write then the removal of that record.
-/

namespace WNear.Binary.MeasureUsage

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (vecCode2 costAllocF okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.StorageWrite (wslot wCode evictedRegister)
open WNear.Binary.StorageRemove (rslot)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.EnvGetters (uslot uCode pre528 post528)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapInsert (code391)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn lenIn_step lenIn_zero roomFor_ofK code401 pre401 post401 cost401
  code402 pre402 post402 cost402)
open Near.TrieOverlay

/-! ## Heap lengths -/

theorem lenIn_trans {a b c j k : Nat} (h1 : LenIn a j b) (h2 : LenIn b k c) : LenIn a (j + k) c := by
  obtain ⟨a1, a2, -⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  refine ⟨Nat.le_trans a1 b1, ?_, b3⟩
  calc c ≤ b + k * 65536 := b2
    _ ≤ (a + j * 65536) + k * 65536 := Nat.add_le_add_right a2 _
    _ = a + (j + k) * 65536 := by rw [Nat.add_mul, Nat.add_assoc]

theorem heapRoom_shift {k k' j a b maxP : Nat} (hr : HeapRoomK k a maxP) (hl : LenIn a j b) (hj : j + k' ≤ k) :
    HeapRoomK k' b maxP := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  obtain ⟨l1, l2, l3⟩ := hl
  have m1 : (j + k') * 65536 ≤ k * 65536 := Nat.mul_le_mul_right _ hj
  have m2 : (j + (k' + 1)) * 65536 ≤ (k + 1) * 65536 := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at m1 m2
  refine ⟨l3, Nat.lt_of_lt_of_le r2 l1, ?_, ?_⟩
  · calc b + k' * 65536 ≤ a + j * 65536 + k' * 65536 := Nat.add_le_add_right l2 _
      _ = a + (j * 65536 + k' * 65536) := Nat.add_assoc _ _ _
      _ ≤ a + k * 65536 := Nat.add_le_add_left m1 _
      _ ≤ maxP * 65536 := r3
  · calc b + (k' + 1) * 65536 ≤ a + j * 65536 + (k' + 1) * 65536 := Nat.add_le_add_right l2 _
      _ = a + (j * 65536 + (k' + 1) * 65536) := Nat.add_assoc _ _ _
      _ ≤ a + (k + 1) * 65536 := Nat.add_le_add_left m2 _
      _ ≤ 2 ^ 32 := r4

/-! ## The record `measure_account_storage_usage` writes and removes -/

/-- The map's key of the dummy account: the prefix `"a"`, then the Borsh `String` `"a" * 64`. -/
def mKey : List UInt8 := [97] ++ (bytes32 64 ++ List.replicate 64 97)

/-- The Borsh `0u128`. -/
def mVal : List UInt8 := List.replicate 8 0 ++ List.replicate 8 0

theorem mKey_length : mKey.length = 69 := by simp [mKey, bytes32]

theorem mVal_length : mVal.length = 16 := by simp [mVal]

section S404

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 404 (persistent). -/
def code404 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code401 e n maxP inst mi A mx ∗ code402 e n maxP inst mi A mx ∗ vecCode2 n maxP inst mi A ∗
    uCode e inst A ∗ A 460 ↪[wf] FuncInst.wasm types[11]! inst f460 ∗
    A 528 ↪[wf] FuncInst.wasm types[19]! inst f528 ∗ A 847 ↪[wf] FuncInst.wasm types[45]! inst f847 ∗
    A 401 ↪[wf] FuncInst.wasm types[45]! inst f401 ∗ A 402 ↪[wf] FuncInst.wasm types[31]! inst f402)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code404 (GF := GF) e n maxP inst mi A mx) := by
  unfold code404; infer_instance

def pre404 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s c pp pc : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (h : NearState)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    ifaceR n ta A ∗ uslot n ta A ∗ wslot n ta A ∗ rslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ n ↦[wms][ c.toNat + 16 ] ob ∗ prefixAt n (c + 24) pp pc 1 ∗
    n ↦[wms][ pp.toNat ] [97] ∗ n ↦[wms][ 1052792 ] [97] ∗ n ↦[wms][ 1052800 ] List.replicate 16 0 ∗
    mhostPt h)

/-- What 404 leaves of the host `h` with accounting `st` and budget `bud`: the write of the record
(`h1`, its accounting `s2` linked and canonical), then its removal. -/
def Post404 (e : Nat) (h : NearState) (st : Near.TrieOverlay.State) (bud : Nat) (h2 : NearState) : Prop :=
  ∃ (h1 : NearState) (s2 : Near.TrieOverlay.State), StorageWritePost e h mKey mVal evictedRegister st h1 ∧ h1.storageAccounting = some s2 ∧
    Canon s2 ∧ StorageLink h1 s2 ∧
    ProofBudget h1 s2 (bud - writeProofCost (contractKey h.context.currentAccountId mKey) none) ∧
    erase h1 = erase (storageWriteHost e h mKey mVal evictedRegister s2) ∧
    StorageRemovePost e h1 mKey evictedRegister s2 h2

/-- `account_storage_usage := 85 + extra`, the heap after at most seven grows with seven more free
cells. -/
def post404 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s c pp pc : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (e : Nat) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    ifaceR n ta A ∗ uslot n ta A ∗ wslot n ta A ∗ rslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜LenIn len 7 len'⌝ ∗ heapInv n maxP len' live (F + 7)) ∗
    n ↦[wms][ c.toNat + 16 ] storeBytes (.i64 (UInt64.ofNat (85 + e))) 8 ∗ prefixAt n (c + 24) pp pc 1 ∗
    n ↦[wms][ pp.toNat ] [97] ∗ n ↦[wms][ 1052792 ] [97] ∗ n ↦[wms][ 1052800 ] List.replicate 16 0 ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 404, activation excluded: `K2` bounds what runs on the host after the write (the
second `storage_usage` and the removal). -/
def cost404 (cfg : WasmConfig) (F : Nat) (h : NearState) (K2 : Nat) : Nat :=
  683 * cfg.regularOpCost + storageUsageUse h + StrRepeat.cost847 cfg F +
    cost401 cfg F 1 64 h mKey + K2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **`measure_account_storage_usage`** (404) on the contract at `c`, its map's prefix `"a"`
(at `pp`), the dummy record absent. -/
theorem f404_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s c pp pc : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8)
    (hs : 352 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 8) (hc : c.toNat + 36 ≤ 2 ^ 32)
    (hpp : pp.toNat + 1 ≤ 2 ^ 32) (hroom : HeapRoomK 7 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hbud : writeProofCost (contractKey h.context.currentAccountId mKey) none +
      removeProofCost (contractKey h.context.currentAccountId mKey) (some mVal) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen 69 = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hnone : h.storage mKey = none)
    (hU : h.context.storageUsage.toNat + (85 + e) < 2 ^ 64)
    (K2 : Nat) (hK2 : ∀ h1 s2, erase h1 = erase (storageWriteHost e h mKey mVal evictedRegister s2) →
      250 * cfg.regularOpCost + storageUsageUse h1 + cost402 cfg (F + 3) 1 64 h1 mKey mVal ≤ K2) :
    code404 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f404 Cg
        (pre404 n g ta A gt s c pp pc idx maxP len live F ob h)
        (fun _ => cost404 cfg F h K2)
        (post404 n g ta A gt s c pp pc idx maxP len live F e (Post404 e h st bud)) := by
  iintro #Hk
  iunfold code404 at Hk
  icases Hk with ⟨#H401c, #H402c, #Hvec, #Hu, #F460, #F528, #F847, #F401, #F402⟩
  ihave #H391c : code391 e n maxP inst mi A mx $$ []
  · iunfold code401 at H401c; icases H401c with ⟨#H, -⟩; iexact H
  ihave #Hdrop : dropCode inst mi A $$ []
  · iunfold code391 at H391c; icases H391c with ⟨-, #H, -⟩; iexact H
  ihave #Hcode : ifaceCode e inst mi A n mx $$ []
  · iunfold code391 at H391c; icases H391c with ⟨-, -, #H, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #F321 : A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 $$ []
  · iunfold code391 at H391c; icases H391c with ⟨-, -, -, -, -, -, -, #H⟩; iexact H
  ihave #H528 : (ifaceCode (GF := GF) e inst mi A n mx ∗ uCode e inst A ∗
      A 460 ↪[wf] FuncInst.wasm types[11]! inst f460) $$ []
  · iframe Hcode Hu F460
  have hn := hm.mem
  have hg := hm.glob
  have ha528 := hm.funcs 528 (by decide)
  have ha847 := hm.funcs 847 (by decide)
  have ha401 := hm.funcs 401 (by decide)
  have ha402 := hm.funcs 402 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t19 : types[19]!.params.length = 0 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h64 : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hc24 : (c + 24).toNat = c.toNat + 24 := by simp [UInt32.toNat_add]; omega
  ihave #S528a := EnvGetters.f528_spec_host cfg lim (d + 1) types[19]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 64) (by omega) (by omega) h $$ H528
  unfold cost404
  generalize hU528 : storageUsageUse h = KU
  generalize hK847 : StrRepeat.cost847 cfg F = K847
  generalize hK401 : cost401 cfg F 1 64 h mKey = K401
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre404 at HP
  icases HP with ⟨%hargs, Hg, Hs, HIR, HU, HW, HR, Hvt, Hinv, H16, Hm, Hp, Ha, Hz, Hhost⟩
  subst hargs
  -- the callees' 288, then the frame: R (24), I (24), K (12), U (4)
  icases stk_split n (s.toNat - 352) 288 64 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 352 + 288 = s.toNat - 64 by omega]
  icases stk_split n (s.toNat - 64) 24 40 $$ Fr with ⟨Rr, Fr⟩
  rw [show s.toNat - 64 + 24 = s.toNat - 40 by omega]
  icases stk_split n (s.toNat - 40) 24 16 $$ Fr with ⟨Ii, Fr⟩
  rw [show s.toNat - 40 + 24 = s.toNat - 16 by omega]
  icases stk_split n (s.toNat - 16) 12 4 $$ Fr with ⟨Kk, U60⟩
  rw [show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  iunfold stk at Rr Ii Kk
  icases Rr with ⟨%rb, %hrb, Rr⟩
  icases Ii with ⟨%ib, %hib, Ii⟩
  icases Kk with ⟨%kb, %hkb, Kk⟩
  iunfold ifaceR at HIR
  icases HIR with ⟨HI, HRS⟩
  simp only [f404]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- before := storage_usage()
  icases stk_split n (s.toNat - 352) 272 16 $$ Lo with ⟨Lo, L16⟩
  rw [show s.toNat - 352 + 272 = s.toNat - 80 by omega]
  mcall S528a using [Hg HI HU L16 Hhost] with (mstep_norm_full; omega)
  · iunfold pre528
    ihave L16 := stk_addr (show s.toNat - 80 = (s - 64).toNat - 16 by omega) $$ L16
    iframe Hg HI HU L16 Hhost
    ipureintro; rfl
  iunfold post528 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HU, L16, Hhost⟩
  subst hrs
  mstep
  -- "a".repeat(64) at sp + 48
  ihave L16 := stk_addr (show (s - 64).toNat - 16 = s.toNat - 352 + 272 by rw [h64]; omega) $$ L16
  ihave Lo := stk_join n (s.toNat - 352) 272 16 $$ [Lo L16]
  · iframe Lo L16
  icases stk_split n (s.toNat - 352) 240 48 $$ Lo with ⟨Lo, L48⟩
  rw [show s.toNat - 352 + 240 = s.toNat - 112 by omega]
  ihave Kk := memBytes_addr (show s.toNat - 16 = (s - 64 + 48).toNat by simp [UInt32.toNat_add, h64]; omega) $$ Kk
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (StrRepeat.f847_spec cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 64)
      (s - 64 + 48) kb idx maxP len live F hF (by omega) hkb
      (roomFor_ofK 64 (by decide) hroom (lenIn_zero len hroom.1) (by omega)))
      using [Hg L48 Kk Ha Hvt Hinv] with (rw [hK847]; mstep_norm_full; omega)
  · iunfold StrRepeat.pre847
    ihave L48 := stk_addr (show s.toNat - 112 = (s - 64).toNat - 48 by rw [h64]; omega) $$ L48
    iframe Hg L48 Kk Ha Hvt Hinv
    ipureintro; rfl
  rw [hK847]
  iunfold StrRepeat.post847 at HQ
  icases HQ with ⟨%hrs, Hg, L48, Ha, Hvt, %pk, %⟨hpk0, hpkb⟩, K0, K4, K8, Wk, Hgr⟩
  subst hrs
  iunfold grown at Hgr
  icases Hgr with ⟨%l1, %hl1, Hinv⟩
  have hL1 : LenIn len 1 l1 := lenIn_step 64 (by decide) (lenIn_zero len hroom.1) hl1
  -- 401: accounts.insert(&key, &0)
  have hkey : ([97] ++ (bytes32 64 ++ List.replicate 64 97) : List UInt8) = mKey := rfl
  have hval : (List.replicate 8 0 ++ List.replicate 8 0 : List UInt8) = mVal := rfl
  have hkey2 : (97 :: (bytes32 64 ++ List.replicate 64 97) : List UInt8) = mKey := rfl
  have hK401' : cost401 cfg F 1 64 h (97 :: (bytes32 64 ++ List.replicate 64 97)) = K401 := hK401
  ihave KK := KeyGet.join64 n ((s - 64 + 48).toNat + 4) 64 64 $$ [K4 K8]
  · ihave K8 := memBytes_addr (show (s - 64 + 48).toNat + 8 = (s - 64 + 48).toNat + 4 + 4 by omega) $$ K8
    iframe K4 K8
  ihave KK := BorshFT.joinB (n := n) (a := (s - 64 + 48).toNat) (b := (s - 64 + 48).toNat + 4) (bytes32 pk)
    (bytes32 64 ++ bytes32 64) (by simp [bytes32]) $$ [K0 KK]
  · iframe K0 KK
  ihave Hz := U128From.memBytes_split n 1052800 8 (List.replicate 16 0) (by simp) $$ Hz
  icases Hz with ⟨Z0, Z8⟩
  rw [show (List.replicate 16 (0 : UInt8)).take 8 = List.replicate 8 0 from rfl,
    show (List.replicate 16 (0 : UInt8)).drop 8 = List.replicate 8 0 from rfl]
  ihave Ii := memBytes_addr (show s.toNat - 40 = (s - 64 + 24).toNat by simp [UInt32.toNat_add, h64]; omega) $$ Ii
  ihave L48 := stk_addr (show (s - 64).toNat - 48 = s.toNat - 352 + 240 by rw [h64]; omega) $$ L48
  ihave Lo := stk_join n (s.toNat - 352) 240 48 $$ [Lo L48]
  · iframe Lo L48
  icases stk_split n (s.toNat - 352) 16 272 $$ Lo with ⟨Lo16, Lo⟩
  ihave Lo := stk_addr (show s.toNat - 352 + 16 = (s - 64).toNat - 272 by rw [h64]; omega) $$ Lo
  have hpre1 : ([97] : List UInt8).length = (1 : UInt32).toNat := rfl
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapOps.f401_none cfg lim (d + 1) types[45]! rfl inst mi e A n g ta mx hm (by omega) Cg gt (s - 64)
      (s - 64 + 24) (c + 24) pp pc 1 (s - 64 + 48) pk 64 64 1052800 idx maxP l1 ((pk.toNat, 64) :: live) F hF
      [97] (List.replicate 64 97) (List.replicate 8 0) (List.replicate 8 0) ib (by rw [h64]; omega)
      (by rw [h64]; omega) hib (by simp [UInt32.toNat_add, h64]; omega) hpre1 (by simp) (by simp) (by simp)
      (by decide) (by decide) (by decide) (by simpa using hpp) (by simp [UInt32.toNat_add, h64]; omega) (by simp; omega)
      (by decide) (heapRoom_shift hroom hL1 (by omega))
      h st hview hacc (by rw [hkey, mKey_length]; exact hlim) (by rw [hval, mVal_length]; exact hvlim)
      hcanon.1 hcanon.2 (by rw [hkey]; exact hlink mKey) hproof (by rw [hkey, hnone]; omega) (by rw [hkey]; exact hnone))
      using [Hg Lo HI HW Hvt Hinv Hm Hp KK Wk Z0 Z8 Ii Hhost] with (rw [hK401']; mstep_norm_full; omega)
  · iunfold pre401
    ihave Z0 := memBytes_addr (show 1052800 = (1052800 : UInt32).toNat from rfl) $$ Z0
    ihave Z8 := memBytes_addr (show 1052800 + 8 = (1052800 : UInt32).toNat + 8 from rfl) $$ Z8
    iframe Hg Lo HI HW Hvt Hinv Hm Hp KK Wk Z0 Z8 Ii Hhost
    ipureintro; rfl
  rw [hK401']
  iunfold post401 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, HW, Hvt, ⟨%l2, %hl2, Hinv⟩, Hm, Hp, KK, Wk, Z0, Z8, Ii, ⟨%h1, %hq1, Hhost⟩⟩
  subst hrs
  have hq1' : StorageWritePost e h mKey mVal evictedRegister st h1 := hq1
  clear hq1
  obtain ⟨s2, hacc1, hcan1, hlink1, hpb1, he1⟩ :=
    StorageWritePost.next hq1' hcanon hlink hproof (by rw [hnone]; omega)
  obtain ⟨hcfg1, hfees1, hext1, hview1, hcur1, hus1, hsto1⟩ := post_fields he1
  have hK := hK2 h1 s2 he1
  have hA : h1.context.storageUsage = UInt64.ofNat (h.context.storageUsage.toNat + (85 + e)) := by
    rw [hus1, hnone]; simp only [writeUsage, mKey_length, mVal_length]; congr 1; omega
  obtain ⟨hsub, hngt⟩ := usage_sub h.context.storageUsage (85 + e) hU
  -- after := storage_usage()
  ihave #S528b := EnvGetters.f528_spec_host cfg lim (d + 1) types[19]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 64) (by omega) (by omega) h1 $$ H528
  icases stk_split n ((s - 64).toNat - 272) 256 16 $$ Lo with ⟨Lo, L16⟩
  ihave L16 := stk_addr (show (s - 64).toNat - 272 + 256 = (s - 64).toNat - 16 by rw [h64]; omega) $$ L16
  mstep
  mcall S528b using [Hg HI HU L16 Hhost] with (mstep_norm_full; omega)
  · iunfold pre528
    iframe Hg HI HU L16 Hhost
    ipureintro; rfl
  iunfold post528 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HU, L16, Hhost⟩
  subst hrs
  rw [hA]
  mstep; mstep; mstep; mstep; mstep; mstep
  have hcond : Numeric.bool (Numeric.irelop64 IRelOp.gt_u (UInt64.ofNat (85 + e))
      (UInt64.ofNat (h.context.storageUsage.toNat + (85 + e)))) = 0 := by
    simp only [Numeric.irelop64, Numeric.bool, gt_iff_lt, hngt, decide_false, Bool.false_eq_true, ite_false]
  rw [hsub, hcond]
  mstep
  -- account_storage_usage := 85 + extra
  mstep; mstep; mstep [H16] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  -- 402: accounts.remove(&key)
  have hK' : 250 * cfg.regularOpCost + storageUsageUse h1 + cost402 cfg (F + 3) 1 64 h1
      (97 :: (bytes32 64 ++ List.replicate 64 97)) (List.replicate 8 0 ++ List.replicate 8 0) ≤ K2 := hK
  have hL2 : LenIn len (1 + 3) l2 := lenIn_trans hL1 hl2
  ihave HIR : ifaceR n ta A $$ [HI HRS]
  · iunfold ifaceR; iframe HI HRS
  ihave L16 := stk_addr (show (s - 64).toNat - 16 = s.toNat - 352 + 16 + 256 by rw [h64]; omega) $$ L16
  ihave Lo := stk_addr (show (s - 64).toNat - 272 = s.toNat - 352 + 16 by rw [h64]; omega) $$ Lo
  ihave Lo := stk_join n (s.toNat - 352 + 16) 256 16 $$ [Lo L16]
  · iframe Lo L16
  ihave Lo := stk_join n (s.toNat - 352) 16 (256 + 16) $$ [Lo16 Lo]
  · iframe Lo16 Lo
  ihave Lo := stk_addr (show s.toNat - 352 = (s - 64).toNat - 288 by rw [h64]; omega) $$ Lo
  ihave Rr := memBytes_addr (show s.toNat - 64 = (s - 64).toNat by rw [h64]) $$ Rr
  mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapOps.f402_some cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega) Cg gt (s - 64)
      (s - 64) (c + 24) pp pc 1 (s - 64 + 48) pk 64 64 idx maxP l2 ((pk.toNat, 64) :: live) (F + 3) (by omega)
      [97] (List.replicate 64 97) (List.replicate 8 0) (List.replicate 8 0) rb (by rw [h64]; omega)
      (by rw [h64]; omega) hrb (by rw [h64]; omega) hpre1 (by simp) (by simp) (by simp)
      (by decide) (by decide) (by decide) (by simpa using hpp) (by simp [UInt32.toNat_add, h64]; omega) (by simp; omega)
      (heapRoom_shift hroom hL2 (by omega))
      h1 s2 (by rw [hview1]; exact hview) hacc1 (by rw [hcfg1, hkey, mKey_length]; exact hlim)
      hcan1.1 hcan1.2 (by rw [hkey]; exact hlink1 mKey) hpb1
      (by rw [hkey, hcur1, hsto1, hnone]; omega) (by rw [hcfg1]; exact hreg) (by rw [hkey]; exact hsto1))
      using [Hg Lo HIR HR Hvt Hinv Hm Hp KK Wk Rr Hhost] with (mstep_norm_full; omega)
  · iunfold pre402
    iframe Hg Lo HIR HR Hvt Hinv Hm Hp KK Wk Rr Hhost
    ipureintro; rfl
  iunfold post402 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HIR, HR, Hvt, ⟨%l3, %hl3, Hinv⟩, Hm, Hp, KK, Wk, Rr, ⟨%h2, %hq2, Hhost⟩⟩
  subst hrs
  have hL3 : LenIn len 7 l3 := lenIn_trans hL2 hl3
  -- 321(sp + 48): the key freed
  ihave KK := BorshFT.splitB (n := n) (a := (s - 64 + 48).toNat) (b := (s - 64 + 48).toNat + 4) (bytes32 pk)
    (bytes32 64 ++ bytes32 64) (by simp [bytes32]) $$ KK
  icases KK with ⟨K0, KK⟩
  ihave KK := KeyGet.split64 n ((s - 64 + 48).toNat + 4) 64 64 $$ KK
  icases KK with ⟨K4, K8⟩
  ihave Blk : AllocInv.block n pk.toNat (64 : UInt32).toNat $$ [Wk]
  · iunfold AllocInv.block
    iexists _
    iframe Wk
    ipureintro; simp
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP l3
      ((pk.toNat, 64) :: live) (F + 3 + 3) (s - 64 + 48) pk 64 64
      (by decide) (by simp [UInt32.toNat_add, h64]; omega)) using [K0 K4 K8 Hinv Blk]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 64 + 48).toNat + 4 + 4 = (s - 64 + 48).toNat + 8 by omega) $$ K8
    simp only [UInt32.reduceToNat]
    iframe K0 K4 K8 Hinv Blk
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 64 + 64 = s by simp]
  mstep
  mcredits R
  iframe Hc
  iunfold post404
  isplitr
  · ipureintro; rfl
  iframe Hg HIR HU HW HR Hvt H16 Hm Hp Ha
  isplitl [Lo Rr Ii K0 K4 K8 U60]
  · ihave K8 := BorshFT.stkW (b := s.toNat - 8) _ (by simp [UInt32.toNat_add, h64]; omega) $$ K8
    ihave X := BorshFT.stkJ (a := s.toNat - 8) (b := s.toNat - 4) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [K8 U60]
    · iframe K8 U60
    ihave K4 := BorshFT.stkW (b := s.toNat - 12) _ (by simp [UInt32.toNat_add, h64]; omega) $$ K4
    ihave X := BorshFT.stkJ (a := s.toNat - 12) (b := s.toNat - 8) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [K4 X]
    · iframe K4 X
    ihave K0 := BorshFT.stkW (b := s.toNat - 16) _ (by simp [UInt32.toNat_add, h64]; omega) $$ K0
    ihave X := BorshFT.stkJ (a := s.toNat - 16) (b := s.toNat - 12) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [K0 X]
    · iframe K0 X
    ihave Ii := BorshFT.stkB (b := s.toNat - 40) (k := 24) _ (by simp [UInt32.toNat_add, h64]; omega) (by simp) $$ Ii
    ihave X := BorshFT.stkJ (a := s.toNat - 40) (b := s.toNat - 16) (k1 := 24) (k2 := 16) (k := 40) (by omega) rfl $$ [Ii X]
    · iframe Ii X
    ihave Rr := BorshFT.stkB (b := s.toNat - 64) (k := 24) _ (by rw [h64]) (by rfl) $$ Rr
    ihave X := BorshFT.stkJ (a := s.toNat - 64) (b := s.toNat - 40) (k1 := 24) (k2 := 40) (k := 64) (by omega) rfl $$ [Rr X]
    · iframe Rr X
    ihave Lo := BorshFT.stkA (b := s.toNat - 352) (by rw [h64]; omega) $$ Lo
    iapply BorshFT.stkJ (a := s.toNat - 352) (b := s.toNat - 64) (k1 := 288) (k2 := 64) (k := 352) (by omega) rfl
    iframe Lo X
  isplitl [Hinv]
  · iexists l3
    rw [show F + 3 + 3 + 1 = F + 7 by omega]
    iframe Hinv
    ipureintro; exact hL3
  ihave Z := BorshFT.joinB (n := n) (a := 1052800) (b := 1052808) (List.replicate 8 0) (List.replicate 8 0) rfl $$ [Z0 Z8]
  · iframe Z0 Z8
  ihave Z := (show (n ↦[wms][ 1052800 ] (List.replicate 8 0 ++ List.replicate 8 0) : IProp GF) ⊢ n ↦[wms][ 1052800 ] List.replicate 16 0 from .rfl) $$ Z
  iframe Z
  iexists h2
  iframe Hhost
  ipureintro
  refine ⟨h1, s2, hq1', hacc1, hcan1, hlink1, ?_, he1, hq2⟩
  rw [hnone] at hpb1; exact hpb1

end S404

end WNear.Binary.MeasureUsage
