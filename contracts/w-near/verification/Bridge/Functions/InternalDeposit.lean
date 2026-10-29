import Bridge.Functions.LookupMapInsertSome
import Bridge.Functions.StorageBalanceBounds
import Bridge.Functions.Add128
import Bridge.Functions.MeasureUsage

/-!
# `internal_unwrap_balance_of` (405), `internal_deposit` (406), `internal_register_account` (409)

```wat
;; 405 internal_unwrap_balance_of(out, this, acct): sp -= 96
;;     [sp+36] := acct
;;     399(sp + 8, this + 24, acct)              ;; accounts.get(acct)
;;     None → panic (format! "The account {} is not registered")   (not on this path)
;;     out := [sp+16 .. sp+32)                   ;; the u128
;;     sp += 96
```

* `f405_some`: the account registered with the balance `b0 ++ b1`: the `u128` at `out`.
-/

namespace WNear.Binary.InternalDeposit

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
open WNear.Binary.LookupMapGet (code399 pre399 post399 cost399)

/-! ## `internal_unwrap_balance_of` (405) on a registered account -/

section S405

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 405 (persistent). -/
def code405 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code399 e n maxP inst mi A mx ∗ A 399 ↪[wf] FuncInst.wasm types[31]! inst f399)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code405 (GF := GF) e n maxP inst mi A mx) := by
  unfold code405; infer_instance

/-- The token at `this`: the accounts map's prefix `Vec` at `this + 24`. -/
def pre405 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out this pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 this, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 400) 400 ∗ ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n (this + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post405 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out this pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗ ifaceR n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 3 len'⌝ ∗ heapInv n maxP len' live (F + 3)) ∗
    prefixAt n (this + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] b0 ∗ n ↦[wms][ out.toNat + 8 ] b1 ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

def cost405 (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k b : List UInt8) : Nat :=
  100 * cfg.regularOpCost + cost399 cfg F pl L h k b

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`internal_unwrap_balance_of`** (405) of the `String` `key` at `v`, registered with the
balance `b0 ++ b1`: the `u128` at `out`, the host as `StorageReadPost`. -/
theorem f405_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out this pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key b0 b1 ob : List UInt8)
    (hs : 400 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hthis : this.toNat + 36 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 3 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (b0 ++ b1)) :
    code405 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f405 Cg
        (pre405 n g ta A gt s out this pp pc pl v p c L idx maxP len live F pre key ob h)
        (fun _ => cost405 cfg F pl L h (pre ++ (bytes32 L ++ key)) (b0 ++ b1))
        (post405 n g ta A gt s out this pp pc pl v p c L idx maxP len live F pre key b0 b1
          (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)) := by
  iintro #Hk
  iunfold code405 at Hk
  icases Hk with ⟨#H399c, #F399⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code399, LookupMapGet.code400, DropVec.dropCode at H399c
    icases H399c with ⟨⟨-, ⟨#H, -⟩, -⟩, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha399 := hm.funcs 399 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h96 : (s - 96).toNat = s.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have S399 := LookupMapGet.f399_some (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega)
    Cg gt (s - 96) (s - 96 + 8) (this + 24) pp pc pl v p c L idx maxP len live F hF pre key b0 b1
  unfold cost405
  generalize hK : cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (b0 ++ b1) = K at S399
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre405 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hkey, Ho, Hhost⟩
  subst hargs
  -- the callees' 304, then the frame: [0, 8) [8, 32) the Option [32, 36) [36, 40) acct [40, 96)
  icases stk_split n (s.toNat - 400) 304 96 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 400 + 304 = s.toNat - 96 by omega]
  icases stk_split n (s.toNat - 96) 8 88 $$ Fr with ⟨U0, Fr⟩
  icases stk_split n (s.toNat - 96 + 8) 24 64 $$ Fr with ⟨O, Fr⟩
  icases stk_split n (s.toNat - 96 + 8 + 24) 4 60 $$ Fr with ⟨U32, Fr⟩
  icases stk_split n (s.toNat - 96 + 8 + 24 + 4) 4 56 $$ Fr with ⟨Ac, Fr⟩
  iunfold stk at O Ac
  icases O with ⟨%obb, %hobb, O⟩
  icases Ac with ⟨%ab, %hab, Ac⟩
  ihave O := memBytes_addr (show s.toNat - 96 + 8 = (s - 96 + 8).toNat by simp [UInt32.toNat_add, h96]; omega) $$ O
  ihave Ac := memBytes_addr (show s.toNat - 96 + 8 + 24 + 4 = (s - 96).toNat + 36 by omega) $$ Ac
  simp only [f405]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [Ac] with (simp [hab, storeWidth, NumType.byteWidth])
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (S399 obb (by omega) (by omega) hobb (by simp [UInt32.toNat_add, h96]; omega) hpre hkey hb0 hb1 hL hpl hl0
      hpp hv hp hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome)
      using [Hg Lo HI Hvt Hinv Hm Hp Hv Hkey O Hhost] with (mstep_norm_full; omega)
  · iunfold pre399
    ihave Lo := stk_addr (show s.toNat - 400 = (s - 96).toNat - 304 by omega) $$ Lo
    iframe Hg Lo HI Hvt Hinv Hm Hp Hv Hkey O Hhost
    ipureintro; rfl
  iunfold post399 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, Hinv, Hm, Hp, Hv, Hkey, O, Hhost⟩
  subst hrs
  ihave O := BorshFT.splitB (n := n) (a := (s - 96 + 8).toNat) (b := (s - 96 + 8).toNat + 8)
    (storeBytes (.i64 1) 8) (b0 ++ b1) (by rfl) $$ O
  icases O with ⟨O0, O8⟩
  ihave O8 := BorshFT.splitB (n := n) (a := (s - 96 + 8).toNat + 8) (b := (s - 96 + 8).toNat + 8 + 8) b0 b1
    (by simp [hb0]) $$ O8
  icases O8 with ⟨O8, O16⟩
  ihave O0 := memBytes_addr (show (s - 96 + 8).toNat = (s - 96).toNat + 8 by simp [UInt32.toNat_add, h96]; omega) $$ O0
  ihave O8 := memBytes_addr (show (s - 96 + 8).toNat + 8 = (s - 96).toNat + 16 by simp [UInt32.toNat_add, h96]; omega) $$ O8
  ihave O16 := memBytes_addr (show (s - 96 + 8).toNat + 8 + 8 = (s - 96).toNat + 24 by simp [UInt32.toNat_add, h96]; omega) $$ O16
  have hb0n : b0 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hb1n : b1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Q8⟩
  have hq0 : (ob.take 8).length = 8 := by simp; omega
  have hq8 : (ob.drop 8).length = 8 := by simp; omega
  -- Some: the tag 1
  mstep; mstep; mstep [O0]; mstep
  mstep_taken
  mstep; mstep; mstep; mstep [O16] with (first | (simp [hb1, loadWidth, NumType.byteWidth]) | exact hb1n); mstep
  mstep; mstep; mstep [O8] with (first | (simp [hb0, loadWidth, NumType.byteWidth]) | exact hb0n)
  mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [BorshLeaves.storeBytes_i64_decode _ hb0]
  mstep; mstep; mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [BorshLeaves.storeBytes_i64_decode _ hb1]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 96 + 96 = s by simp]
  mcredits R
  iframe Hc
  iunfold post405
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI Hvt Hinv Hm Hp Hv Hkey Q0 Q8 Hhost
  ihave O0 := BorshFT.stkB (n := n) (b := s.toNat - 88) (k := 8) _ (by omega) (by rfl) $$ O0
  ihave O8 := BorshFT.stkB (n := n) (b := s.toNat - 80) (k := 8) _ (by omega) hb0 $$ O8
  ihave O16 := BorshFT.stkB (n := n) (b := s.toNat - 72) (k := 8) _ (by omega) hb1 $$ O16
  ihave Ac := BorshFT.stkB (n := n) (b := s.toNat - 60) (k := 4) _ (by omega) (by simp [storeWidth, NumType.byteWidth]) $$ Ac
  ihave U0 := BorshFT.stkA (n := n) (k := 8) (b := s.toNat - 96) (by omega) $$ U0
  ihave Lo := BorshFT.stkA (n := n) (k := 304) (b := s.toNat - 400) (by omega) $$ Lo
  ihave U32 := BorshFT.stkA (n := n) (k := 4) (b := s.toNat - 64) (by omega) $$ U32
  ihave Fr := BorshFT.stkA (n := n) (k := 56) (b := s.toNat - 56) (by omega) $$ Fr
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 96) (k1 := 304) (k2 := 8) (k := 312)
    (by omega) (by omega) $$ [Lo U0]
  · iframe Lo U0
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 88) (k1 := 312) (k2 := 8) (k := 320)
    (by omega) (by omega) $$ [S O0]
  · iframe S O0
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 80) (k1 := 320) (k2 := 8) (k := 328)
    (by omega) (by omega) $$ [S O8]
  · iframe S O8
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 72) (k1 := 328) (k2 := 8) (k := 336)
    (by omega) (by omega) $$ [S O16]
  · iframe S O16
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 64) (k1 := 336) (k2 := 4) (k := 340)
    (by omega) (by omega) $$ [S U32]
  · iframe S U32
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 60) (k1 := 340) (k2 := 4) (k := 344)
    (by omega) (by omega) $$ [S Ac]
  · iframe S Ac
  ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 56) (k1 := 344) (k2 := 56) (k := 400)
    (by omega) (by omega) $$ [S Fr]
  · iframe S Fr
  iexact S

end S405

/-! ## `Option::<u128>::expect` (363) on `Some` -/

section S363

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`Option::<u128>::expect`** (363) of `(tag, lo, hi)` with a nonzero tag: `(lo, hi)` at `out`. -/
theorem f363_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out : UInt32) (tag lo hi : UInt64) (loc : UInt32)
    (htag : tag.toUInt32 ≠ 0) (o0 o8 : List UInt8) (ho0 : o0.length = 8) (ho8 : o8.length = 8) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f363 Cg
        (fun args => iprop(⌜args = [.i32 out, .i64 tag, .i64 lo, .i64 hi, .i32 loc]⌝ ∗
          n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 8 ] o8))
        (fun _ => 10 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] storeBytes (.i64 lo) 8 ∗
          n ↦[wms][ out.toNat + 8 ] storeBytes (.i64 hi) 8)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, O0, O8⟩
  subst hargs
  simp only [f363]
  mstep; mstep; mstep
  mstep_taken
  mstep; mstep; mstep [O0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [O8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mcredits R
  iframe Hc O0 O8

end S363

/-! ## `internal_deposit` (406), no overflow -/

set_option maxRecDepth 100000 in
theorem heapRoom_mono {k k' len maxP : Nat} (h : HeapRoomK k len maxP) (hk : k' ≤ k) : HeapRoomK k' len maxP := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _) h3,
    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_succ hk)) _) h4⟩

theorem ld64 (x : UInt64) : UInt64.ofNat (Memory.decodeLE (storeBytes (.i64 x) 8)) = x := by
  rw [U128From.decodeLE_storeBytes_i64]; simp

open Near.TrieOverlay in
/-- What 406 leaves of the host `h` with accounting `st` and budget `bud`: the read of the balance
(`h1`, its accounting `s1` linked and canonical), then the write of the new one. -/
def Post406 (e : Nat) (h : NearState) (k nv : List UInt8) (st : Near.TrieOverlay.State) (bud : Nat)
    (h2 : NearState) : Prop :=
  ∃ (h1 : NearState) (s1 : Near.TrieOverlay.State), StorageReadPost h k 0 st h1 ∧
    h1.storageAccounting = some s1 ∧ Canon s1 ∧ StorageLink h1 s1 ∧
    ProofBudget h1 s1 (bud - readProofCost (contractKey h.context.currentAccountId k) (h.storage k)) ∧
    erase h1 = erase (storageReadRegs { h with storageAccounting := some s1 } 0 (h.storage k)) ∧
    StorageWritePost e h1 k nv StorageWrite.evictedRegister s1 h2

section S406

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.LookupMapInsertSome (code401s pre401s post401s cost401s)
open WNear.Binary.StorageWrite (wslot evictedRegister)

/-- The code of 406 (persistent). -/
def code406 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code405 e n maxP inst mi A mx ∗ code401s e n maxP inst mi A mx ∗
    A 405 ↪[wf] FuncInst.wasm types[31]! inst f405 ∗ A 401 ↪[wf] FuncInst.wasm types[45]! inst f401 ∗
    A 363 ↪[wf] FuncInst.wasm types[49]! inst f363)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code406 (GF := GF) e n maxP inst mi A mx) := by
  unfold code406; infer_instance

/-- The token at `this`: `total_supply` `(t0, t1)` at `this`, the accounts map's prefix `Vec` at
`this + 24`; the account's `String` at `v`. -/
def pre406 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s this pp pc pl v p c L : UInt32)
    (lo hi t0 t1 : UInt64) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (pre key : List UInt8) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 this, .i32 v, .i64 lo, .i64 hi]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 480) 480 ∗ ifaceR n ta A ∗ wslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ n ↦[wms][ this.toNat ] storeBytes (.i64 t0) 8 ∗
    n ↦[wms][ this.toNat + 8 ] storeBytes (.i64 t1) 8 ∗
    prefixAt n (this + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗ mhostPt h)

/-- The new total supply `T + a` at `this`, the heap after at most seven grows with seven more
free cells. -/
def post406 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s this pp pc pl v p c L : UInt32)
    (T a : Nat) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (pre key : List UInt8) (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 480) 480 ∗ ifaceR n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 7 len'⌝ ∗ heapInv n maxP len' live (F + 7)) ∗
    n ↦[wms][ this.toNat ] StorageBalanceBounds.u128Of (T + a) ∗
    prefixAt n (this + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- **`FungibleToken::internal_deposit`** (406) of `a = lo + 2^64 hi` to the registered `String`
`key` at `v` (balance `B = x0 + 2^64 x1`), with no overflow of the balance or the total supply
`T = t0 + 2^64 t1`: the balance `B + a` written back (the host as `Post406`), the total supply
`T + a`. -/
theorem f406_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s this pp pc pl v p c L : UInt32) (lo hi t0 t1 x0 x1 : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key : List UInt8)
    (hs : 480 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hthis : this.toNat + 36 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 7 len maxP)
    (hno1 : x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128)
    (hno2 : t0.toNat + 2 ^ 64 * t1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128)
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
    (K401 : Nat) (hK401 : ∀ h1 s1, erase h1 = erase (storageReadRegs { h with storageAccounting := some s1 } 0
      (h.storage (pre ++ (bytes32 L ++ key)))) →
      cost401s cfg (F + 3) pl L h1 (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) ≤ K401) :
    code406 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f406 Cg
        (pre406 n g ta A gt s this pp pc pl v p c L lo hi t0 t1 idx maxP len live F pre key h)
        (fun _ => 300 * cfg.regularOpCost + cost405 cfg F pl L h (pre ++ (bytes32 L ++ key))
          (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) + K401)
        (post406 n g ta A gt s this pp pc pl v p c L (t0.toNat + 2 ^ 64 * t1.toNat) (lo.toNat + 2 ^ 64 * hi.toNat)
          idx maxP len live F pre key
          (Post406 e h (pre ++ (bytes32 L ++ key))
            (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + (lo.toNat + 2 ^ 64 * hi.toNat))) st bud)) := by
  iintro #Hk
  iunfold code406 at Hk
  icases Hk with ⟨#H405c, #H401c, #F405, #F401, #F363⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code405, code399, LookupMapGet.code400, DropVec.dropCode at H405c
    icases H405c with ⟨⟨⟨-, ⟨#H, -⟩, -⟩, -⟩, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha405 := hm.funcs 405 (by decide)
  have ha401 := hm.funcs 401 (by decide)
  have ha363 := hm.funcs 363 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have t49 : types[49]!.params.length = 5 := by rfl
  have hlt := s.toNat_lt
  have h80 : (s - 80).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have S405 := f405_some (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega)
    Cg gt (s - 80) (s - 80 + 48) this pp pc pl v p c L idx maxP len live F hF pre key
    (storeBytes (.i64 x0) 8) (storeBytes (.i64 x1) 8)
  generalize hK405 : cost405 cfg F pl L h (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) = K405
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre406 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Ht0, Ht8, Hm, Hp, Hv, Hkey, Hhost⟩
  subst hargs
  -- the callees' 400, then the frame: [0, 8) [8, 24) T [24, 48) I [48, 64) B [64, 80) N
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
  have hsome' : h.storage (pre ++ (bytes32 L ++ key)) = some (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) := hsome
  mcall (S405 bb (by omega) (by omega) hbb (by simp [UInt32.toNat_add, h80]; omega) (by omega) hpre hkey
      (by simp) (by simp) hL hpl hl0 hpp hv hp (heapRoom_mono hroom (by omega)) h st hacc hlim hcanon.1 hcanon.2 (hlink _) hproof
      (by unfold readProofCost writeProofCost at hbud; omega) hreg hsome')
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
  have hb64 : (s - 80 + 64).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h80]; omega
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
  have hK1 := hK401 h1 s1 he1
  generalize cost401s cfg (F + 3) pl L h1 (pre ++ (bytes32 L ++ key)) (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8) = K1
    at S401 hK1
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
  rw [← apply_ite Value.i32, Add128.add128_flag t0 t1 lo hi, if_pos hno2]
  mstep; mstep; mstep
  -- 363: expect the new total supply at sp + 8
  ihave T := U128From.memBytes_split n (s.toNat - 80 + 8) 8 tb (by omega) $$ T
  icases T with ⟨T0, T8⟩
  have ht0 : (tb.take 8).length = 8 := by simp; omega
  have ht8 : (tb.drop 8).length = 8 := by simp; omega
  ihave T0 := memBytes_addr (show s.toNat - 80 + 8 = (s - 80 + 8).toNat by simp [UInt32.toNat_add, h80]; omega) $$ T0
  ihave T8 := memBytes_addr (show s.toNat - 80 + 8 + 8 = (s - 80 + 8).toNat + 8 by simp [UInt32.toNat_add, h80]; omega) $$ T8
  mstep; mstep; mstep
  mcall (f363_some cfg lim (d + 1) types[49]! rfl inst mi n hn Cg (s - 80 + 8) ((0 : UInt32) ^^^ 1).toUInt64 (t0 + lo)
      (t1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (t0 + lo) t0)).toUInt64) 1053040 (by decide)
      (tb.take 8) (tb.drop 8) ht0 ht8) using [T0 T8]
  · iframe T0 T8
  icases HQ with ⟨%hrs, T0, T8⟩
  subst hrs
  ihave T0 := memBytes_addr (show (s - 80 + 8).toNat = (s - 80).toNat + 8 by simp [UInt32.toNat_add, h80]; omega) $$ T0
  ihave T8 := memBytes_addr (show (s - 80 + 8).toNat + 8 = (s - 80 + 8 + 8).toNat by simp [UInt32.toNat_add, h80]; omega) $$ T8
  mstep; mstep [T0]
  rw [ld64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [T8]
  rw [ld64]
  mstep [Ht8] with (first | exact List.ne_nil_of_length_pos (by simp) | (simp [storeWidth, NumType.byteWidth]) | rfl)
  mstep; mstep; mstep [Ht0] with (first | exact List.ne_nil_of_length_pos (by simp) | (simp [storeWidth, NumType.byteWidth]) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 80 + 80 = s by simp]
  mcredits R
  iframe Hc
  have hTs : StorageBalanceBounds.u128Of (t0.toNat + 18446744073709551616 * t1.toNat +
      (lo.toNat + 18446744073709551616 * hi.toNat)) =
      storeBytes (.i64 (t0 + lo)) 8 ++
        storeBytes (.i64 (t1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (t0 + lo) t0)).toUInt64)) 8 := by
    refine (StorageBalanceBounds.u128Bytes_eq_u128Of _ _ _ ?_).symm
    have := Add128.add128_words t0 t1 lo hi
    omega
  have hBs : StorageBalanceBounds.u128Of (x0.toNat + 18446744073709551616 * x1.toNat +
      (lo.toNat + 18446744073709551616 * hi.toNat)) =
      storeBytes (.i64 (x0 + lo)) 8 ++
        storeBytes (.i64 (x1 + hi + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + lo) x0)).toUInt64)) 8 := by
    refine (StorageBalanceBounds.u128Bytes_eq_u128Of _ _ _ ?_).symm
    have := Add128.add128_words x0 x1 lo hi
    omega
  iunfold post406
  rw [hTs, hBs]
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI HW Hvt Hm Hp Hv Hkey
  isplitl [U0 B0 B8 Lo80 Lo N0 N8 I T0 T8]
  · ihave N8 := BorshFT.stkB (n := n) (b := s.toNat - 8) (k := 8) _ (by simp [UInt32.toNat_add, h80]; omega) (by simp) $$ N8
    ihave N0 := BorshFT.stkB (n := n) (b := s.toNat - 16) (k := 8) _ (by omega) (by simp) $$ N0
    ihave B8 := BorshFT.stkB (n := n) (b := s.toNat - 24) (k := 8) _ (by simp [UInt32.toNat_add, h80]; omega) (by simp) $$ B8
    ihave B0 := BorshFT.stkB (n := n) (b := s.toNat - 32) (k := 8) _ (by simp [UInt32.toNat_add, h80]; omega) (by simp) $$ B0
    ihave I := BorshFT.stkB (n := n) (b := s.toNat - 56) (k := 24) _ (by simp [UInt32.toNat_add, h80]; omega) (by simp) $$ I
    ihave T8 := BorshFT.stkB (n := n) (b := s.toNat - 64) (k := 8) _ (by simp [UInt32.toNat_add, h80]; omega) (by simp) $$ T8
    ihave T0 := BorshFT.stkB (n := n) (b := s.toNat - 72) (k := 8) _ (by omega) (by simp) $$ T0
    ihave U0 := BorshFT.stkA (n := n) (k := 8) (b := s.toNat - 80) (by omega) $$ U0
    ihave Lo := BorshFT.stkA (n := n) (k := 320) (b := s.toNat - 400) (by omega) $$ Lo
    ihave Lo80 := BorshFT.stkA (n := n) (k := 80) (b := s.toNat - 480) (by omega) $$ Lo80
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 16) (b := s.toNat - 8) (k1 := 8) (k2 := 8) (k := 16)
      (by omega) rfl $$ [N0 N8]
    · iframe N0 N8
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 24) (b := s.toNat - 16) (k1 := 8) (k2 := 16) (k := 24)
      (by omega) rfl $$ [B8 X]
    · iframe B8 X
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 32) (b := s.toNat - 24) (k1 := 8) (k2 := 24) (k := 32)
      (by omega) rfl $$ [B0 X]
    · iframe B0 X
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 56) (b := s.toNat - 32) (k1 := 24) (k2 := 32) (k := 56)
      (by omega) rfl $$ [I X]
    · iframe I X
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 64) (b := s.toNat - 56) (k1 := 8) (k2 := 56) (k := 64)
      (by omega) rfl $$ [T8 X]
    · iframe T8 X
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 72) (b := s.toNat - 64) (k1 := 8) (k2 := 64) (k := 72)
      (by omega) rfl $$ [T0 X]
    · iframe T0 X
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 80) (b := s.toNat - 72) (k1 := 8) (k2 := 72) (k := 80)
      (by omega) rfl $$ [U0 X]
    · iframe U0 X
    ihave X := BorshFT.stkJ (n := n) (a := s.toNat - 400) (b := s.toNat - 80) (k1 := 320) (k2 := 80) (k := 400)
      (by omega) rfl $$ [Lo X]
    · iframe Lo X
    iapply BorshFT.stkJ (n := n) (a := s.toNat - 480) (b := s.toNat - 400) (k1 := 80) (k2 := 400) (k := 480)
      (by omega) rfl
    iframe Lo80 X
  isplitl [Hinv]
  · iexists l2
    rw [show F + 3 + 4 = F + 7 by omega]
    iframe Hinv
    ipureintro; exact MeasureUsage.lenIn_trans hl1 hl2
  isplitl [Ht0 Ht8]
  · iapply BorshFT.joinB (n := n) (a := this.toNat) (b := this.toNat + 8) _ _ (by simp)
    iframe Ht0 Ht8
  iexists h2
  iframe Hhost
  ipureintro
  exact ⟨h1, s1, hq1, hacc1, hcan1, hlink1, hp1, he1, hq2⟩

end S406

end WNear.Binary.InternalDeposit
