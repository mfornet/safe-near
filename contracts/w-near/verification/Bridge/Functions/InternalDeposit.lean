import Bridge.Functions.LookupMapInsertSome

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

end WNear.Binary.InternalDeposit
