import Bridge.Functions.LookupMapContains
import Bridge.Functions.StorageReadWrapF

/-!
# `LookupMap<String, u128>::get` (399) and `get_raw` (400), on a key present

```wat
;; 400 get_raw(out, map, kp, kl): sp -= 32
;;     392(sp + 16, map, kp, kl)                   ;; the storage key pre ++ key, a fresh Vec
;;     779(sp + 8, sp + 16)                        ;; (ptr, len)
;;     548(out, ptr, len)                          ;; env::storage_read: Some(vec)
;;     321(sp + 16)                                ;; the key freed
;;     sp += 32
```

* `f400_some`: `get_raw(key)` of a key present with `v`: `Some(vec)` at `out`, `vec` a fresh block
  holding `v`; the host as `StorageReadPost`; the key's buffer freed.
-/

namespace WNear.Binary.LookupMapGet

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (code392 prefixAt pre392 post392 cost510)
open WNear.Binary.LookupMapBorsh (code395 pre395 post395 cost395 code398 pre398 post398)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step lenIn_zero lenIn_mono)
open WNear.Binary.ReadRegister (ifaceR RegOk)
open WNear.Binary.ReadRegisterF (optVecAtF)
open WNear.Binary.StorageReadWrapF (srCodeF pre548F post548F costSF)
open WNear.Binary.StateWrite (stkJ stkL memBytes_disjoint)

/-! ## `get_raw` (400) -/

section S400

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 400 (persistent). -/
def code400 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code392 n maxP inst mi A ∗ dropCode inst mi A ∗ srCodeF e inst mi A n maxP mx ∗
    A 392 ↪[wf] FuncInst.wasm types[45]! inst f392 ∗ A 548 ↪[wf] FuncInst.wasm types[31]! inst f548 ∗
    A 321 ↪[wf] FuncInst.wasm types[0]! inst f321)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code400 (GF := GF) e n maxP inst mi A mx) := by
  unfold code400; infer_instance

def pre400 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 224) 224 ∗ ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

/-- `Some(vec)` at `out`: `vec = (p, |v|, |v|)`, `p ↦ v` a fresh live block; the key's block freed. -/
def post400 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key v : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 224) 224 ∗ ifaceR n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ kp.toNat ] key ∗
    (∃ p : UInt32, ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] UInt32.ofNat v.length ∗
      n ↦[i32][ out.toNat + 8 ] UInt32.ofNat v.length ∗ n ↦[wms][ p.toNat ] v ∗
      ∃ len1 len2, ⌜(len1 = len ∨ len1 = grownLen len (pl + kl)) ∧
          (len2 = len1 ∨ len2 = grownLen len1 (UInt32.ofNat v.length))⌝ ∗
        heapInv n maxP len2 ((p.toNat, v.length) :: live) (F + 1)) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 400, activation excluded. -/
def cost400 (cfg : WasmConfig) (F : Nat) (pl kl : UInt32) (h : NearState) (k v : List UInt8) : Nat :=
  800 * cfg.regularOpCost + cost510 cfg F pl kl + storageReadUse h k (pl + kl).toNat + costSF cfg F h v

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`LookupMap::get_raw`** (400) of the key `pre ++ key`, present in storage with `v`: `Some(vec)`
at `out` with `vec` holding `v`; the host as `StorageReadPost`; the key's buffer freed. -/
theorem f400_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl kp kl : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key ob v : List UInt8)
    (hs : 224 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = kl.toNat)
    (hl : pl.toNat + kl.toNat ≤ 4096) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hkp : kp.toNat + kl.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (pl + kl))
    (hv0 : 0 < v.length) (hv28 : v.length < 2 ^ 28)
    (hr2 : ∀ l, l = len ∨ l = grownLen len (pl + kl) → roomFor l maxP (UInt32.ofNat v.length))
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ key).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ key) = viewVal st (contractKey h.context.currentAccountId (pre ++ key)))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ key)) (h.storage (pre ++ key)) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen v.length = true)
    (hsome : h.storage (pre ++ key) = some v) :
    code400 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f400 Cg
        (pre400 n g ta A gt s out m pp pc pl kp kl idx maxP len live F pre key ob h)
        (fun _ => cost400 cfg F pl kl h (pre ++ key) v)
        (post400 n g ta A gt s out m pp pc pl kp kl idx maxP len live F pre key v
          (StorageReadPost h (pre ++ key) 0 st)) := by
  iintro #Hk
  iunfold code400 at Hk
  icases Hk with ⟨#H392c, #Hdrop, #Hsr, #F392, #F548, #F321⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code392 at H392c; icases H392c with ⟨-, -, #H⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha392 := hm.funcs 392 (by decide)
  have ha548 := hm.funcs 548 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hT : (pl + kl).toNat = pl.toNat + kl.toNat := by rw [UInt32.toNat_add]; omega
  have hkl : (pre ++ key).length = (pl + kl).toNat := by simp [hpre, hkey, hT]
  have S548 := fun (q : UInt32) (l1 : Nat) (live1 : List (Nat × Nat)) (ob1 : List UInt8) (hob1 : ob1.length = 12)
      (hok : RegOk maxP l1 (some v)) =>
    StorageReadWrapF.f548_someF_host (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega)
      Cg gt (s - 32) out q (pl + kl) (by omega) (by omega) hout (pre ++ key) idx maxP l1 live1 F hF ob1 hob1 h st
      hkl (by omega) hacc hlim hb hz hlink hproof hbud v hsome hreg hok
  clear hacc hlim hb hz hlink hproof hbud
  unfold cost400
  generalize hK510 : cost510 cfg F pl kl = K510
  generalize hKr : storageReadUse h (pre ++ key) (pl + kl).toNat = Kr at S548
  generalize hKS : costSF cfg F h v = KS at S548
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre400 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hkey, Ho, Hhost⟩
  subst hargs
  -- the callees' 192, then the frame: [0, 8) [8, 16) the slice [16, 28) the Vec [28, 32)
  icases stk_split n (s.toNat - 224) 192 32 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 224 + 192 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 8 24 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 32 + 8) 8 16 $$ Fr with ⟨D, Fr⟩
  icases stk_split n (s.toNat - 32 + 8 + 8) 12 4 $$ Fr with ⟨V, U⟩
  iunfold stk at V D
  icases V with ⟨%vb, %hvb, V⟩
  icases D with ⟨%db, %hdb, D⟩
  ihave V := memBytes_addr (show s.toNat - 32 + 8 + 8 = (s - 32 + 16).toNat by simp [UInt32.toNat_add, h32]; omega) $$ V
  ihave D := memBytes_addr (show s.toNat - 32 + 8 = (s - 32 + 8).toNat by simp [UInt32.toNat_add, h32]; omega) $$ D
  icases stk_split n (s.toNat - 224) 80 112 $$ Lo with ⟨Lo80, Lo⟩
  simp only [f400]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 392: the storage key
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapLeaves.f392_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 16) m pp pc pl kp kl idx maxP len live F hF pre key vb (by omega) hvb hpre hkey (by omega)
      (by omega) (by simp [UInt32.toNat_add, h32]; omega) hpp hkp hr)
      using [Hg Lo Hvt Hinv Hm Hp Hkey V] with (rw [hK510]; mstep_norm_full; omega)
  · iunfold pre392
    ihave Lo := stk_addr (show s.toNat - 224 + 80 = (s - 32).toNat - 112 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hm Hp Hkey V
    ipureintro; rfl
  rw [hK510]
  iunfold post392 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hm, Hp, Hkey, %q, %⟨hq0, hqb⟩, Hgr, V0, V4, V8, Hk⟩
  subst hrs
  -- 779: (q, pl + kl)
  ihave VV := KeyGet.join64 n (s - 32 + 16).toNat q (pl + kl) $$ [V0 V4]
  · iframe V0 V4
  ihave VV := BorshFT.joinB (n := n) (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 8)
    (bytes32 q ++ bytes32 (pl + kl)) (bytes32 (pl + kl)) (by simp [bytes32]) $$ [VV V8]
  · iframe VV V8
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 32 + 8) (s - 32 + 16) db
      (bytes32 q ++ bytes32 (pl + kl) ++ bytes32 (pl + kl)) hdb (by simp [bytes32])) using [D VV]
  · iunfold VecDeref.pre
    iframe D VV
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D, VV⟩
  subst hrs
  have hpl : (bytes32 q ++ (bytes32 (pl + kl) ++ bytes32 (pl + kl))).take 4 ++
      (bytes32 q ++ (bytes32 (pl + kl) ++ bytes32 (pl + kl))).drop 8 = bytes32 q ++ bytes32 (pl + kl) := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 q), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl]; clear hpl
  ihave D := KeyGet.split64 n (s - 32 + 8).toNat q (pl + kl) $$ D
  icases D with ⟨D0, D4⟩
  ihave D0 := memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by simp [UInt32.toNat_add, h32]; omega) $$ D0
  ihave D4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 12 by simp [UInt32.toNat_add, h32]; omega) $$ D4
  -- 548: storage_read
  iunfold grown at Hgr
  icases Hgr with ⟨%hl', %hhl, Hinv⟩
  ihave #S := S548 q hl' ((q.toNat, (pl + kl).toNat) :: live) ob hob ⟨hv0, hv28, hr2 _ hhl⟩ $$ Hsr
  ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 224 + 80 by omega) $$ Lo
  ihave Lo := stkJ (n := n) (show s.toNat - 224 + 80 = s.toNat - 224 + 80 by rfl) $$ [Lo80 Lo]
  · iframe Lo80 Lo
  ihave Lo := stk_addr (show s.toNat - 224 = (s - 32).toNat - 192 by omega) $$ Lo
  mstep; mstep; mstep [D0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D4] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall S using [Hg HI Lo Hvt Hinv Ho Hk Hhost] with (mstep_norm_full; omega)
  · iunfold pre548F
    iframe Hg HI Lo Hvt Hinv Ho Hk Hhost
    ipureintro; rfl
  iunfold post548F at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, Hvt, Hk, HV, Hhost⟩
  subst hrs
  iunfold optVecAtF at HV
  icases HV with ⟨%p, P0, P4, P8, %len2, %⟨hp0, hlen2⟩, Hinv, Pv⟩
  -- 321: the key freed
  icases memBytes_disjoint n p.toNat q.toNat v (pre ++ key)
    (by intro h0; rw [h0] at hv0; simp at hv0)
    (by intro h0; have := congrArg List.length h0; rw [hkl] at this; simp at this; omega) $$ [Pv Hk]
    with ⟨%hdj, Pv, Hk⟩
  · iframe Pv Hk
  have hpq : (p.toNat, v.length) ≠ (q.toNat, (pl + kl).toNat) := by
    intro h0; simp at h0; omega
  ihave VV := BorshFT.splitB (n := n) (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 4) (bytes32 q)
    (bytes32 (pl + kl) ++ bytes32 (pl + kl)) (by simp [bytes32]) $$ VV
  icases VV with ⟨K0, VV⟩
  ihave VV := KeyGet.split64 n ((s - 32 + 16).toNat + 4) (pl + kl) (pl + kl) $$ VV
  icases VV with ⟨K4, K8⟩
  ihave Blk : AllocInv.block n q.toNat (pl + kl).toNat $$ [Hk]
  · iunfold AllocInv.block
    iexists _
    iframe Hk
    ipureintro; exact hkl
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len2
      ((p.toNat, v.length) :: (q.toNat, (pl + kl).toNat) :: live) F (s - 32 + 16) q (pl + kl) (pl + kl)
      (by intro h0; have := congrArg UInt32.toNat h0; rw [hT] at this; simp at this; omega)
      (by simp [UInt32.toNat_add, h32]; omega)) using [K0 K4 K8 Hinv Blk]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 32 + 16).toNat + 4 + 4 = (s - 32 + 16).toNat + 8 by omega) $$ K8
    iframe K0 K4 K8 Hinv Blk
    ipureintro; exact ⟨rfl, by simp⟩
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  rw [List.erase_cons_tail (by simpa using hpq), List.erase_cons_head] at *
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post400
  isplitr
  · ipureintro; rfl
  iframe Hg HI Hvt Hm Hp Hkey
  isplitl [F0 U D0 D4 Lo K0 K4 K8]
  · ihave K0 := BorshFT.stkW (n := n) (b := s.toNat - 16) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K0
    ihave K4 := BorshFT.stkW (n := n) (b := s.toNat - 12) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K4
    ihave K8 := BorshFT.stkW (n := n) (b := s.toNat - 8) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K8
    ihave D0 := BorshFT.stkW (n := n) (b := s.toNat - 24) _ (by omega) $$ D0
    ihave D4 := BorshFT.stkW (n := n) (b := s.toNat - 20) _ (by omega) $$ D4
    ihave U := BorshFT.stkA (n := n) (k := 4) (b := s.toNat - 4) (by omega) $$ U
    ihave F0 := BorshFT.stkA (n := n) (k := 8) (b := s.toNat - 32) (by omega) $$ F0
    ihave Lo := BorshFT.stkA (n := n) (k := 192) (b := s.toNat - 224) (by omega) $$ Lo
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 32) (k1 := 192) (k2 := 8) (k := 200)
      (by omega) (by omega) $$ [Lo F0]
    · iframe Lo F0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 24) (k1 := 200) (k2 := 4) (k := 204)
      (by omega) (by omega) $$ [S D0]
    · iframe S D0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 20) (k1 := 204) (k2 := 4) (k := 208)
      (by omega) (by omega) $$ [S D4]
    · iframe S D4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 16) (k1 := 208) (k2 := 4) (k := 212)
      (by omega) (by omega) $$ [S K0]
    · iframe S K0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 12) (k1 := 212) (k2 := 4) (k := 216)
      (by omega) (by omega) $$ [S K4]
    · iframe S K4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 8) (k1 := 216) (k2 := 4) (k := 220)
      (by omega) (by omega) $$ [S K8]
    · iframe S K8
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 224) (b := s.toNat - 4) (k1 := 220) (k2 := 4) (k := 224)
      (by omega) (by omega) $$ [S U]
    · iframe S U
    iexact S
  isplitr [Hhost]
  · iexists p
    iframe P0 P4 P8 Pv
    isplitr
    · ipureintro; exact hp0
    iexists hl', len2
    iframe Hinv
    ipureintro; exact ⟨hhl, hlen2⟩
  iexact Hhost

end S400

section S399

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.ReadRegister (ifaceR)

/-- The code of 399 (persistent). -/
def code399 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code400 e n maxP inst mi A mx ∗ code395 n maxP inst mi A ∗ code398 inst mi A ∗
    A 395 ↪[wf] FuncInst.wasm types[14]! inst f395 ∗ A 400 ↪[wf] FuncInst.wasm types[45]! inst f400 ∗
    A 398 ↪[wf] FuncInst.wasm types[31]! inst f398)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code399 (GF := GF) e n maxP inst mi A mx) := by
  unfold code399; infer_instance

def pre399 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 304) 304 ∗ ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

/-- `Some(u128)` at `out`: the word 1 (`i64`), then the 16 bytes `b0 ++ b1` read back. -/
def post399 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗ ifaceR n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 3 len'⌝ ∗ heapInv n maxP len' live (F + 3)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] (storeBytes (.i64 1) 8 ++ (b0 ++ b1)) ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 399, activation excluded. -/
def cost399 (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k b : List UInt8) : Nat :=
  3000 * cfg.regularOpCost + cost395 cfg F L + cost510 cfg F pl (0 + 4 + L) +
    storageReadUse h k (pl + (0 + 4 + L)).toNat + StorageReadWrapF.costSF cfg F h b

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- **`LookupMap::get`** (399) of the `String` `key` at `v`, present in storage with the `u128`
`b0 ++ b1`: `Some(u128)` at `out`, the host as `StorageReadPost`, both buffers freed. -/
theorem f399_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key b0 b1 ob : List UInt8)
    (hs : 304 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 24) (hout : out.toNat + 24 ≤ 2 ^ 32)
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
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (b0 ++ b1)) :
    code399 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f399 Cg
        (pre399 n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key ob h)
        (fun _ => cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (b0 ++ b1))
        (post399 n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key b0 b1
          (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)) := by
  iintro #Hk
  iunfold code399 at Hk
  icases Hk with ⟨#H400c, #H395c, #H398c, #F395, #F400, #F398⟩
  ihave #Hdrop : dropCode inst mi A $$ []
  · iunfold code400 at H400c; icases H400c with ⟨-, #H, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code400, code392 at H400c; icases H400c with ⟨⟨-, -, #H⟩, -⟩; iexact H
  ihave #F321 : A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 $$ []
  · iunfold code400 at H400c; icases H400c with ⟨-, -, -, -, -, #H⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha395 := hm.funcs 395 (by decide)
  have ha400 := hm.funcs 400 (by decide)
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
  unfold cost399
  generalize hK395 : cost395 cfg F L = K395
  generalize hKr : storageReadUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  generalize hK510 : cost510 cfg F pl (0 + 4 + L) = K510
  generalize hK523 : StorageReadWrapF.costSF cfg F h (b0 ++ b1) = K523
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre399 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hkey, Ho, Hhost⟩
  subst hargs
  -- the callees' 224, then the frame
  icases stk_split n (s.toNat - 304) 224 80 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 304 + 224 = s.toNat - 80 by omega]
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
  icases stk_split n (s.toNat - 304) 96 128 $$ Lo with ⟨Lo80, Lo⟩
  rw [show s.toNat - 304 + 96 = s.toNat - 208 by omega]
  simp only [f399]
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
  -- 400: get_raw
  iunfold grown at Hgr1
  icases Hgr1 with ⟨%l1, %hl1, Hinv⟩
  have hL1 : LenIn len 1 l1 := lenIn_step 1024 (by decide) (lenIn_zero len hroom.1) hl1
  ihave O := memBytes_addr (show s.toNat - 48 = (s - 80 + 32).toNat by simp [UInt32.toNat_add, h80]; omega) $$ O
  ihave Lo := stk_addr (show (s - 80).toNat - 128 = s.toNat - 208 by omega) $$ Lo
  ihave Lo := stkJ (n := n) (show s.toNat - 208 = s.toNat - 304 + 96 by omega) $$ [Lo80 Lo]
  · iframe Lo80 Lo
  ihave Lo := stk_addr (show s.toNat - 304 = (s - 80).toNat - 224 by omega) $$ Lo
  mstep; mstep; mstep; mstep
  mstep; mstep [D10] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D14] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall (LookupMapGet.f400_some cfg lim (d + 1) types[45]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 80) (s - 80 + 32) m pp pc pl q1 (0 + 4 + L) idx maxP l1
      ((q1.toNat, 1024) :: live) F hF pre (bytes32 L ++ key) obb (b0 ++ b1)
      (by omega) (by rw [h80]; omega) hobb (by simp [UInt32.toNat_add, h80]; omega) hpre hKL
      (by rw [hk4]; omega) hl0 hpp (by rw [hk4]; omega)
      (roomFor_ofK _ (by rw [hplk]; omega) hroom hL1 (by omega)) (by rw [hv16]; decide) (by rw [hv16]; decide)
      (fun l hl => roomFor_ofK _ (by rw [hv16]; decide) hroom
        (lenIn_step _ (by rw [hplk]; omega) hL1 hl) (by omega))
      h st hacc hlim hb hz hlink hproof hbud (by rw [hv16]; exact hreg) hsome)
      using [Hg Lo HI Hvt Hinv Hm Hp Wk O Hhost]
      with (simp only [cost400, hKr, hK510, hK523]; mstep_norm_full; omega)
  · iunfold pre400
    iframe Hg Lo HI Hvt Hinv Hm Hp Wk O Hhost
    ipureintro; rfl
  simp only [cost400, hKr, hK510, hK523]
  iunfold post400 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, Hm, Hp, Wk, ⟨%pv, %hpv0, P0, P4, P8, Pv, %len1, %len2, %⟨hlen1, hlen2⟩, Hinv⟩, Hhost⟩
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
  icases stk_split n ((s - 80).toNat - 224) 80 144 $$ Lo with ⟨Lo64, Lo⟩
  ihave Lo := stk_addr (show (s - 80).toNat - 224 + 80 = (s - 80).toNat - 144 by omega) $$ Lo
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
  iunfold post399
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI Hvt Hm Hp Hv Hkey
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
    ihave Lo64 := BorshFT.stkA (b := s.toNat - 304) (by omega) $$ Lo64
    iapply BorshFT.stkJ (a := s.toNat - 304) (b := s.toNat - 224) (k1 := 80) (k2 := 224) (k := 304) (by omega) rfl
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

end S399

end WNear.Binary.LookupMapGet
