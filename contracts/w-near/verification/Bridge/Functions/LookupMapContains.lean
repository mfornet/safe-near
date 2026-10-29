import Bridge.Functions.LookupMapOps
import Bridge.Functions.StorageHasKey

/-!
# `LookupMap<String, u128>::contains_key` (394) and `contains_key_raw` (396)

```wat
;; 396 contains_key_raw(map, kp, kl) -> bool: sp -= 32
;;     392(sp + 16, map, kp, kl)                   ;; the storage key pre ++ key, a fresh Vec
;;     779(sp + 8, sp + 16)                        ;; (ptr, len)
;;     r := 551(ptr, len)                          ;; env::storage_has_key
;;     321(sp + 16)                                ;; the Vec freed
;;     sp += 32; r
;; 394 contains_key(map, k) -> bool: sp -= 32
;;     395(sp + 16, k); 779(sp + 8, sp + 16)       ;; the Borsh key, (ptr, len)
;;     r := 396(map, ptr, len)
;;     321(sp + 16)                                ;; the Borsh key freed
;;     sp += 32; r
```

* `f396_spec`: `contains_key_raw(key)`: whether `pre ++ key` has a value (`foundU64`), the host
  as `StorageHasKeyPost`, the heap after at most one grow with one more free cell.
* `f394_spec`: `contains_key(k)` of the `String` `k`: the same on `pre ++ borsh(k)`, two more free
  cells.
-/

namespace WNear.Binary.LookupMapContains

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
open WNear.Binary.LookupMapBorsh (code395 pre395 post395 cost395)
open WNear.Binary.StorageHasKey (hslot hCode pre551 post551)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step lenIn_zero lenIn_mono)
open WNear.Binary.StateWrite (stkJ stkL)

/-! ## `contains_key_raw` (396) -/

section S396

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 396 (persistent). -/
def code396 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code392 n maxP inst mi A ∗ dropCode inst mi A ∗ ifaceCode e inst mi A n mx ∗ hCode e inst A ∗
    A 436 ↪[wf] FuncInst.wasm types[30]! inst f436 ∗ A 392 ↪[wf] FuncInst.wasm types[45]! inst f392 ∗
    A 551 ↪[wf] FuncInst.wasm types[13]! inst f551 ∗ A 321 ↪[wf] FuncInst.wasm types[0]! inst f321)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code396 (GF := GF) e n maxP inst mi A mx) := by
  unfold code396; infer_instance

def pre396 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s m pp pc pl kp kl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 m, .i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    iface n ta A ∗ hslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ n ↦[wms][ kp.toNat ] key ∗ mhostPt h)

/-- Whether `pre ++ key` has a value, the heap with one more free cell. -/
def post396 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s m pp pc pl kp kl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8)
    (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 v.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    iface n ta A ∗ hslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜len' = len ∨ len' = grownLen len (pl + kl)⌝ ∗ heapInv n maxP len' live (F + 1)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ n ↦[wms][ kp.toNat ] key ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 396, activation excluded. -/
def cost396 (cfg : WasmConfig) (F : Nat) (pl kl : UInt32) (h : NearState) (k : List UInt8) : Nat :=
  800 * cfg.regularOpCost + cost510 cfg F pl kl + storageHasKeyUse h k (pl + kl).toNat

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`LookupMap::contains_key_raw`** (396) of the key `key` at `kp`: whether `pre ++ key` has a
value in storage, the host as `StorageHasKeyPost`. -/
theorem f396_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s m pp pc pl kp kl : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key : List UInt8)
    (hs : 144 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hpre : pre.length = pl.toNat) (hkey : key.length = kl.toNat)
    (hl : pl.toNat + kl.toNat ≤ 4096) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hkp : kp.toNat + kl.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (pl + kl))
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ key).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ key) = viewVal st (contractKey h.context.currentAccountId (pre ++ key)))
    (hproof : ProofBudget h st bud)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId (pre ++ key)) ≤ bud) :
    code396 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f396 Cg
        (pre396 n g ta A gt s m pp pc pl kp kl idx maxP len live F pre key h)
        (fun _ => cost396 cfg F pl kl h (pre ++ key))
        (post396 n g ta A gt s m pp pc pl kp kl idx maxP len live F pre key (StorageHasKeyPost h (pre ++ key) st)
          (StorageRead.foundU64 (h.storage (pre ++ key)))) := by
  iintro #Hk
  iunfold code396 at Hk
  icases Hk with ⟨#H392c, #Hdrop, #Hcode, #Hhc, #F436, #F392, #F551, #F321⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code392 at H392c; icases H392c with ⟨-, -, #H⟩; iexact H
  ihave #H551c : (ifaceCode (GF := GF) e inst mi A n mx ∗ hCode e inst A ∗
      A 436 ↪[wf] FuncInst.wasm types[30]! inst f436) $$ []
  · iframe Hcode Hhc F436
  have hn := hm.mem
  have hg := hm.glob
  have ha392 := hm.funcs 392 (by decide)
  have ha551 := hm.funcs 551 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hT : (pl + kl).toNat = pl.toNat + kl.toNat := by rw [UInt32.toNat_add]; omega
  have hkl : (pre ++ key).length = (pl + kl).toNat := by simp [hpre, hkey, hT]
  have S551 := fun (q : UInt32) => StorageHasKey.f551_spec_host (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi
    e A n g ta mx hm (by omega) Cg gt (s - 32) q (pl + kl) (by omega) (by omega) (pre ++ key) h st hkl
    (by omega) hacc hlim hb hz hlink hproof hbud
  clear hacc hlim hb hz hlink hproof hbud
  unfold cost396
  generalize hK510 : cost510 cfg F pl kl = K510
  generalize hKh : storageHasKeyUse h (pre ++ key) (pl + kl).toNat = Kh at S551
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre396 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Hm, Hp, Hkey, Hhost⟩
  subst hargs
  -- the callees' 112, then the frame: [0, 8) [8, 16) the slice [16, 28) the Vec [28, 32)
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 144 + 112 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 8 24 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 32 + 8) 8 16 $$ Fr with ⟨D, Fr⟩
  icases stk_split n (s.toNat - 32 + 8 + 8) 12 4 $$ Fr with ⟨V, U⟩
  iunfold stk at V D
  icases V with ⟨%vb, %hvb, V⟩
  icases D with ⟨%db, %hdb, D⟩
  ihave V := memBytes_addr (show s.toNat - 32 + 8 + 8 = (s - 32 + 16).toNat by simp [UInt32.toNat_add, h32]; omega) $$ V
  ihave D := memBytes_addr (show s.toNat - 32 + 8 = (s - 32 + 8).toNat by simp [UInt32.toNat_add, h32]; omega) $$ D
  simp only [f396]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 392: the storage key
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapLeaves.f392_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 16) m pp pc pl kp kl idx maxP len live F hF pre key vb (by omega) hvb hpre hkey (by omega)
      (by omega) (by simp [UInt32.toNat_add, h32]; omega) hpp hkp hr)
      using [Hg Lo Hvt Hinv Hm Hp Hkey V] with (rw [hK510]; mstep_norm_full; omega)
  · iunfold pre392
    ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
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
  -- 551: storage_has_key
  ihave #S := S551 q $$ H551c
  icases stk_split n ((s - 32).toNat - 112) 80 32 $$ Lo with ⟨Lo, Lo32⟩
  ihave Lo32 := stk_addr (show (s - 32).toNat - 112 + 80 = (s - 32).toNat - 32 by omega) $$ Lo32
  mstep; mstep [D0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D4] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall S using [Hg HI HW Lo32 Hk Hhost] with (mstep_norm_full; omega)
  · iunfold pre551
    iframe Hg HI HW Lo32 Hk Hhost
    ipureintro; rfl
  iunfold post551 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HW, Lo32, Hk, HH⟩
  subst hrs
  mstep
  -- 321: the Vec freed
  iunfold grown at Hgr
  icases Hgr with ⟨%hl', %hhl, Hinv⟩
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
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl'
      ((q.toNat, (pl + kl).toNat) :: live) F (s - 32 + 16) q (pl + kl) (pl + kl)
      (by intro h0; have := congrArg UInt32.toNat h0; rw [hT] at this; simp at this; omega)
      (by simp [UInt32.toNat_add, h32]; omega)) using [K0 K4 K8 Hinv Blk]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 32 + 16).toNat + 4 + 4 = (s - 32 + 16).toNat + 8 by omega) $$ K8
    iframe K0 K4 K8 Hinv Blk
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  simp only [List.erase_cons_head]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mstep
  mcredits R
  iframe Hc
  iunfold post396
  isplitr
  · ipureintro; first | rfl | simp [htype]
  iframe Hg HI HW Hvt Hm Hp Hkey HH
  isplitr [Hinv]
  · ihave K0 := BorshFT.stkW (n := n) (b := s.toNat - 16) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K0
    ihave K4 := BorshFT.stkW (n := n) (b := s.toNat - 12) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K4
    ihave K8 := BorshFT.stkW (n := n) (b := s.toNat - 8) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K8
    ihave D0 := BorshFT.stkW (n := n) (b := s.toNat - 24) _ (by omega) $$ D0
    ihave D4 := BorshFT.stkW (n := n) (b := s.toNat - 20) _ (by omega) $$ D4
    ihave U := BorshFT.stkA (n := n) (k := 4) (b := s.toNat - 4) (by omega) $$ U
    ihave F0 := BorshFT.stkA (n := n) (k := 8) (b := s.toNat - 32) (by omega) $$ F0
    ihave Lo := BorshFT.stkA (n := n) (k := 80) (b := s.toNat - 144) (by omega) $$ Lo
    ihave Lo32 := BorshFT.stkA (n := n) (k := 32) (b := s.toNat - 64) (by omega) $$ Lo32
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 64) (k1 := 80) (k2 := 32) (k := 112)
      (by omega) (by omega) $$ [Lo Lo32]
    · iframe Lo Lo32
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 32) (k1 := 112) (k2 := 8) (k := 120)
      (by omega) (by omega) $$ [S F0]
    · iframe S F0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 24) (k1 := 120) (k2 := 4) (k := 124)
      (by omega) (by omega) $$ [S D0]
    · iframe S D0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 20) (k1 := 124) (k2 := 4) (k := 128)
      (by omega) (by omega) $$ [S D4]
    · iframe S D4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 16) (k1 := 128) (k2 := 4) (k := 132)
      (by omega) (by omega) $$ [S K0]
    · iframe S K0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 12) (k1 := 132) (k2 := 4) (k := 136)
      (by omega) (by omega) $$ [S K4]
    · iframe S K4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 8) (k1 := 136) (k2 := 4) (k := 140)
      (by omega) (by omega) $$ [S K8]
    · iframe S K8
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 144) (b := s.toNat - 4) (k1 := 140) (k2 := 4) (k := 144)
      (by omega) (by omega) $$ [S U]
    · iframe S U
    iexact S
  iexists hl'
  iframe Hinv
  ipureintro; exact hhl

end S396

/-! ## `contains_key` (394) -/

section S394

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 394 (persistent). -/
def code394 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code396 e n maxP inst mi A mx ∗ code395 n maxP inst mi A ∗
    A 395 ↪[wf] FuncInst.wasm types[14]! inst f395 ∗ A 396 ↪[wf] FuncInst.wasm types[15]! inst f396)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code394 (GF := GF) e n maxP inst mi A mx) := by
  unfold code394; infer_instance

def pre394 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 m, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 176) 176 ∗
    iface n ta A ∗ hslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗ mhostPt h)

/-- Whether `pre ++ borsh(key)` has a value, the heap after at most two grows with two more free
cells. -/
def post394 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8)
    (Q : NearState → Prop) (r : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 r.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 176) 176 ∗
    iface n ta A ∗ hslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜LenIn len 2 len'⌝ ∗ heapInv n maxP len' live (F + 2)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 394, activation excluded. -/
def cost394 (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k : List UInt8) : Nat :=
  800 * cfg.regularOpCost + cost395 cfg F L + cost396 cfg F pl (0 + 4 + L) h k

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`LookupMap::contains_key`** (394) of the `String` `key` at `v`: whether the storage key
`pre ++ borsh(key)` has a value, the host as `StorageHasKeyPost`. -/
theorem f394_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s m pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key : List UInt8)
    (hs : 176 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
    (hL : L.toNat + 4 ≤ 1024) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 2 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) ≤ bud) :
    code394 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f394 Cg
        (pre394 n g ta A gt s m pp pc pl v p c L idx maxP len live F pre key h)
        (fun _ => cost394 cfg F pl L h (pre ++ (bytes32 L ++ key)))
        (post394 n g ta A gt s m pp pc pl v p c L idx maxP len live F pre key
          (StorageHasKeyPost h (pre ++ (bytes32 L ++ key)) st)
          (StorageRead.foundU64 (h.storage (pre ++ (bytes32 L ++ key))))) := by
  iintro #Hk
  iunfold code394 at Hk
  icases Hk with ⟨#H396c, #H395c, #F395, #F396⟩
  ihave #Hdrop : dropCode inst mi A $$ []
  · iunfold code396 at H396c; icases H396c with ⟨-, #H, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code396, code392 at H396c; icases H396c with ⟨⟨-, -, #H⟩, -⟩; iexact H
  ihave #F321 : A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 $$ []
  · iunfold code396 at H396c; icases H396c with ⟨-, -, -, -, -, -, -, #H⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha395 := hm.funcs 395 (by decide)
  have ha396 := hm.funcs 396 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hk4 : (0 + 4 + L).toNat = 4 + L.toNat := by simp [UInt32.toNat_add]; omega
  have hKL : (bytes32 L ++ key).length = (0 + 4 + L).toNat := by simp [bytes32, hkey, hk4]; omega
  have hplk : (pl + (0 + 4 + L)).toNat = pl.toNat + (4 + L.toNat) := by simp [UInt32.toNat_add]; omega
  have S396 := fun (q : UInt32) (hq : q.toNat + 1024 < 2 ^ 32) (l1 : Nat) (hr : roomFor l1 maxP (pl + (0 + 4 + L))) =>
    f396_spec (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi e A n g ta mx hm (by omega) Cg gt (s - 32) m pp pc
      pl q (0 + 4 + L) idx maxP l1 ((q.toNat, 1024) :: live) F hF pre (bytes32 L ++ key) (by omega) (by omega) hpre
      hKL (by rw [hk4]; omega) hl0 hpp (by rw [hk4]; omega) hr h st hacc hlim hb hz hlink hproof hbud
  clear hacc hlim hb hz hlink hproof hbud
  unfold cost394
  generalize hK395 : cost395 cfg F L = K395
  generalize hK396 : cost396 cfg F pl (0 + 4 + L) h (pre ++ (bytes32 L ++ key)) = K396 at S396
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre394 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Hm, Hp, Hv, Hkey, Hhost⟩
  subst hargs
  -- the callees' 144, then the frame: [0, 8) [8, 16) the slice [16, 28) the Vec [28, 32)
  icases stk_split n (s.toNat - 176) 144 32 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 176 + 144 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 8 24 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 32 + 8) 8 16 $$ Fr with ⟨D, Fr⟩
  icases stk_split n (s.toNat - 32 + 8 + 8) 12 4 $$ Fr with ⟨V, U⟩
  iunfold stk at V D
  icases V with ⟨%vb, %hvb, V⟩
  icases D with ⟨%db, %hdb, D⟩
  ihave V := memBytes_addr (show s.toNat - 32 + 8 + 8 = (s - 32 + 16).toNat by simp [UInt32.toNat_add, h32]; omega) $$ V
  ihave D := memBytes_addr (show s.toNat - 32 + 8 = (s - 32 + 8).toNat by simp [UInt32.toNat_add, h32]; omega) $$ D
  icases stk_split n (s.toNat - 176) 16 128 $$ Lo with ⟨Lo16, Lo⟩
  simp only [f394]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 395: the Borsh key
  mstep; mstep; mstep; mstep
  mcall (LookupMapBorsh.f395_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 16) v p c L idx maxP len live F hF key vb (by omega) hkey (by omega) hvb
      (by simp [UInt32.toNat_add, h32]; omega) hv hp
      (roomFor_ofK 1024 (by decide) hroom (lenIn_zero len hroom.1) (by omega)))
      using [Hg Lo Hvt Hinv Hv Hkey V] with (rw [hK395]; mstep_norm_full; omega)
  · iunfold pre395
    ihave Lo := stk_addr (show s.toNat - 176 + 16 = (s - 32).toNat - 128 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hv Hkey V
    ipureintro; rfl
  rw [hK395]
  iunfold post395 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hv, Hkey, %q1, %rest1, %⟨hq10, hq1b, hrest1⟩, Hgr1, V0, V4, V8, Wk, Rest1⟩
  subst hrs
  -- 779: (q1, 4 + L)
  ihave VV := KeyGet.join64 n (s - 32 + 16).toNat q1 1024 $$ [V0 V4]
  · iframe V0 V4
  ihave VV := BorshFT.joinB (n := n) (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 8)
    (bytes32 q1 ++ bytes32 1024) (bytes32 (0 + 4 + L)) (by simp [bytes32]) $$ [VV V8]
  · iframe VV V8
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 32 + 8) (s - 32 + 16) db
      (bytes32 q1 ++ bytes32 1024 ++ bytes32 (0 + 4 + L)) hdb (by simp [bytes32])) using [D VV]
  · iunfold VecDeref.pre
    iframe D VV
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D, VV⟩
  subst hrs
  have hpl1 : (bytes32 q1 ++ (bytes32 1024 ++ bytes32 (0 + 4 + L))).take 4 ++
      (bytes32 q1 ++ (bytes32 1024 ++ bytes32 (0 + 4 + L))).drop 8 = bytes32 q1 ++ bytes32 (0 + 4 + L) := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 q1), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl1]; clear hpl1
  ihave D := KeyGet.split64 n (s - 32 + 8).toNat q1 (0 + 4 + L) $$ D
  icases D with ⟨D0, D4⟩
  ihave D0 := memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by simp [UInt32.toNat_add, h32]; omega) $$ D0
  ihave D4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 12 by simp [UInt32.toNat_add, h32]; omega) $$ D4
  -- 396: contains_key_raw
  iunfold grown at Hgr1
  icases Hgr1 with ⟨%l1, %hl1, Hinv⟩
  have hL1 : LenIn len 1 l1 := lenIn_step 1024 (by decide) (lenIn_zero len hroom.1) hl1
  ihave #S := S396 q1 hq1b l1 (roomFor_ofK _ (by rw [hplk]; omega) hroom hL1 (by omega)) $$ H396c
  ihave Lo := stk_addr (show (s - 32).toNat - 128 = s.toNat - 176 + 16 by omega) $$ Lo
  ihave Lo := stkJ (n := n) (show s.toNat - 176 + 16 = s.toNat - 176 + 16 by rfl) $$ [Lo16 Lo]
  · iframe Lo16 Lo
  ihave Lo := stk_addr (show s.toNat - 176 = (s - 32).toNat - 144 by omega) $$ Lo
  mstep; mstep; mstep [D0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D4] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall S using [Hg Lo HI HW Hvt Hinv Hm Hp Wk Hhost] with (mstep_norm_full; omega)
  · iunfold pre396
    iframe Hg Lo HI HW Hvt Hinv Hm Hp Wk Hhost
    ipureintro; rfl
  iunfold post396 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, HW, Hvt, ⟨%l2, %hl2, Hinv⟩, Hm, Hp, Wk, HH⟩
  subst hrs
  have hsz : (pl + (0 + 4 + L)).toNat ≤ 4096 := by rw [hplk]; omega
  have hL2 : LenIn len 2 l2 := lenIn_step _ hsz hL1 hl2
  mstep
  -- 321(sp + 16): the key's buffer
  ihave VV := BorshFT.splitB (n := n) (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 4) (bytes32 q1)
    (bytes32 1024 ++ bytes32 (0 + 4 + L)) (by simp [bytes32]) $$ VV
  icases VV with ⟨K0, VV⟩
  ihave VV := KeyGet.split64 n ((s - 32 + 16).toNat + 4) 1024 (0 + 4 + L) $$ VV
  icases VV with ⟨K4, K8⟩
  ihave Blk1 : AllocInv.block n q1.toNat (1024 : UInt32).toNat $$ [Wk Rest1]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := q1.toNat) (b := q1.toNat + (4 + L.toNat)) (bytes32 L ++ key) rest1
      (by simp [bytes32, hkey]) $$ [Wk Rest1]
    · iframe Wk Rest1
    iframe X
    ipureintro; simp [bytes32, hkey, hrest1]; omega
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP l2
      ((q1.toNat, 1024) :: live) (F + 1) (s - 32 + 16) q1 1024 (0 + 4 + L)
      (by decide) (by simp [UInt32.toNat_add, h32]; omega)) using [K0 K4 K8 Hinv Blk1]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 32 + 16).toNat + 4 + 4 = (s - 32 + 16).toNat + 8 by omega) $$ K8
    simp only [UInt32.reduceToNat]
    iframe K0 K4 K8 Hinv Blk1
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mstep
  mcredits R
  iframe Hc
  iunfold post394
  isplitr
  · ipureintro; first | rfl | simp [htype]
  iframe Hg HI HW Hvt Hm Hp Hv Hkey HH
  isplitr [Hinv]
  · ihave K0 := BorshFT.stkW (n := n) (b := s.toNat - 16) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K0
    ihave K4 := BorshFT.stkW (n := n) (b := s.toNat - 12) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K4
    ihave K8 := BorshFT.stkW (n := n) (b := s.toNat - 8) _ (by simp [UInt32.toNat_add, h32]; omega) $$ K8
    ihave D0 := BorshFT.stkW (n := n) (b := s.toNat - 24) _ (by omega) $$ D0
    ihave D4 := BorshFT.stkW (n := n) (b := s.toNat - 20) _ (by omega) $$ D4
    ihave U := BorshFT.stkA (n := n) (k := 4) (b := s.toNat - 4) (by omega) $$ U
    ihave F0 := BorshFT.stkA (n := n) (k := 8) (b := s.toNat - 32) (by omega) $$ F0
    ihave Lo := BorshFT.stkA (n := n) (k := 144) (b := s.toNat - 176) (by omega) $$ Lo
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 32) (k1 := 144) (k2 := 8) (k := 152)
      (by omega) (by omega) $$ [Lo F0]
    · iframe Lo F0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 24) (k1 := 152) (k2 := 4) (k := 156)
      (by omega) (by omega) $$ [S D0]
    · iframe S D0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 20) (k1 := 156) (k2 := 4) (k := 160)
      (by omega) (by omega) $$ [S D4]
    · iframe S D4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 16) (k1 := 160) (k2 := 4) (k := 164)
      (by omega) (by omega) $$ [S K0]
    · iframe S K0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 12) (k1 := 164) (k2 := 4) (k := 168)
      (by omega) (by omega) $$ [S K4]
    · iframe S K4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 8) (k1 := 168) (k2 := 4) (k := 172)
      (by omega) (by omega) $$ [S K8]
    · iframe S K8
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 176) (b := s.toNat - 4) (k1 := 172) (k2 := 4) (k := 176)
      (by omega) (by omega) $$ [S U]
    · iframe S U
    iexact S
  iexists l2
  iframe Hinv
  ipureintro; exact hL2

end S394

end WNear.Binary.LookupMapContains
