import Bridge.Functions.LookupMapGet
import Bridge.Functions.LookupMapRemove

/-!
# `LookupMap::insert_raw` (391) and `insert` (401), on a key present in storage

```wat
;; 391 insert_raw(out, map, kp, kl, vp, vl): sp -= 48
;;     392(sp + 16, map, kp, kl)             ;; the storage key, a fresh Vec
;;     779(sp + 8, sp + 16)                  ;; (ptr, len)
;;     547(ptr, len, vp, vl) = 1             ;; storage_write: the old value in EVICTED_REGISTER
;;     550(sp + 32)                          ;; read_register(EVICTED_REGISTER): Some(vec)
;;     364(out, sp + 32, …)                  ;; expect: out := vec
;;     321(sp + 16)                          ;; the key freed
;;     sp += 48
```

* `writePost_reg`: after `storage_write` of a key holding `v` (register `EVICTED_REGISTER`), the
  register holds `v` (and the fees are those of before).
* `f391_some`: `Some(vec)` at `out`, `vec` a fresh block holding the old value; the host as
  `StorageWritePost`; the key's buffer freed.
-/

namespace WNear.Binary.LookupMapInsertSome

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.StorageWrite (evictedRegister evictedRegister_ne wslot wCode pre547 post547)
open WNear.Binary.LookupMapRemove (cost523F_after)

open Near.TrieOverlay in
/-- After `storage_write(key, val)` of a key holding `v` (register `EVICTED_REGISTER`), the
register holds `v`; the costs and fees are unchanged. -/
theorem writePost_reg {e : Nat} {h h' : NearState} {key val v : List UInt8} {st : Near.TrieOverlay.State}
    (hp : StorageWritePost e h key val evictedRegister st h') (hv : h.storage key = some v) :
    h'.registers evictedRegister.toNat = some v ∧ h'.extCosts = h.extCosts ∧ h'.fees = h.fees := by
  obtain ⟨s1, -, -, he⟩ := hp
  have hr := congrArg NearState.registers he
  have hx := congrArg NearState.extCosts he
  have hf := congrArg NearState.fees he
  simp only [erase] at hr hx hf
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]
    simp [storageWriteHost, logWrite, hv, storageReadRegs, evictedRegister_ne,
      NearState.setRegister, NearState.setStorage, NearState.invalidateIterators]
  · rw [hx]
    simp [storageWriteHost, logWrite, hv, storageReadRegs, evictedRegister_ne,
      NearState.setRegister, NearState.setStorage, NearState.invalidateIterators]
  · rw [hf]
    simp [storageWriteHost, logWrite, hv, storageReadRegs, evictedRegister_ne,
      NearState.setRegister, NearState.setStorage, NearState.invalidateIterators]

/-! ## `insert_raw` (391) on a present key -/

open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (vecCode2 costAllocF okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.ReadRegister (ifaceR RegOk)
open WNear.Binary.ReadRegisterF (pre523F post523F cost523F optVecAtF)
open WNear.Binary.LookupMapLeavesF (rr550CodeF pre550F)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (code392 prefixAt pre392 post392 cost510)
open WNear.Binary.StateWrite (stkJ stkL memBytes_disjoint)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 391 on a present key (persistent). -/
def code391s (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code392 n maxP inst mi A ∗ dropCode inst mi A ∗ ifaceCode e inst mi A n mx ∗ wCode e inst A ∗
    rr550CodeF e inst mi A n maxP mx ∗
    A 428 ↪[wf] FuncInst.wasm types[54]! inst f428 ∗ A 547 ↪[wf] FuncInst.wasm types[33]! inst f547 ∗
    A 392 ↪[wf] FuncInst.wasm types[45]! inst f392 ∗ A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 ∗
    A 550 ↪[wf] FuncInst.wasm types[0]! inst f550 ∗ A 364 ↪[wf] FuncInst.wasm types[31]! inst f364)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code391s (GF := GF) e n maxP inst mi A mx) := by
  unfold code391s; infer_instance

def pre391s (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl vp vl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key val ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 kp, .i32 kl, .i32 vp, .i32 vl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 208) 208 ∗ ifaceR n ta A ∗ wslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

/-- `Some(vec)` at `out`: `vec = (p, |v|, |v|)`, `p ↦ v` a fresh live block; the key's block freed. -/
def post391s (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl vp : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key val v : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 208) 208 ∗ ifaceR n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗
    (∃ p : UInt32, ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] UInt32.ofNat v.length ∗
      n ↦[i32][ out.toNat + 8 ] UInt32.ofNat v.length ∗ n ↦[wms][ p.toNat ] v ∗
      ∃ len1 len2, ⌜(len1 = len ∨ len1 = grownLen len (pl + kl)) ∧
          (len2 = len1 ∨ len2 = grownLen len1 (UInt32.ofNat v.length))⌝ ∗
        heapInv n maxP len2 ((p.toNat, v.length) :: live) (F + 1)) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- **`LookupMap::insert_raw`** (391) of `val` under the key `pre ++ key`, present in storage with
the value `v`: `Some(vec)` at `out` with `vec` holding `v` (read back from `EVICTED_REGISTER`); the
host as `StorageWritePost`; the key's buffer freed. -/
theorem f391_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl kp kl vp vl : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key val ob v : List UInt8)
    (hs : 208 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = kl.toNat)
    (hval : val.length = vl.toNat) (hvpos : 0 < vl.toNat)
    (hl : pl.toNat + kl.toNat < 2 ^ 28) (hl0 : 0 < pl.toNat + kl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hkp : kp.toNat + kl.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (pl + kl))
    (hv0 : 0 < v.length) (hv28 : v.length < 2 ^ 28)
    (hr2 : ∀ l, (l = len ∨ l = grownLen len (pl + kl)) → roomFor l maxP (UInt32.ofNat v.length))
    (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ key).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen val.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ key) = viewVal st (contractKey h.context.currentAccountId (pre ++ key)))
    (hproof : ProofBudget h st b)
    (hbud : writeProofCost (contractKey h.context.currentAccountId (pre ++ key)) (h.storage (pre ++ key)) ≤ b)
    (hreg : ∀ v, h.storage (pre ++ key) = some v → withinLimit h.config.maxRegisterLen v.length = true)
    (hsome : h.storage (pre ++ key) = some v) :
    code391s e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f391 Cg
        (pre391s n g ta A gt s out m pp pc pl kp kl vp vl idx maxP len live F pre key val ob h)
        (fun _ => 300 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost510 cfg F pl kl) +
          (51 * cfg.regularOpCost + (257 * cfg.regularOpCost +
            storageWriteUse h (pre ++ key) (pl + kl).toNat vl.toNat)) +
          (13 * cfg.regularOpCost + cost523F cfg F (h.setRegister evictedRegister.toNat v) evictedRegister) +
          315 * cfg.regularOpCost)
        (post391s n g ta A gt s out m pp pc pl kp kl vp idx maxP len live F pre key val v
          (StorageWritePost e h (pre ++ key) val evictedRegister st)) := by
  iintro #Hk
  iunfold code391s at Hk
  icases Hk with ⟨#H392c, #Hdrop, #Hcode, #Hrc, #Hrr, #F428, #F547, #F392, #F321, #F550, #F364⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code392 at H392c; icases H392c with ⟨-, -, #H⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha392 := hm.funcs 392 (by decide)
  have ha547 := hm.funcs 547 (by decide)
  have ha550 := hm.funcs 550 (by decide)
  have ha364 := hm.funcs 364 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t33 : types[33]!.params.length = 4 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 48 + 16).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h48]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e32 : (s - 48 + 32).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h48]; omega
  have hT : (pl + kl).toNat = pl.toNat + kl.toNat := by rw [UInt32.toNat_add]; omega
  have hkl : (pre ++ key).length = (pl + kl).toNat := by simp [hpre, hkey, hT]
  have S547 := fun (q : UInt32) (hdj : q.toNat + (pre ++ key).length ≤ vp.toNat ∨ vp.toNat + val.length ≤ q.toNat) =>
    StorageWrite.f547_spec_host (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi e A n g ta mx hm
      (by omega) Cg gt (s - 48) q (pl + kl) vp vl (by omega) (by omega) (pre ++ key) val h st hkl (by omega) hval hvpos
      hdj hview hacc hlim hvlim hb hz hlink hproof hbud hreg
  have hf1 : StorageRead.foundU64 (h.storage (pre ++ key)) = 1 := by rw [hsome]; rfl
  simp only [hf1] at S547
  clear hview hacc hlim hvlim hb hz hlink hproof hbud hreg hf1
  generalize hK392 : 100 * cfg.regularOpCost + cost510 cfg F pl kl = K392
  generalize hKr : storageWriteUse h (pre ++ key) (pl + kl).toNat vl.toNat = Kr
  generalize hK523 : cost523F cfg F (h.setRegister evictedRegister.toNat v) evictedRegister = K523
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre391s at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HR, Hvt, Hinv, Hm, Hp, Hkey, Hval, Ho, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 208) 160 48 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 208 + 160 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 8 40 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 48 + 8) 8 32 $$ Fr with ⟨D, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 8) 12 20 $$ Fr with ⟨V, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 12) 4 16 $$ Fr with ⟨U, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 12 + 4) 12 4 $$ Fr with ⟨O, W⟩
  iunfold stk at V
  icases V with ⟨%vb, %hvb, V⟩
  ihave V := memBytes_addr (show s.toNat - 48 + 8 + 8 = (s - 48 + 16).toNat by omega) $$ V
  icases stk_split n (s.toNat - 208) 48 112 $$ Lo with ⟨Lo48, Lo⟩
  simp only [f391]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapLeaves.f392_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 16) m pp pc pl kp kl idx maxP len live F hF pre key vb (by omega) hvb hpre hkey hl hl0 (by omega)
      hpp hkp hr) using [Hg Lo Hvt Hinv Hm Hp Hkey V] with (rw [hK392]; mstep_norm_full; omega)
  · iunfold pre392
    ihave Lo := stk_addr (show s.toNat - 208 + 48 = (s - 48).toNat - 112 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hm Hp Hkey V
    ipureintro; rfl
  rw [hK392]
  iunfold post392 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hm, Hp, Hkey, %q, %⟨hq0, hqb⟩, Hgr, V0, V4, V8, Hk⟩
  subst hrs
  ihave V01 := KeyGet.join64 n (s - 48 + 16).toNat q (pl + kl) $$ [V0 V4]
  · iframe V0 V4
  ihave VV := BorshFT.joinB (n := n) (a := (s - 48 + 16).toNat) (b := (s - 48 + 16).toNat + 8)
    (bytes32 q ++ bytes32 (pl + kl)) (bytes32 (pl + kl)) (by simp [bytes32]) $$ [V01 V8]
  · iframe V01 V8
  iunfold stk at D
  icases D with ⟨%db, %hdb, D⟩
  ihave D := memBytes_addr (show s.toNat - 48 + 8 = (s - 48 + 8).toNat by omega) $$ D
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 48 + 8) (s - 48 + 16) db
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
  ihave D := KeyGet.split64 n (s - 48 + 8).toNat q (pl + kl) $$ D
  icases D with ⟨D0, D4⟩
  ihave D0 := memBytes_addr (show (s - 48 + 8).toNat = (s - 48).toNat + 8 by omega) $$ D0
  ihave D4 := memBytes_addr (show (s - 48 + 8).toNat + 4 = (s - 48).toNat + 12 by omega) $$ D4
  mstep; mstep; mstep; mstep [D0] with (simp [bytes32, loadWidth, NumType.byteWidth]); mstep
  mstep [D4] with (simp [bytes32, loadWidth, NumType.byteWidth]); mstep; mstep
  icases memBytes_disjoint n q.toNat vp.toNat (pre ++ key) val
    (by intro h0; have := congrArg List.length h0; rw [hkl] at this; simp at this; omega)
    (by intro h0; have := congrArg List.length h0; rw [hval] at this; simp at this; omega) $$ [Hk Hval]
    with ⟨%hdjv, Hk, Hval⟩
  · iframe Hk Hval
  ihave #H3 : (ifaceCode (GF := GF) e inst mi A n mx ∗ wCode e inst A ∗
      A 428 ↪[wf] FuncInst.wasm types[54]! inst f428) $$ []
  · iframe Hcode Hrc F428
  ihave #S := S547 q hdjv $$ H3
  icases stk_split n ((s - 48).toNat - 112) 80 32 $$ Lo with ⟨Lo, Lo32⟩
  ihave Lo32 := stk_addr (show (s - 48).toNat - 112 + 80 = (s - 48).toNat - 32 by omega) $$ Lo32
  iunfold ifaceR at HI
  icases HI with ⟨HI, HS12⟩
  mcall S using [Hg HI HR Lo32 Hk Hval Hhost] with (rw [hKr]; mstep_norm_full; omega)
  · iunfold pre547
    iframe Hg HI HR Lo32 Hk Hval Hhost
    ipureintro; rfl
  rw [hKr]
  iunfold post547 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HR, Lo32, Hk, Hval, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  obtain ⟨hreg', hext, hfee⟩ := writePost_reg hq hsome
  iunfold grown at Hgr
  icases Hgr with ⟨%hl', %hhl, Hinv⟩
  have hok : RegOk maxP hl' (h'.registers evictedRegister.toNat) := by
    rw [hreg']; exact ⟨hv0, hv28, hr2 _ hhl⟩
  iunfold stk at O
  icases O with ⟨%obb, %hobb, O⟩
  ihave O := memBytes_addr (show s.toNat - 48 + 8 + 8 + 12 + 4 = (s - 48 + 32).toNat by omega) $$ O
  ihave #S550 := LookupMapLeavesF.f550_specF (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm
    (by omega) Cg gt (s - 48) (s - 48 + 32) (by omega) (by omega) (by omega) idx maxP hl'
    ((q.toNat, (pl + kl).toNat) :: live) F hF obb hobb h' hok $$ Hrr
  mstep; mstep; mstep; mstep; mstep
  ihave LL := stkJ (n := n) (show (s - 48).toNat - 112 = s.toNat - 208 + 48 by omega) $$ [Lo48 Lo]
  · iframe Lo48 Lo
  ihave LL := stkJ (n := n) (show (s - 48).toNat - 32 = s.toNat - 208 + (48 + 80) by omega) $$ [LL Lo32]
  · iframe LL Lo32
  mcall S550 using [Hg HI HS12 LL Hvt Hinv O Hhost]
      with (rw [cost523F_after cfg F hreg' hext hfee, hK523]; mstep_norm_full; omega)
  · iunfold pre550F, pre523F, ifaceR
    ihave LL := stkL (n := n) (show s.toNat - 208 = (s - 48).toNat - 160 by omega) (show 48 + 80 + 32 = 160 by rfl) $$ LL
    iframe Hg HI HS12 LL Hvt Hinv O Hhost
    ipureintro; exact ⟨rfl, rfl⟩
  rw [cost523F_after cfg F hreg' hext hfee, hK523]
  iunfold post523F at HQ
  icases HQ with ⟨%hrs, Hg, HIR, LL, Hvt, HV, Hhost⟩
  subst hrs
  ihave HV := (show optVecAtF (GF := GF) n maxP hl' ((q.toNat, (pl + kl).toNat) :: live) F (s - 48 + 32)
      (h'.registers evictedRegister.toNat) ⊢ optVecAtF n maxP hl' ((q.toNat, (pl + kl).toNat) :: live) F (s - 48 + 32)
      (some v) by rw [hreg']) $$ HV
  iunfold optVecAtF at HV
  icases HV with ⟨%p, P0, P4, P8, %len2, %⟨hp0, hlen2⟩, Hinv, Pv⟩
  mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapLeaves.f364_some cfg lim (d + 1) types[31]! rfl inst mi n hn Cg out (s - 48 + 32) 1052644 p
      (UInt32.ofNat v.length) (UInt32.ofNat v.length) ob hob hp0 hout (by omega)) using [P0 P4 P8 Ho]
  · iframe P0 P4 P8 Ho
  icases HQ with ⟨%hrs, P0, P4, P8, Ho0, Ho4, Ho8⟩
  subst hrs
  mstep
  icases memBytes_disjoint n p.toNat q.toNat v (pre ++ key)
    (by intro h0; rw [h0] at hv0; simp at hv0)
    (by intro h0; have := congrArg List.length h0; rw [hkl] at this; simp at this; omega) $$ [Pv Hk]
    with ⟨%hdj, Pv, Hk⟩
  · iframe Pv Hk
  have hpq : (p.toNat, v.length) ≠ (q.toNat, (pl + kl).toNat) := by
    intro h0; simp at h0; omega
  ihave VV := BorshFT.splitB (n := n) (a := (s - 48 + 16).toNat) (b := (s - 48 + 16).toNat + 4) (bytes32 q)
    (bytes32 (pl + kl) ++ bytes32 (pl + kl)) (by simp [bytes32]) $$ VV
  icases VV with ⟨K0, VV⟩
  ihave VV := KeyGet.split64 n ((s - 48 + 16).toNat + 4) (pl + kl) (pl + kl) $$ VV
  icases VV with ⟨K4, K8⟩
  ihave Blk : AllocInv.block n q.toNat (pl + kl).toNat $$ [Hk]
  · iunfold AllocInv.block
    iexists _
    iframe Hk
    ipureintro; exact hkl
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len2
      ((p.toNat, v.length) :: (q.toNat, (pl + kl).toNat) :: live) F (s - 48 + 16) q (pl + kl) (pl + kl)
      (by intro h0; rw [h0] at hT; simp at hT; omega) (by omega)) using [K0 K4 K8 Hinv Blk]
  · iunfold pre747
    ihave K8 := memBytes_addr (show (s - 48 + 16).toNat + 4 + 4 = (s - 48 + 16).toNat + 8 by omega) $$ K8
    iframe K0 K4 K8 Hinv Blk
    ipureintro; exact ⟨rfl, by simp⟩
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  rw [List.erase_cons_tail (by simpa using hpq), List.erase_cons_head] at *
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post391s
  isplitr
  · ipureintro; rfl
  iframe Hg HIR HR Hvt Hm Hp Hkey Hval
  isplitl [F0 U W D0 D4 LL P0 P4 P8 K0 K4 K8]
  · ihave D0 := stk_word n _ _ $$ D0
    ihave D4 := stk_word n _ _ $$ D4
    ihave K0 := stk_word n _ _ $$ K0
    ihave K4 := stk_word n _ _ $$ K4
    ihave K8 := stk_word n _ _ $$ K8
    ihave P0 := stk_word n _ _ $$ P0
    ihave P4 := stk_word n _ _ $$ P4
    ihave P8 := stk_word n _ _ $$ P8
    ihave X := stkJ (n := n) (show s.toNat - 48 = (s - 48).toNat - 160 + 160 by omega) $$ [LL F0]
    · iframe LL F0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 8 = (s - 48).toNat - 160 + (160 + 8) by omega) $$ [X D0]
    · iframe X D0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 12 = (s - 48).toNat - 160 + (160 + 8 + 4) by omega) $$ [X D4]
    · iframe X D4
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat = (s - 48).toNat - 160 + (160 + 8 + 4 + 4) by omega) $$ [X K0]
    · iframe X K0
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat + 4 = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4) by omega) $$ [X K4]
    · iframe X K4
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat + 8 = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4 + 4) by omega) $$ [X K8]
    · iframe X K8
    ihave X := stkJ (n := n) (show s.toNat - 48 + 8 + 8 + 12 = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X U]
    · iframe X U
    ihave X := stkJ (n := n) (show (s - 48 + 32).toNat = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X P0]
    · iframe X P0
    ihave X := stkJ (n := n) (show (s - 48 + 32).toNat + 4 = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X P4]
    · iframe X P4
    ihave X := stkJ (n := n) (show (s - 48 + 32).toNat + 8 = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X P8]
    · iframe X P8
    ihave X := stkJ (n := n) (show s.toNat - 48 + 8 + 8 + 12 + 4 + 12 = (s - 48).toNat - 160 + (160 + 8 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X W]
    · iframe X W
    iapply stkL (n := n) (show (s - 48).toNat - 160 = s.toNat - 208 by omega) (by rfl)
    iexact X
  isplitr [Hhost]
  · iexists p
    iframe Ho0 Ho4 Ho8 Pv
    isplitr
    · ipureintro; exact hp0
    iexists hl', len2
    iframe Hinv
    ipureintro; exact ⟨hhl, hlen2⟩
  iexists h'
  iframe Hhost
  ipureintro; exact hq


end Spec

/-! ## `insert` (401) on a present key -/

section S401

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.LookupMapBorsh (code395 pre395 post395 cost395 code397 pre397 post397 cost397 code398 pre398
  post398)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step lenIn_zero lenIn_mono)

/-- The code of 401 on a present key (persistent). -/
def code401s (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code391s e n maxP inst mi A mx ∗ code395 n maxP inst mi A ∗ code397 n maxP inst mi A ∗
    code398 inst mi A ∗
    A 395 ↪[wf] FuncInst.wasm types[14]! inst f395 ∗ A 397 ↪[wf] FuncInst.wasm types[14]! inst f397 ∗
    A 391 ↪[wf] FuncInst.wasm types[36]! inst f391 ∗ A 398 ↪[wf] FuncInst.wasm types[31]! inst f398)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code401s (GF := GF) e n maxP inst mi A mx) := by
  unfold code401s; infer_instance

def pre401s (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L w : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 v, .i32 w]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 320) 320 ∗ ifaceR n ta A ∗ wslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ w.toNat ] b0 ∗ n ↦[wms][ w.toNat + 8 ] b1 ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

/-- `Some(old)` at `out`, the heap after at most four grows with four more free cells. -/
def post401s (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L w : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key b0 b1 c0 c1 : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 320) 320 ∗ ifaceR n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 4 len'⌝ ∗ heapInv n maxP len' live (F + 4)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ w.toNat ] b0 ∗ n ↦[wms][ w.toNat + 8 ] b1 ∗
    n ↦[wms][ out.toNat ] (storeBytes (.i64 1) 8 ++ (c0 ++ c1)) ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of 401 on a present key, activation excluded. -/
def cost401s (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k old : List UInt8) : Nat :=
  4000 * cfg.regularOpCost + cost395 cfg F L + cost397 cfg F + cost510 cfg F pl (0 + 4 + L) +
    storageWriteUse h k (pl + (0 + 4 + L)).toNat 16 +
    cost523F cfg F (h.setRegister evictedRegister.toNat old) evictedRegister

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- **`LookupMap::insert`** (401) of the `u128` `b0 ++ b1` at `w` under the `String` `key` at `v`,
present in storage with the `u128` `c0 ++ c1`: `Some(old)` at `out`, the host as `StorageWritePost`. -/
theorem f401_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L w : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key b0 b1 c0 c1 ob : List UInt8)
    (hs : 320 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 24) (hout : out.toNat + 24 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
    (hc0 : c0.length = 8) (hc1 : c1.length = 8)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hw : w.toNat + 16 ≤ 2 ^ 32) (hroom : HeapRoomK 4 len maxP)
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
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (c0 ++ c1)) :
    code401s e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f401 Cg
        (pre401s n g ta A gt s out m pp pc pl v p c L w idx maxP len live F pre key b0 b1 ob h)
        (fun _ => cost401s cfg F pl L h (pre ++ (bytes32 L ++ key)) (c0 ++ c1))
        (post401s n g ta A gt s out m pp pc pl v p c L w idx maxP len live F pre key b0 b1 c0 c1
          (StorageWritePost e h (pre ++ (bytes32 L ++ key)) (b0 ++ b1) evictedRegister st)) := by
  iintro #Hk
  iunfold code401s at Hk
  icases Hk with ⟨#H391c, #H395c, #H397c, #H398c, #F395, #F397, #F391, #F398⟩
  ihave #Hdrop : dropCode inst mi A $$ []
  · iunfold code391s at H391c; icases H391c with ⟨-, #H, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code391s, code392 at H391c; icases H391c with ⟨⟨-, -, #H⟩, -⟩; iexact H
  ihave #F321 : A 321 ↪[wf] FuncInst.wasm types[0]! inst f321 $$ []
  · iunfold code391s at H391c; icases H391c with ⟨-, -, -, -, -, -, -, -, #H, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha395 := hm.funcs 395 (by decide)
  have ha397 := hm.funcs 397 (by decide)
  have ha391 := hm.funcs 391 (by decide)
  have ha398 := hm.funcs 398 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t36 : types[36]!.params.length = 6 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h112 : (s - 112).toNat = s.toNat - 112 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hk4 : (0 + 4 + L).toNat = 4 + L.toNat := by simp [UInt32.toNat_add]; omega
  have hKL : (bytes32 L ++ key).length = (0 + 4 + L).toNat := by simp [bytes32, hkey, hk4]; omega
  have hplk : (pl + (0 + 4 + L)).toNat = pl.toNat + (4 + L.toNat) := by simp [UInt32.toNat_add]; omega
  have hv16 : (c0 ++ c1).length = 16 := by simp [hc0, hc1]
  unfold cost401s
  generalize hK395 : cost395 cfg F L = K395
  generalize hK397 : cost397 cfg F = K397
  generalize hKw : storageWriteUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat 16 = Kw
  generalize hK510 : cost510 cfg F pl (0 + 4 + L) = K510
  generalize hK523 : cost523F cfg F (h.setRegister evictedRegister.toNat (c0 ++ c1)) evictedRegister = K523
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre401s at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Hm, Hp, Hv, Hkey, B0, B1, Ho, Hhost⟩
  subst hargs
  -- the callees' 208, then the frame
  icases stk_split n (s.toNat - 320) 208 112 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 320 + 208 = s.toNat - 112 by omega]
  icases stk_split n (s.toNat - 112) 8 104 $$ Fr with ⟨U0, Fr⟩
  rw [show s.toNat - 112 + 8 = s.toNat - 104 by omega]
  icases stk_split n (s.toNat - 104) 16 88 $$ Fr with ⟨T, Fr⟩
  rw [show s.toNat - 104 + 16 = s.toNat - 88 by omega]
  icases stk_split n (s.toNat - 88) 8 80 $$ Fr with ⟨D3, Fr⟩
  rw [show s.toNat - 88 + 8 = s.toNat - 80 by omega]
  icases stk_split n (s.toNat - 80) 8 72 $$ Fr with ⟨D2, Fr⟩
  rw [show s.toNat - 80 + 8 = s.toNat - 72 by omega]
  icases stk_split n (s.toNat - 72) 8 64 $$ Fr with ⟨D1, Fr⟩
  rw [show s.toNat - 72 + 8 = s.toNat - 64 by omega]
  icases stk_split n (s.toNat - 64) 12 52 $$ Fr with ⟨O, Fr⟩
  rw [show s.toNat - 64 + 12 = s.toNat - 52 by omega]
  icases stk_split n (s.toNat - 52) 4 48 $$ Fr with ⟨U60, Fr⟩
  rw [show s.toNat - 52 + 4 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 12 36 $$ Fr with ⟨V1, Fr⟩
  rw [show s.toNat - 48 + 12 = s.toNat - 36 by omega]
  icases stk_split n (s.toNat - 36) 4 32 $$ Fr with ⟨U76, Fr⟩
  rw [show s.toNat - 36 + 4 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 12 20 $$ Fr with ⟨V2, Fr⟩
  rw [show s.toNat - 32 + 12 = s.toNat - 20 by omega]
  icases stk_split n (s.toNat - 20) 4 16 $$ Fr with ⟨U92, Fr⟩
  rw [show s.toNat - 20 + 4 = s.toNat - 16 by omega]
  icases stk_split n (s.toNat - 16) 12 4 $$ Fr with ⟨Cp, U108⟩
  rw [show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  iunfold stk at V1 V2 D1 D2 D3 O T Cp
  icases V1 with ⟨%v1b, %hv1b, V1⟩
  icases V2 with ⟨%v2b, %hv2b, V2⟩
  icases D1 with ⟨%d1b, %hd1b, D1⟩
  icases D2 with ⟨%d2b, %hd2b, D2⟩
  icases D3 with ⟨%d3b, %hd3b, D3⟩
  icases O with ⟨%obb, %hobb, O⟩
  icases T with ⟨%tb, %htb, T⟩
  icases Cp with ⟨%cb, %hcb, Cp⟩
  icases stk_split n (s.toNat - 320) 80 128 $$ Lo with ⟨Lo80, Lo⟩
  rw [show s.toNat - 320 + 80 = s.toNat - 240 by omega]
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
  -- 391: insert_raw, Some(old)
  iunfold grown at Hgr2
  icases Hgr2 with ⟨%l2, %hl2, Hinv⟩
  have hL2 : LenIn len 2 l2 := lenIn_step 1024 (by decide) hL1 hl2
  ihave O := memBytes_addr (show s.toNat - 64 = (s - 112 + 48).toNat by simp [UInt32.toNat_add, h112]; omega) $$ O
  ihave Lo := stk_addr (show (s - 112).toNat - 128 = s.toNat - 240 by omega) $$ Lo
  ihave Lo := stkJ (n := n) (show s.toNat - 240 = s.toNat - 320 + 80 by omega) $$ [Lo80 Lo]
  · iframe Lo80 Lo
  ihave Lo := stk_addr (show s.toNat - 320 = (s - 112).toNat - 208 by omega) $$ Lo
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep [D20] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D24] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall (f391_some cfg lim (d + 1) types[36]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 112) (s - 112 + 48) m pp pc pl q1 (0 + 4 + L) q2 (0 + 16) idx maxP l2
      ((q2.toNat, 1024) :: (q1.toNat, 1024) :: live) F hF pre (bytes32 L ++ key) (b0 ++ b1) obb (c0 ++ c1)
      (by omega) (by rw [h112]; omega) hobb (by simp [UInt32.toNat_add, h112]; omega) hpre hKL
      (by simp [hb0, hb1]) (by decide) (by rw [hk4]; omega) (by rw [hk4]; omega) hpp (by rw [hk4]; omega)
      (roomFor_ofK _ (by rw [hplk]; omega) hroom hL2 (by omega)) (by rw [hv16]; decide) (by rw [hv16]; decide)
      (fun l hl => roomFor_ofK _ (by rw [hv16]; decide) hroom
        (lenIn_step _ (by rw [hplk]; omega) hL2 hl) (by omega))
      h st hview hacc hlim hvlim hb hz hlink hproof hbud
      (by intro x hx; rw [hsome] at hx; cases hx; rw [hv16]; exact hreg) hsome)
      using [Hg Lo HI HW Hvt Hinv Hm Hp Wk Wv O Hhost]
      with (rw [show ((0:UInt32) + 16).toNat = 16 from rfl, hKw, hK510, hK523]; mstep_norm_full; omega)
  · iunfold pre391s
    iframe Hg Lo HI HW Hvt Hinv Hm Hp Wk Wv O Hhost
    ipureintro; rfl
  rw [show ((0:UInt32) + 16).toNat = 16 from rfl, hKw, hK510, hK523]
  iunfold post391s at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, HW, Hvt, Hm, Hp, Wk, Wv, ⟨%pv, %hpv0, P0, P4, P8, Pv, %len1, %len3, %⟨hlen1, hlen3⟩, Hinv⟩, Hhost⟩
  subst hrs
  have hsz : (pl + (0 + 4 + L)).toNat ≤ 4096 := by rw [hplk]; omega
  have hL4 : LenIn len 4 len3 :=
    lenIn_step _ (by rw [hv16]; decide) (lenIn_step _ hsz hL2 hlen1) hlen3
  simp only [hv16]
  rw [show (UInt32.ofNat 16 : UInt32) = 16 from rfl]
  ihave P0 := memBytes_addr (show (s - 112 + 48).toNat = (s - 112).toNat + 48 by simp [UInt32.toNat_add, h112]; omega) $$ P0
  -- the Some branch
  mstep; mstep; mstep; mstep [P0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr
  · ipureintro; exact ⟨rfl, hpv0⟩
  mctrl_norm; mpay
  -- [sp+104] := [sp+56]; [sp+96..104) := [sp+48..56)
  ihave P8 := memBytes_addr (show (s - 112 + 48).toNat + 8 = (s - 112 + 48 + 8).toNat by simp [UInt32.toNat_add, h112]; omega) $$ P8
  ihave Cp := U128From.memBytes_split n (s.toNat - 16) 8 cb (by omega) $$ Cp
  icases Cp with ⟨C0, C8⟩
  have hc8 : (cb.drop 8).length = 4 := by simp; omega
  have hc0' : (cb.take 8).length = 8 := by simp; omega
  ihave C0 := memBytes_addr (show s.toNat - 16 = (s - 112).toNat + 96 by omega) $$ C0
  ihave C8 := memBytes_addr (show s.toNat - 16 + 8 = (s - 112 + 96 + 8).toNat by simp [UInt32.toNat_add, h112]; omega) $$ C8
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [P8] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep [C8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  ihave P0 := memBytes_addr (show (s - 112).toNat + 48 = (s - 112 + 48).toNat by simp [UInt32.toNat_add, h112]; omega) $$ P0
  ihave PP := KeyGet.join64 n (s - 112 + 48).toNat pv 16 $$ [P0 P4]
  · iframe P0 P4
  ihave PP := memBytes_addr (show (s - 112 + 48).toNat = (s - 112).toNat + 48 by simp [UInt32.toNat_add, h112]; omega) $$ PP
  mstep; mstep; mstep [PP] with (simp [bytes32, loadWidth, NumType.byteWidth])
  rw [VecFromElem.ofNat_decode_pair]
  mstep [C0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [VecFromElem.storeBytes_pair64]
  rw [show (UInt32.ofNat 16 : UInt32) = 16 from rfl]
  -- 779(sp + 24, sp + 96): (pv, 16)
  ihave C0 := memBytes_addr (show (s - 112).toNat + 96 = (s - 112 + 96).toNat by simp [UInt32.toNat_add, h112]; omega) $$ C0
  ihave C8 := memBytes_addr (show (s - 112 + 96 + 8).toNat = (s - 112 + 96).toNat + (bytes32 pv ++ bytes32 16).length by simp [bytes32, UInt32.toNat_add, h112]; omega) $$ C8
  ihave CC := BorshFT.joinB (n := n) (a := (s - 112 + 96).toNat) (b := (s - 112 + 96).toNat + (bytes32 pv ++ bytes32 16).length)
    (bytes32 pv ++ bytes32 16) (bytes32 16) rfl $$ [C0 C8]
  · iframe C0 C8
  ihave D3 := memBytes_addr (show s.toNat - 88 = (s - 112 + 24).toNat by simp [UInt32.toNat_add, h112]; omega) $$ D3
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 112 + 24) (s - 112 + 96) d3b
      (bytes32 pv ++ bytes32 16 ++ bytes32 16) hd3b (by simp [bytes32])) using [D3 CC]
  · iunfold VecDeref.pre
    iframe D3 CC
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D3, CC⟩
  subst hrs
  have hpl3 : (bytes32 pv ++ (bytes32 16 ++ bytes32 16)).take 4 ++
      (bytes32 pv ++ (bytes32 16 ++ bytes32 16)).drop 8 = bytes32 pv ++ bytes32 16 := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 pv), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl3]; clear hpl3
  ihave D3 := KeyGet.split64 n (s - 112 + 24).toNat pv 16 $$ D3
  icases D3 with ⟨D30, D34⟩
  ihave D30 := memBytes_addr (show (s - 112 + 24).toNat = (s - 112).toNat + 24 by simp [UInt32.toNat_add, h112]; omega) $$ D30
  ihave D34 := memBytes_addr (show (s - 112 + 24).toNat + 4 = (s - 112).toNat + 28 by simp [UInt32.toNat_add, h112]; omega) $$ D34
  -- 398(sp + 8, pv, 16): the old u128
  icases stk_split n ((s - 112).toNat - 208) 64 144 $$ Lo with ⟨Lo64, Lo⟩
  ihave Lo := stk_addr (show (s - 112).toNat - 208 + 64 = (s - 112).toNat - 144 by omega) $$ Lo
  ihave Pv := BorshFT.splitB (n := n) (a := pv.toNat) (b := pv.toNat + 8) c0 c1 (by simp [hc0]) $$ Pv
  icases Pv with ⟨Pv0, Pv8⟩
  ihave T := memBytes_addr (show s.toNat - 104 = (s - 112 + 8).toNat by simp [UInt32.toNat_add, h112]; omega) $$ T
  icases FmtSink.heapInv_bound (p := pv.toNat) (s := 16) (by simp) $$ Hinv with ⟨%hpvb, Hinv⟩
  mstep; mstep; mstep; mstep; mstep [D30] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [D34] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mcall (LookupMapBorsh.f398_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 112)
      (s - 112 + 8) pv c0 c1 tb (by omega) hc0 hc1 htb (by simp [UInt32.toNat_add, h112]; omega) (by omega))
      using [Hg Lo Pv0 Pv8 T]
  · iunfold pre398
    iframe Hg Lo Pv0 Pv8 T
    ipureintro; rfl
  iunfold post398 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Pv0, Pv8, T0, T8⟩
  subst hrs
  have h104 : (s - 112 + 8).toNat = s.toNat - 104 := by simp [UInt32.toNat_add, h112]; omega
  have hc0n : c0 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hc1n : c1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  ihave T8 := memBytes_addr (show (s - 112 + 8).toNat + 8 = (s - 112 + 8 + 8).toNat by simp [UInt32.toNat_add, h112]; omega) $$ T8
  ihave T0 := memBytes_addr (show (s - 112 + 8).toNat = (s - 112).toNat + 8 by simp [UInt32.toNat_add, h112]; omega) $$ T0
  mstep; mstep; mstep; mstep; mstep; mstep [T8] with (first | (simp [hc1, loadWidth, NumType.byteWidth]) | exact List.ne_nil_of_length_pos (by omega)); mstep
  mstep; mstep [T0] with (first | (simp [hc0, loadWidth, NumType.byteWidth]) | exact List.ne_nil_of_length_pos (by omega)); mstep
  -- 321(sp + 96): the old value's buffer
  ihave CC := BorshFT.splitB (n := n) (a := (s - 112 + 96).toNat) (b := (s - 112 + 96).toNat + 4) (bytes32 pv)
    (bytes32 16 ++ bytes32 16) (by simp [bytes32]) $$ CC
  icases CC with ⟨C0, CC⟩
  ihave CC := KeyGet.split64 n ((s - 112 + 96).toNat + 4) 16 16 $$ CC
  icases CC with ⟨C4, C8⟩
  ihave Blk3 : AllocInv.block n pv.toNat 16 $$ [Pv0 Pv8]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := pv.toNat) (b := pv.toNat + 8) c0 c1 (by simp [hc0]) $$ [Pv0 Pv8]
    · iframe Pv0 Pv8
    iframe X
    ipureintro; simp [hc0, hc1]
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len3
      ((pv.toNat, 16) :: (q2.toNat, 1024) :: (q1.toNat, 1024) :: live) (F + 1) (s - 112 + 96) pv 16 16
      (by decide) (by simp [UInt32.toNat_add, h112]; omega)) using [C0 C4 C8 Hinv Blk3]
  · iunfold pre747
    ihave C8 := memBytes_addr (show (s - 112 + 96).toNat + 4 + 4 = (s - 112 + 96).toNat + 8 by omega) $$ C8
    simp only [UInt32.reduceToNat]
    iframe C0 C4 C8 Hinv Blk3
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, C0, C4, C8, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
  mstep; mstep
  -- 321(sp + 80): the value's buffer
  ihave VV2 := BorshFT.splitB (n := n) (a := (s - 112 + 80).toNat) (b := (s - 112 + 80).toNat + 4) (bytes32 q2)
    (bytes32 1024 ++ bytes32 (0 + 16)) (by simp [bytes32]) $$ VV2
  icases VV2 with ⟨P20, VV2⟩
  ihave VV2 := KeyGet.split64 n ((s - 112 + 80).toNat + 4) 1024 (0 + 16) $$ VV2
  icases VV2 with ⟨P24, P28⟩
  ihave Blk2 : AllocInv.block n q2.toNat (1024 : UInt32).toNat $$ [Wv Rest2]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := q2.toNat) (b := q2.toNat + 16) (b0 ++ b1) rest2
      (by simp [hb0, hb1]) $$ [Wv Rest2]
    · iframe Wv Rest2
    iframe X
    ipureintro; simp [hb0, hb1, hrest2]
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len3
      ((q2.toNat, 1024) :: (q1.toNat, 1024) :: live) (F + 1 + 1) (s - 112 + 80) q2 1024 (0 + 16)
      (by decide) (by simp [UInt32.toNat_add, h112]; omega)) using [P20 P24 P28 Hinv Blk2]
  · iunfold pre747
    ihave P28 := memBytes_addr (show (s - 112 + 80).toNat + 4 + 4 = (s - 112 + 80).toNat + 8 by omega) $$ P28
    simp only [UInt32.reduceToNat]
    iframe P20 P24 P28 Hinv Blk2
    ipureintro; first | exact ⟨rfl, List.mem_cons_self⟩ | exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, P20, P24, P28, Hinv⟩
  subst hrs
  simp only [UInt32.reduceToNat, List.erase_cons_head]
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
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len3
      ((q1.toNat, 1024) :: live) (F + 1 + 1 + 1) (s - 112 + 64) q1 1024 (0 + 4 + L)
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
  rw [BorshLeaves.storeBytes_i64_decode _ hc1]
  mstep; mstep; mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [BorshLeaves.storeBytes_i64_decode _ hc0]
  mstep; mstep; mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 112 + 112 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post401s
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI HW Hvt Hm Hp Hv Hkey B0 B1
  isplitl [Lo64 Lo U0 T0 T8 D30 D34 D20 D24 D10 D14 PP P8 U60 K0 K4 K8 U76 P20 P24 P28 U92 C0 C4 C8 U108]
  · ihave C8 := BorshFT.stkW (b := s.toNat - 8) _ (by simp [UInt32.toNat_add, h112]; omega) $$ C8
    ihave X := BorshFT.stkJ (a := s.toNat - 8) (b := s.toNat - 4) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [C8 U108]
    · iframe C8 U108
    ihave C4 := BorshFT.stkW (b := s.toNat - 12) _ (by simp [UInt32.toNat_add, h112]; omega) $$ C4
    ihave X := BorshFT.stkJ (a := s.toNat - 12) (b := s.toNat - 8) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [C4 X]
    · iframe C4 X
    ihave C0 := BorshFT.stkW (b := s.toNat - 16) _ (by simp [UInt32.toNat_add, h112]; omega) $$ C0
    ihave X := BorshFT.stkJ (a := s.toNat - 16) (b := s.toNat - 12) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [C0 X]
    · iframe C0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 20) (b := s.toNat - 16) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [U92 X]
    · iframe U92 X
    ihave P28 := BorshFT.stkW (b := s.toNat - 24) _ (by simp [UInt32.toNat_add, h112]; omega) $$ P28
    ihave X := BorshFT.stkJ (a := s.toNat - 24) (b := s.toNat - 20) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [P28 X]
    · iframe P28 X
    ihave P24 := BorshFT.stkW (b := s.toNat - 28) _ (by simp [UInt32.toNat_add, h112]; omega) $$ P24
    ihave X := BorshFT.stkJ (a := s.toNat - 28) (b := s.toNat - 24) (k1 := 4) (k2 := 24) (k := 28) (by omega) rfl $$ [P24 X]
    · iframe P24 X
    ihave P20 := BorshFT.stkW (b := s.toNat - 32) _ (by simp [UInt32.toNat_add, h112]; omega) $$ P20
    ihave X := BorshFT.stkJ (a := s.toNat - 32) (b := s.toNat - 28) (k1 := 4) (k2 := 28) (k := 32) (by omega) rfl $$ [P20 X]
    · iframe P20 X
    ihave X := BorshFT.stkJ (a := s.toNat - 36) (b := s.toNat - 32) (k1 := 4) (k2 := 32) (k := 36) (by omega) rfl $$ [U76 X]
    · iframe U76 X
    ihave K8 := BorshFT.stkW (b := s.toNat - 40) _ (by simp [UInt32.toNat_add, h112]; omega) $$ K8
    ihave X := BorshFT.stkJ (a := s.toNat - 40) (b := s.toNat - 36) (k1 := 4) (k2 := 36) (k := 40) (by omega) rfl $$ [K8 X]
    · iframe K8 X
    ihave K4 := BorshFT.stkW (b := s.toNat - 44) _ (by simp [UInt32.toNat_add, h112]; omega) $$ K4
    ihave X := BorshFT.stkJ (a := s.toNat - 44) (b := s.toNat - 40) (k1 := 4) (k2 := 40) (k := 44) (by omega) rfl $$ [K4 X]
    · iframe K4 X
    ihave K0 := BorshFT.stkW (b := s.toNat - 48) _ (by simp [UInt32.toNat_add, h112]; omega) $$ K0
    ihave X := BorshFT.stkJ (a := s.toNat - 48) (b := s.toNat - 44) (k1 := 4) (k2 := 44) (k := 48) (by omega) rfl $$ [K0 X]
    · iframe K0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 52) (b := s.toNat - 48) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [U60 X]
    · iframe U60 X
    ihave P8 := BorshFT.stkW (b := s.toNat - 56) _ (by simp [UInt32.toNat_add, h112]; omega) $$ P8
    ihave X := BorshFT.stkJ (a := s.toNat - 56) (b := s.toNat - 52) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [P8 X]
    · iframe P8 X
    ihave PP := BorshFT.stkB (b := s.toNat - 64) (k := 8) _ (by omega) (by simp [bytes32]) $$ PP
    ihave X := BorshFT.stkJ (a := s.toNat - 64) (b := s.toNat - 56) (k1 := 8) (k2 := 56) (k := 64) (by omega) rfl $$ [PP X]
    · iframe PP X
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
    ihave D34 := BorshFT.stkW (b := s.toNat - 84) _ (by omega) $$ D34
    ihave X := BorshFT.stkJ (a := s.toNat - 84) (b := s.toNat - 80) (k1 := 4) (k2 := 80) (k := 84) (by omega) rfl $$ [D34 X]
    · iframe D34 X
    ihave D30 := BorshFT.stkW (b := s.toNat - 88) _ (by omega) $$ D30
    ihave X := BorshFT.stkJ (a := s.toNat - 88) (b := s.toNat - 84) (k1 := 4) (k2 := 84) (k := 88) (by omega) rfl $$ [D30 X]
    · iframe D30 X
    ihave T8 := BorshFT.stkB (b := s.toNat - 96) (k := 8) _ (by simp [UInt32.toNat_add, h112]; omega) hc1 $$ T8
    ihave X := BorshFT.stkJ (a := s.toNat - 96) (b := s.toNat - 88) (k1 := 8) (k2 := 88) (k := 96) (by omega) rfl $$ [T8 X]
    · iframe T8 X
    ihave T0 := BorshFT.stkB (b := s.toNat - 104) (k := 8) _ (by omega) hc0 $$ T0
    ihave X := BorshFT.stkJ (a := s.toNat - 104) (b := s.toNat - 96) (k1 := 8) (k2 := 96) (k := 104) (by omega) rfl $$ [T0 X]
    · iframe T0 X
    ihave X := BorshFT.stkJ (a := s.toNat - 112) (b := s.toNat - 104) (k1 := 8) (k2 := 104) (k := 112) (by omega) rfl $$ [U0 X]
    · iframe U0 X
    ihave Lo := BorshFT.stkA (b := s.toNat - 256) (by omega) $$ Lo
    ihave X := BorshFT.stkJ (a := s.toNat - 256) (b := s.toNat - 112) (k1 := 144) (k2 := 112) (k := 256) (by omega) rfl $$ [Lo X]
    · iframe Lo X
    ihave Lo64 := BorshFT.stkA (b := s.toNat - 320) (by omega) $$ Lo64
    iapply BorshFT.stkJ (a := s.toNat - 320) (b := s.toNat - 256) (k1 := 64) (k2 := 256) (k := 320) (by omega) rfl
    iframe Lo64 X
  isplitl [Hinv]
  · iexists len3
    rw [show F + 1 + 1 + 1 + 1 = F + 4 by omega]
    iframe Hinv
    ipureintro; exact hL4
  isplitl [Q0 Q8 Q16]
  · ihave Q16 := memBytes_addr (show (out + 16).toNat = out.toNat + 8 + c0.length by omega) $$ Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat + 8) (b := out.toNat + 8 + c0.length) c0 c1 rfl $$ [Q8 Q16]
    · iframe Q8 Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat) (b := out.toNat + 8) (storeBytes (.i64 1) 8)
      (c0 ++ c1) (by rfl) $$ [Q0 X]
    · iframe Q0 X
    iexact X
  iexact Hhost

end S401

end WNear.Binary.LookupMapInsertSome
