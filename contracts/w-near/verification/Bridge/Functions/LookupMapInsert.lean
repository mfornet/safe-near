import Bridge.Functions.LookupMapLeaves

/-!
# `LookupMap::insert_raw` (391), on a key absent from storage

```wat
;; 391 insert_raw(out, map, kp, kl, vp, vl): sp -= 48
;;     392(sp + 16, map, kp, kl)             ;; the storage key, a fresh Vec
;;     779(sp + 8, sp + 16)                  ;; (ptr, len)
;;     547(ptr, len, vp, vl) = 0 → out := 0  ;; storage_write: nothing evicted, None
;;     (= 1 → 550(sp + 32); 364(out, sp + 32, …): not on this path)
;;     321(sp + 16)                          ;; the key freed
;;     sp += 48
```

* `f391_none`: on a host whose storage has no value under `pre ++ key`, `out := None` (the
  word 0), the host as `StorageWritePost` of `storage_write(pre ++ key, val)`, the heap with one
  more free cell.
-/

namespace WNear.Binary.LookupMapInsert

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.VecWithCap (vecCode2 costAllocF okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.StorageWrite (wslot wCode pre547 post547 evictedRegister)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (code392 prefixAt pre392 post392 cost510)
open WNear.Binary.StateWrite (stkJ stkL memBytes_disjoint)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 391 (persistent). -/
def code391 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code392 n maxP inst mi A ∗ dropCode inst mi A ∗ ifaceCode e inst mi A n mx ∗ wCode e inst A ∗
    A 428 ↪[wf] FuncInst.wasm types[54]! inst f428 ∗ A 547 ↪[wf] FuncInst.wasm types[33]! inst f547 ∗
    A 392 ↪[wf] FuncInst.wasm types[45]! inst f392 ∗ A 321 ↪[wf] FuncInst.wasm types[0]! inst f321)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code391 (GF := GF) e n maxP inst mi A mx) := by
  unfold code391; infer_instance

def pre391 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl vp vl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key val ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 kp, .i32 kl, .i32 vp, .i32 vl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 160) 160 ∗ iface n ta A ∗ wslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post391 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl vp : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key val : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 160) 160 ∗ iface n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜len' = len ∨ len' = VecFromElem.grownLen len (pl + kl)⌝ ∗ heapInv n maxP len' live (F + 1)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗
    n ↦[i32][ out.toNat ] 0 ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`LookupMap::insert_raw`** (391) of `val` under the key `pre ++ key` (the map's prefix, the
key's bytes), absent from storage: `None` (the word 0 at `out`); the host as `StorageWritePost`;
the key's buffer freed. -/
theorem f391_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl kp kl vp vl : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key val ob : List UInt8)
    (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 4) (hout : out.toNat + 4 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = kl.toNat) (hval : val.length = vl.toNat)
    (hvpos : 0 < vl.toNat) (hl : pl.toNat + kl.toNat < 2 ^ 28) (hl0 : 0 < pl.toNat + kl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hkp : kp.toNat + kl.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (pl + kl))
    (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ key).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen val.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ key) = viewVal st (contractKey h.context.currentAccountId (pre ++ key)))
    (hproof : ProofBudget h st b)
    (hbud : writeProofCost (contractKey h.context.currentAccountId (pre ++ key)) (h.storage (pre ++ key)) ≤ b)
    (hreg : ∀ v, h.storage (pre ++ key) = some v → withinLimit h.config.maxRegisterLen v.length = true)
    (hnone : h.storage (pre ++ key) = none) :
    code391 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f391 Cg
        (pre391 n g ta A gt s out m pp pc pl kp kl vp vl idx maxP len live F pre key val ob h)
        (fun _ => 200 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost510 cfg F pl kl) +
          (51 * cfg.regularOpCost + (257 * cfg.regularOpCost +
            storageWriteUse h (pre ++ key) (pl + kl).toNat vl.toNat)) + 315 * cfg.regularOpCost)
        (post391 n g ta A gt s out m pp pc pl kp kl vp idx maxP len live F pre key val
          (StorageWritePost e h (pre ++ key) val evictedRegister st)) := by
  iintro #Hk
  iunfold code391 at Hk
  icases Hk with ⟨#H392c, #Hdrop, #Hcode, #Hw, #F428, #F547, #F392, #F321⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold code392 at H392c; icases H392c with ⟨-, -, #H⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha392 := hm.funcs 392 (by decide)
  have ha547 := hm.funcs 547 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t33 : types[33]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 48 + 16).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h48]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have hT : (pl + kl).toNat = pl.toNat + kl.toNat := by rw [UInt32.toNat_add]; omega
  have hkl : (pre ++ key).length = (pl + kl).toNat := by simp [hpre, hkey, hT]
  have S547 := fun (q : UInt32) (hdj : q.toNat + (pre ++ key).length ≤ vp.toNat ∨ vp.toNat + val.length ≤ q.toNat) =>
    StorageWrite.f547_spec_host (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi e A n g ta mx hm
      (by omega) Cg gt (s - 48) q (pl + kl) vp vl (by omega) (by omega) (pre ++ key) val h st hkl (by omega) hval hvpos
      hdj hview hacc hlim hvlim hb hz hlink hproof hbud hreg
  have hf0 : StorageRead.foundU64 (h.storage (pre ++ key)) = 0 := by rw [hnone]; rfl
  simp only [hf0] at S547
  clear hview hacc hlim hvlim hb hz hlink hproof hbud hreg hnone hf0
  generalize hK392 : 100 * cfg.regularOpCost + cost510 cfg F pl kl = K392
  generalize hKw : storageWriteUse h (pre ++ key) (pl + kl).toNat vl.toNat = Kw
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre391 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Hm, Hp, Hkey, Hval, Ho, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 160) 112 48 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 160 + 112 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 8 40 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 48 + 8) 8 32 $$ Fr with ⟨D, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 8) 12 20 $$ Fr with ⟨V, Fr20⟩
  iunfold stk at V
  icases V with ⟨%vb, %hvb, V⟩
  ihave V := memBytes_addr (show s.toNat - 48 + 8 + 8 = (s - 48 + 16).toNat by omega) $$ V
  simp only [f391]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapLeaves.f392_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 16) m pp pc pl kp kl idx maxP len live F hF pre key vb (by omega) hvb hpre hkey hl hl0 (by omega)
      hpp hkp hr) using [Hg Lo Hvt Hinv Hm Hp Hkey V] with (rw [hK392]; mstep_norm_full; omega)
  · iunfold pre392
    ihave Lo := stk_addr (show s.toNat - 160 = (s - 48).toNat - 112 by omega) $$ Lo
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
  mstep; mstep; mstep; mstep [D0] with (simp [bytes32, loadWidth, NumType.byteWidth]); mstep; mstep [D4] with (simp [bytes32, loadWidth, NumType.byteWidth]); mstep; mstep
  icases memBytes_disjoint n q.toNat vp.toNat (pre ++ key) val
    (by intro h0; have := congrArg List.length h0; rw [hkl] at this; simp at this; omega)
    (by intro h0; have := congrArg List.length h0; rw [hval] at this; simp at this; omega) $$ [Hk Hval]
    with ⟨%hdj, Hk, Hval⟩
  · iframe Hk Hval
  ihave #H3 : (ifaceCode (GF := GF) e inst mi A n mx ∗ wCode e inst A ∗
      A 428 ↪[wf] FuncInst.wasm types[54]! inst f428) $$ []
  · iframe Hcode Hw F428
  ihave #S := S547 q hdj $$ H3
  icases stk_split n ((s - 48).toNat - 112) 80 32 $$ Lo with ⟨Lo, Lo32⟩
  ihave Lo32 := stk_addr (show (s - 48).toNat - 112 + 80 = (s - 48).toNat - 32 by omega) $$ Lo32
  mcall S using [Hg HI HW Lo32 Hk Hval Hhost] with (rw [hKw]; mstep_norm_full; omega)
  · iunfold pre547
    iframe Hg HI HW Lo32 Hk Hval Hhost
    ipureintro; rfl
  rw [hKw]
  iunfold post547 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HW, Lo32, Hk, Hval, Hhost⟩
  subst hrs
  mstep; mstep
  mstep; mstep; mstep [Ho] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [hob, storeWidth, NumType.byteWidth]; done) | rfl)
  iunfold grown at Hgr
  icases Hgr with ⟨%hl', %hhl, Hinv⟩
  ihave VV := BorshFT.splitB (n := n) (a := (s - 48 + 16).toNat) (b := (s - 48 + 16).toNat + 4) (bytes32 q)
    (bytes32 (pl + kl) ++ bytes32 (pl + kl)) (by simp [bytes32]) $$ VV
  icases VV with ⟨P0, VV⟩
  ihave VV := KeyGet.split64 n ((s - 48 + 16).toNat + 4) (pl + kl) (pl + kl) $$ VV
  icases VV with ⟨P4, P8⟩
  ihave Blk : AllocInv.block n q.toNat (pl + kl).toNat $$ [Hk]
  · iunfold AllocInv.block
    iexists _
    iframe Hk
    ipureintro; exact hkl
  mstep; mstep; mstep
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl'
      ((q.toNat, (pl + kl).toNat) :: live) F (s - 48 + 16) q (pl + kl) (pl + kl)
      (by intro h0; rw [h0] at hT; simp at hT; omega) (by omega)) using [P0 P4 P8 Hinv Blk]
  · iunfold pre747
    ihave P8 := memBytes_addr (show (s - 48 + 16).toNat + 4 + 4 = (s - 48 + 16).toNat + 8 by omega) $$ P8
    iframe P0 P4 P8 Hinv Blk
    ipureintro; exact ⟨rfl, List.mem_cons_self⟩
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, Hinv⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post391
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI HW Hvt Hm Hp Hkey Hval Ho
  isplitl [F0 Fr20 D0 D4 Lo Lo32 P0 P4 P8]
  · ihave D0 := stk_word n _ _ $$ D0
    ihave D4 := stk_word n _ _ $$ D4
    ihave P0 := stk_word n _ _ $$ P0
    ihave P4 := stk_word n _ _ $$ P4
    ihave P8 := stk_word n _ _ $$ P8
    ihave X := stkJ (n := n) (show (s - 48).toNat - 32 = (s - 48).toNat - 112 + 80 by omega) $$ [Lo Lo32]
    · iframe Lo Lo32
    ihave X := stkJ (n := n) (show s.toNat - 48 = (s - 48).toNat - 112 + (80 + 32) by omega) $$ [X F0]
    · iframe X F0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 8 = (s - 48).toNat - 112 + (80 + 32 + 8) by omega) $$ [X D0]
    · iframe X D0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 12 = (s - 48).toNat - 112 + (80 + 32 + 8 + 4) by omega) $$ [X D4]
    · iframe X D4
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat = (s - 48).toNat - 112 + (80 + 32 + 8 + 4 + 4) by omega) $$ [X P0]
    · iframe X P0
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat + 4 = (s - 48).toNat - 112 + (80 + 32 + 8 + 4 + 4 + 4) by omega) $$ [X P4]
    · iframe X P4
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat + 4 + 4 = (s - 48).toNat - 112 + (80 + 32 + 8 + 4 + 4 + 4 + 4) by omega) $$ [X P8]
    · iframe X P8
    ihave X := stkJ (n := n) (show s.toNat - 48 + 8 + 8 + 12 = (s - 48).toNat - 112 + (80 + 32 + 8 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X Fr20]
    · iframe X Fr20
    iapply stkL (n := n) (show (s - 48).toNat - 112 = s.toNat - 160 by omega) (by rfl)
    iexact X
  isplitl [Hinv]
  · iexists hl'
    simp only [List.erase_cons_head] at *
    iframe Hinv
    ipureintro; exact hhl
  iexact Hhost

end Spec

end WNear.Binary.LookupMapInsert
