import Bridge.Functions.LookupMapGet
import Bridge.Functions.StorageReadNoneF

/-! The absent-key branch of `LookupMap::get_raw` (400). -/

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

section S400None
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Absent lookup: the output is None, and the temporary key is freed. -/
def post400None (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl kp kl : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 224) 224 ∗ ifaceR n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ kp.toNat ] key ∗ n ↦[i32][ out.toNat ] 0 ∗
    (∃ tail : List UInt8, ⌜tail.length = 8⌝ ∗ n ↦[wms][ out.toNat + 4 ] tail) ∗
    (∃ len', ⌜len' = len ∨ len' = grownLen len (pl + kl)⌝ ∗ heapInv n maxP len' live (F + 1)) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

def cost400None (cfg : WasmConfig) (F : Nat) (pl kl : UInt32) (h : NearState) (k : List UInt8) : Nat :=
  800 * cfg.regularOpCost + cost510 cfg F pl kl + storageReadUse h k (pl + kl).toNat + 20 * cfg.regularOpCost

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- Actual `get_raw` absent path, including storage read and temporary key cleanup. -/
theorem f400_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl kp kl : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key ob : List UInt8)
    (hs : 224 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
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
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ key)) (h.storage (pre ++ key)) ≤ bud)
    (hnone : h.storage (pre ++ key) = none) :
    code400 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f400 Cg
        (pre400 n g ta A gt s out m pp pc pl kp kl idx maxP len live F pre key ob h)
        (fun _ => cost400None cfg F pl kl h (pre ++ key))
        (post400None n g ta A gt s out m pp pc pl kp kl idx maxP len live F pre key
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
  have S548 := fun (q : UInt32) (l1 : Nat) (live1 : List (Nat × Nat)) (ob1 : List UInt8) (hob1 : ob1.length = 12) =>
    StorageReadWrapF.f548_noneF_host (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega)
      Cg gt (s - 32) out q (pl + kl) (by omega) (by omega) hout (pre ++ key) idx maxP l1 live1 F ob1 hob1 h st
      hkl (by omega) hacc hlim hb hz hlink hproof hbud hnone
  clear hacc hlim hb hz hlink hproof hbud
  unfold cost400None
  generalize hK510 : cost510 cfg F pl kl = K510
  generalize hKr : storageReadUse h (pre ++ key) (pl + kl).toNat = Kr at S548
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
  ihave #S := S548 q hl' ((q.toNat, (pl + kl).toNat) :: live) ob hob $$ Hsr
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
  iunfold StorageReadWrapF.post548NoneF at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, Hvt, Hk, HV, Hhost⟩
  subst hrs
  iunfold optVecAtF at HV
  icases HV with ⟨P0, ⟨%tail, %htail, Ptail⟩, Hinv⟩
  -- Free the temporary key after the absent read.
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
    ipureintro; exact ⟨rfl, by simp⟩
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, K0, K4, K8, Hinv⟩
  subst hrs
  rw [List.erase_cons_head] at *
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post400None
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
  iframe P0 Ptail Hhost
  isplitr
  · ipureintro; exact htail
  iexists hl'
  iframe Hinv
  ipureintro; exact hhl

end S400None

end WNear.Binary.LookupMapGet
