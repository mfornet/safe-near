import Bridge.Functions.LookupMapGetNone

/-! Absent-key path of `LookupMap::get` (399). -/
namespace WNear.Binary.LookupMapGet

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (code392 prefixAt pre392 post392 cost510)
open WNear.Binary.LookupMapBorsh (code395 pre395 post395 cost395 code398 pre398 post398)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step lenIn_zero lenIn_mono)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateWrite (stkJ stkL memBytes_disjoint)

section S399None
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def post399None (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗ ifaceR n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜LenIn len 2 len'⌝ ∗ heapInv n maxP len' live (F + 2)) ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ out.toNat ] (storeBytes (.i64 0) 8 ++ (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8)) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

def cost399None (cfg : WasmConfig) (F : Nat) (pl L : UInt32) (h : NearState) (k : List UInt8) : Nat :=
  3000 * cfg.regularOpCost + cost395 cfg F L + cost510 cfg F pl (0 + 4 + L) +
    storageReadUse h k (pl + (0 + 4 + L)).toNat + 20 * cfg.regularOpCost

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- Actual absent `LookupMap::get` path, including both temporary key drops. -/
theorem f399_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key ob : List UInt8)
    (hs : 304 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 24) (hout : out.toNat + 24 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
    (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 2 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hnone : h.storage (pre ++ (bytes32 L ++ key)) = none) :
    code399 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f399 Cg
        (pre399 n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key ob h)
        (fun _ => cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)))
        (post399None n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key
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
  have hKL : (bytes32 L ++ key).length = (0 + 4 + L).toNat := by simp [bytes32, hkey]; omega
  have hplk : (pl + (0 + 4 + L)).toNat = pl.toNat + (4 + L.toNat) := by simp [UInt32.toNat_add]; omega
  unfold cost399None
  generalize hK395 : cost395 cfg F L = K395
  generalize hKr : storageReadUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  generalize hK510 : cost510 cfg F pl (0 + 4 + L) = K510
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
  mcall (LookupMapGet.f400_none cfg lim (d + 1) types[45]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 80) (s - 80 + 32) m pp pc pl q1 (0 + 4 + L) idx maxP l1
      ((q1.toNat, 1024) :: live) F hF pre (bytes32 L ++ key) obb
      (by omega) (by rw [h80]; omega) hobb (by simp [UInt32.toNat_add, h80]; omega) hpre hKL
      (by rw [hk4]; omega) hl0 hpp (by rw [hk4]; omega)
      (roomFor_ofK _ (by rw [hplk]; omega) hroom hL1 (by omega))
      h st hacc hlim hb hz hlink hproof hbud hnone)
      using [Hg Lo HI Hvt Hinv Hm Hp Wk O Hhost]
      with (simp only [cost400None, hKr, hK510]; mstep_norm_full; omega)
  · iunfold pre400
    iframe Hg Lo HI Hvt Hinv Hm Hp Wk O Hhost
    ipureintro; rfl
  simp only [cost400None, hKr, hK510]
  iunfold post400None at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, Hm, Hp, Wk, P0, ⟨%tail, %htail, Ptail⟩,
    ⟨%l2, %hl2, Hinv⟩, Hhost⟩
  subst hrs
  have hsz : (pl + (0 + 4 + L)).toNat ≤ 4096 := by rw [hplk]; omega
  have hL2 : LenIn len 2 l2 := lenIn_step _ hsz hL1 hl2
  ihave P0 := memBytes_addr (show (s - 80 + 32).toNat = (s - 80).toNat + 32 by simp [UInt32.toNat_add, h80]; omega) $$ P0
  mstep; mstep; mstep; mstep [P0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep
  mstep; mstep; mstep
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
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP l2
      ((q1.toNat, 1024) :: live) (F + 1) (s - 80 + 48) q1 1024 (0 + 4 + L)
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
  mstep; mstep; mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 80 + 80 = s by simp]
  mcredits R
  mpay with (simp [htype])
  iframe Hc
  iunfold post399None
  isplitr
  · ipureintro; simp
  iframe Hg HI Hvt Hm Hp Hv Hkey
  isplitl [Lo T D2 D10 D14 P0 Ptail U44 K0 K4 K8 U60 Cp U76]
  · ihave Cp := BorshFT.stkB (b := s.toNat - 16) (k := 12) _ (by omega) hcb $$ Cp
    ihave X := BorshFT.stkJ (a := s.toNat - 16) (b := s.toNat - 4) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [Cp U76]
    · iframe Cp U76
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
    ihave Ptail := BorshFT.stkB (b := s.toNat - 44) (k := 8) _ (by simp [UInt32.toNat_add, h80]; omega) htail $$ Ptail
    ihave X := BorshFT.stkJ (a := s.toNat - 44) (b := s.toNat - 36) (k1 := 8) (k2 := 36) (k := 44) (by omega) rfl $$ [Ptail X]
    · iframe Ptail X
    ihave P0 := BorshFT.stkW (b := s.toNat - 48) _ (by omega) $$ P0
    ihave X := BorshFT.stkJ (a := s.toNat - 48) (b := s.toNat - 44) (k1 := 4) (k2 := 44) (k := 48) (by omega) rfl $$ [P0 X]
    · iframe P0 X
    ihave D14 := BorshFT.stkW (b := s.toNat - 52) _ (by omega) $$ D14
    ihave X := BorshFT.stkJ (a := s.toNat - 52) (b := s.toNat - 48) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [D14 X]
    · iframe D14 X
    ihave D10 := BorshFT.stkW (b := s.toNat - 56) _ (by omega) $$ D10
    ihave X := BorshFT.stkJ (a := s.toNat - 56) (b := s.toNat - 52) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [D10 X]
    · iframe D10 X
    ihave D2 := BorshFT.stkB (b := s.toNat - 64) (k := 8) _ (by omega) hd2b $$ D2
    ihave X := BorshFT.stkJ (a := s.toNat - 64) (b := s.toNat - 56) (k1 := 8) (k2 := 56) (k := 64) (by omega) rfl $$ [D2 X]
    · iframe D2 X
    ihave T := BorshFT.stkB (b := s.toNat - 80) (k := 16) _ (by omega) htb $$ T
    ihave X := BorshFT.stkJ (a := s.toNat - 80) (b := s.toNat - 64) (k1 := 16) (k2 := 64) (k := 80) (by omega) rfl $$ [T X]
    · iframe T X
    ihave Lo := BorshFT.stkA (b := s.toNat - 304) (by omega) $$ Lo
    iapply BorshFT.stkJ (a := s.toNat - 304) (b := s.toNat - 80) (k1 := 224) (k2 := 80) (k := 304) (by omega) rfl
    iframe Lo X
  isplitl [Hinv]
  · iexists l2
    rw [show F + 1 + 1 = F + 2 by omega]
    iframe Hinv
    ipureintro; exact hL2
  isplitl [Q0 Q8 Q16]
  · ihave Q16 := memBytes_addr (show (out + 16).toNat = out.toNat + 8 + 8 by omega) $$ Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat + 8) (b := out.toNat + 16)
      (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ [Q8 Q16]
    · iframe Q8 Q16
    ihave X := BorshFT.joinB (n := n) (a := out.toNat) (b := out.toNat + 8)
      (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) (by rfl) $$ [Q0 X]
    · iframe Q0 X
    iexact X
  iexact Hhost

end S399None
end WNear.Binary.LookupMapGet
