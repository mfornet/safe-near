import Bridge.Functions.BalanceOfAbsent

/-! The absent-account branch through the token balance caller (293). -/
namespace WNear.Binary.BalanceOfAbsent

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.LookupMapGet (code399 pre399 post399None cost399None)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.FmtGrow (mwpi_select')

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def code293 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code415 e n maxP inst mi A mx ∗ A 415 ↪[wf] FuncInst.wasm types[31]! inst f415)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code293 (GF := GF) e n maxP inst mi A mx) := by
  unfold code293; infer_instance

def pre293 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m mp pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key rest ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 384) 384 ∗
    ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len ((p.toNat, c.toNat) :: live) F ∗
    prefixAt n mp pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post293 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out mp pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 384) 384 ∗
    ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜LenIn len 2 len'⌝ ∗ heapInv n maxP len' live (F + 3)) ∗
    prefixAt n mp pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
    n ↦[wms][ out.toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual function 293 returns zero for an absent account. -/
theorem f293_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key rest ob : List UInt8)
    (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
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
    code293 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f293 Cg
        (pre293 n g ta A gt s out m (m + 24) pp pc pl v p c L idx maxP len live F pre key rest ob h)
        (fun _ => 2000 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)))
        (post293 n g ta A gt s out (m + 24) pp pc pl v p c L idx maxP len live F pre
          (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)) := by
  iintro #Hcode
  iunfold code293 at Hcode
  icases Hcode with ⟨#H415, #F415⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code415 at H415
    icases H415 with ⟨-, #Hd, -⟩
    iunfold dropCode at Hd
    icases Hd with ⟨#H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha415 := hm.funcs 415 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  unfold cost399None
  generalize hK395 : LookupMapBorsh.cost395 cfg F L = K395
  generalize hK510 : LookupMapLeaves.cost510 cfg F pl (0 + 4 + L) = K510
  generalize hKr : storageReadUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre293 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hkey, Hrest, Ho, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 384) 352 32 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 384 + 352 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 16 16 $$ Fr with ⟨A0, Fr⟩
  rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega]
  icases stk_split n (s.toNat - 16) 12 4 $$ Fr with ⟨A16, A28⟩
  iunfold stk at A0 A16
  icases A0 with ⟨%ab0, %hab0, A0⟩
  icases A16 with ⟨%ab16, %hab16, A16⟩
  simp only [← List.append_assoc]
  ihave Hv := BorshFT.splitB (n := n) (a := v.toNat) (b := v.toNat + 8)
    (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32]) $$ Hv
  icases Hv with ⟨V0, V8⟩
  ihave V8 := memBytes_addr (show v.toNat + 8 = (v + 8).toNat by simp [UInt32.toNat_add]; omega) $$ V8
  ihave A16 := U128From.memBytes_split n (s.toNat - 16) 8 ab16 (by omega) $$ A16
  icases A16 with ⟨A160, A168⟩
  ihave A168 := memBytes_addr (show s.toNat - 16 + 8 = (s - 32 + 16 + 8).toNat by simp [UInt32.toNat_add, h32]; omega) $$ A168
  ihave A160 := memBytes_addr (show s.toNat - 16 = (s - 32).toNat + 16 by omega) $$ A160
  simp only [f293]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep [V8] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep [A168] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [V0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep [A160] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [VecFromElem.ofNat_decode_pair, VecFromElem.storeBytes_pair64]
  ihave A160 := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by simp [UInt32.toNat_add, h32]; omega) $$ A160
  ihave A16 := BorshFT.joinB (n := n) (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 8)
    (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32]) $$ [A160 A168]
  · ihave A168 := memBytes_addr (show (s - 32 + 16 + 8).toNat = (s - 32 + 16).toNat + 8 by simp [UInt32.toNat_add, h32]; omega) $$ A168
    iframe A160 A168
  ihave V8 := memBytes_addr (show (v + 8).toNat = v.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ V8
  ihave Hv := BorshFT.joinB (n := n) (a := v.toNat) (b := v.toNat + 8)
    (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32]) $$ [V0 V8]
  · iframe V0 V8
  simp only [List.append_assoc]
  ihave A0 := memBytes_addr (show s.toNat - 32 = (s - 32).toNat by omega) $$ A0
  ihave Lo := stk_addr (show s.toNat - 384 = (s - 32).toNat - 352 by omega) $$ Lo
  mstep; mstep; mstep; mstep; mstep
  mcall (f415_none cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 32) (s - 32) m pp pc pl (s - 32 + 16) p c L idx maxP len live F hF pre key rest ab0
      (by omega) (by rw [h32]; omega) hab0 (by omega) hpre hkey hrest hc hL hpl hl0 hpp
      (by simp [UInt32.toNat_add, h32]; omega) hp hroom h st hacc hlim hb hz hlink hproof hbud hnone)
      using [Hg Lo HI Hvt Hinv Hm Hp A16 Hkey Hrest A0 Hhost]
      with (simp only [cost399None, hK395, hK510, hKr]; mstep_norm_full; omega)
  · iunfold pre415
    iframe Hg Lo HI Hvt Hinv Hm Hp A16 Hkey Hrest A0 Hhost
    ipureintro; rfl
  simp only [cost399None, hK395, hK510, hKr]
  iunfold post415 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, ⟨%len', %hlen, Hinv⟩, Hm, Hp, A16, A0, Hhost⟩
  subst hrs
  ihave A0 := BorshFT.splitB (n := n) (a := (s - 32).toNat) (b := (s - 32).toNat + 8)
    (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ A0
  icases A0 with ⟨B0, B8⟩
  ihave B8 := memBytes_addr (show (s - 32).toNat + 8 = (s - 32 + 8).toNat by simp [UInt32.toNat_add, h32]; omega) $$ B8
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Q8⟩
  ihave Q8 := memBytes_addr (show out.toNat + 8 = (out + 8).toNat by simp [UInt32.toNat_add]; omega) $$ Q8
  mstep; mstep [B0] with (simp [loadWidth, NumType.byteWidth]); mstep
  mstep; mstep; mstep; mstep; mstep [B8] with (simp [loadWidth, NumType.byteWidth])
  mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post293
  isplitr
  · ipureintro; simp
  iframe Hg HI Hvt Hm Hp Hhost
  isplitl [Lo B0 B8 A16 A28]
  · ihave A16 := BorshFT.stkB (b := s.toNat - 16) (k := 12) _
      (by simp [UInt32.toNat_add, h32]; omega) (by simp [bytes32]) $$ A16
    ihave A28 := stk_addr (show s.toNat - 16 + 12 = s.toNat - 4 by omega) $$ A28
    ihave X := BorshFT.stkJ (a := s.toNat - 16) (b := s.toNat - 4) (k1 := 12) (k2 := 4) (k := 16)
      (by omega) rfl $$ [A16 A28]
    · iframe A16 A28
    ihave B8 := BorshFT.stkB (b := s.toNat - 24) (k := 8) _
      (by simp [UInt32.toNat_add, h32]; omega) (by rfl) $$ B8
    ihave X := BorshFT.stkJ (a := s.toNat - 24) (b := s.toNat - 16) (k1 := 8) (k2 := 16) (k := 24)
      (by omega) rfl $$ [B8 X]
    · iframe B8 X
    ihave B0 := BorshFT.stkB (b := s.toNat - 32) (k := 8) _ (by omega) (by rfl) $$ B0
    ihave X := BorshFT.stkJ (a := s.toNat - 32) (b := s.toNat - 24) (k1 := 8) (k2 := 24) (k := 32)
      (by omega) rfl $$ [B0 X]
    · iframe B0 X
    ihave Lo := BorshFT.stkA (b := s.toNat - 384) (by omega) $$ Lo
    iapply BorshFT.stkJ (a := s.toNat - 384) (b := s.toNat - 32) (k1 := 352) (k2 := 32) (k := 384) (by omega) rfl
    iframe Lo X
  isplitl [Hinv]
  · iexists len'
    iframe Hinv
    ipureintro; exact hlen
  isplitl [Hv]
  · iexact Hv
  ihave Q8 := memBytes_addr (show (out + 8).toNat = out.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ Q8
  simp only [show UInt64.ofNat (Memory.decodeLE (storeBytes (.i64 0) 8)) = 0 by decide]
  iapply BorshFT.joinB (n := n) (a := out.toNat) (b := out.toNat + 8)
    (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ [Q0 Q8]
  iframe Q0 Q8

end Spec
end WNear.Binary.BalanceOfAbsent
