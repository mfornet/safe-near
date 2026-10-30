import Bridge.Functions.LookupMapGet399None
import Bridge.Functions.U128From

/-! The absent-account branch of the balance lookup caller. -/

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

/-- `ValidAccountId::as_ref` is the identity on the string pointer. -/
theorem f562_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (v : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f562 Cg
      (fun args => iprop(⌜args = [.i32 v]⌝)) (fun _ => cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 v]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with %hargs
  subst hargs
  simp only [f562]
  mstep
  iframe Hc
  ipureintro; simp [htype]


/-- Code and dependencies of the actual absent-account balance lookup. -/
def code415 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code399 e n maxP inst mi A mx ∗ dropCode inst mi A ∗
    A 562 ↪[wf] FuncInst.wasm types[32]! inst f562 ∗ A 399 ↪[wf] FuncInst.wasm types[31]! inst f399 ∗
    A 566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗ A 321 ↪[wf] FuncInst.wasm types[0]! inst f321)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code415 (GF := GF) e n maxP inst mi A mx) := by
  unfold code415; infer_instance

def pre415 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out m mp pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre key rest ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len ((p.toNat, c.toNat) :: live) F ∗
    prefixAt n mp pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] key ∗
    n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post415 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out mp pp pc pl v p c L : UInt32)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (pre : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    ifaceR n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜LenIn len 2 len'⌝ ∗ heapInv n maxP len' live (F + 3)) ∗
    prefixAt n mp pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
    n ↦[wms][ out.toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual balance lookup returns zero on an absent account. -/
theorem f415_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl v p c L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key rest ob : List UInt8)
    (hs : 352 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
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
    code415 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f415 Cg
        (pre415 n g ta A gt s out m (m + 24) pp pc pl v p c L idx maxP len live F pre key rest ob h)
        (fun _ => 1000 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)))
        (post415 n g ta A gt s out (m + 24) pp pc pl v p c L idx maxP len live F pre
          (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)) := by
  iintro #Hcode
  iunfold code415 at Hcode
  icases Hcode with ⟨#H399, #Hdrop, #F562, #F399, #F566, #F321⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha562 := hm.funcs 562 (by decide)
  have ha399 := hm.funcs 399 (by decide)
  have ha566 := hm.funcs 566 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t4 : types[4]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  unfold cost399None
  generalize hK395 : LookupMapBorsh.cost395 cfg F L = K395
  generalize hK510 : LookupMapLeaves.cost510 cfg F pl (0 + 4 + L) = K510
  generalize hKr : storageReadUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre415 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hkey, Hrest, Ho, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 352) 304 48 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 352 + 304 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 8 40 $$ Fr with ⟨A0, Fr⟩
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega]
  icases stk_split n (s.toNat - 40) 16 24 $$ Fr with ⟨A8, A24⟩
  iunfold stk at A24
  icases A24 with ⟨%ob24, %hob24, A24⟩
  simp only [f415]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f562_spec cfg lim (d + 1) types[32]! (by rfl) inst mi Cg v) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  ihave A24 := memBytes_addr (show s.toNat - 40 + 16 = (s - 48 + 24).toNat by simp [UInt32.toNat_add, h48]; omega) $$ A24
  ihave Lo := stk_addr (show s.toNat - 352 = (s - 48).toNat - 304 by omega) $$ Lo
  mcall (LookupMapGet.f399_none cfg lim (d + 1) types[31]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 48) (s - 48 + 24) (m + 24) pp pc pl v p c L idx maxP len ((p.toNat, c.toNat) :: live) F hF
      pre key ob24 (by omega) (by rw [h48]; omega) hob24 (by simp [UInt32.toNat_add, h48]; omega)
      hpre hkey hL hpl hl0 hpp hv (by omega) hroom h st hacc hlim hb hz hlink hproof hbud hnone)
      using [Hg Lo HI Hvt Hinv Hm Hp Hv Hkey A24 Hhost]
      with (simp only [cost399None, hK395, hK510, hKr]; mstep_norm_full; omega)
  · iunfold pre399
    iframe Hg Lo HI Hvt Hinv Hm Hp Hv Hkey A24 Hhost
    ipureintro; rfl
  simp only [cost399None, hK395, hK510, hKr]
  have hz8 : storeBytes (.i64 0) 8 = bytes32 0 ++ bytes32 0 := by decide
  iunfold post399None at HQ
  simp only [hz8]
  icases HQ with ⟨%hrs, Hg, Lo, HI, Hvt, ⟨%len', %hlen, Hinv⟩, Hm, Hp, Hv, Hkey, A24, Hhost⟩
  subst hrs
  ihave A24 := BorshFT.splitB (n := n) (a := (s - 48 + 24).toNat)
    (b := (s - 48 + 24).toNat + 8) (bytes32 0 ++ bytes32 0)
    ((bytes32 0 ++ bytes32 0) ++ (bytes32 0 ++ bytes32 0)) (by simp [bytes32]) $$ A24
  icases A24 with ⟨Az, Arest⟩
  ihave Az := KeyGet.split64 n (s - 48 + 24).toNat 0 0 $$ Az
  icases Az with ⟨Az0, Az4⟩
  ihave Arest := BorshFT.splitB (n := n) (a := (s - 48 + 24).toNat + 8)
    (b := (s - 48 + 24).toNat + 16) (bytes32 0 ++ bytes32 0) (bytes32 0 ++ bytes32 0) (by simp [bytes32]) $$ Arest
  icases Arest with ⟨Az8, Az16⟩
  ihave Az0 := memBytes_addr (show (s - 48 + 24).toNat = (s - 48).toNat + 24 by simp [UInt32.toNat_add, h48]; omega) $$ Az0
  ihave Az8 := memBytes_addr (show (s - 48 + 24).toNat + 8 = (s - 48).toNat + 32 by simp [UInt32.toNat_add, h48]; omega) $$ Az8
  ihave Az16 := memBytes_addr (show (s - 48 + 24).toNat + 16 = (s - 48 + 40).toNat by simp [UInt32.toNat_add, h48]; omega) $$ Az16
  iunfold stk at A8
  icases A8 with ⟨%ab, %hab, A8⟩
  ihave A8 := memBytes_addr (show s.toNat - 40 = (s - 48 + 8).toNat by simp [UInt32.toNat_add, h48]; omega) $$ A8
  mstep; mstep; mstep; mstep
  mstep [Az8] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep; mstep [Az0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; msel
  mstep; mstep; mstep; mstep [Az16] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep; msel
  simp only [show UInt32.ofNat 0 = 0 from rfl, ↓reduceIte]
  mcall (U128From.f566_spec cfg lim (d + 1) types[4]! rfl inst mi n hn Cg (s - 48 + 8) 0 0 ab hab) using [A8]
  · iunfold U128From.pre
    iframe A8
    ipureintro; rfl
  iunfold U128From.post at HQ
  icases HQ with ⟨%hrs, A8⟩
  subst hrs
  simp only [U128From.u128Bytes, hz8]
  ihave A8 := BorshFT.splitB (n := n) (a := (s - 48 + 8).toNat)
    (b := (s - 48 + 8).toNat + 8) (bytes32 0 ++ bytes32 0) (bytes32 0 ++ bytes32 0) (by simp [bytes32]) $$ A8
  icases A8 with ⟨A80, A88⟩
  ihave A88 := memBytes_addr (show (s - 48 + 8).toNat + 8 = (s - 48 + 16).toNat by simp [UInt32.toNat_add, h48]; omega) $$ A88
  mstep; mstep; mstep; mstep [A88] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep; mstep [A80] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep
  ihave Hv := BorshFT.splitB (n := n) (a := v.toNat) (b := v.toNat + 4) (bytes32 p)
    (bytes32 c ++ bytes32 L) (by simp [bytes32]) $$ Hv
  icases Hv with ⟨V0, Hv⟩
  ihave Hv := KeyGet.split64 n (v.toNat + 4) c L $$ Hv
  icases Hv with ⟨V4, V8⟩
  ihave Blk : AllocInv.block n p.toNat c.toNat $$ [Hkey Hrest]
  · iunfold AllocInv.block
    iexists _
    ihave X := BorshFT.joinB (n := n) (a := p.toNat) (b := p.toNat + key.length) key rest rfl $$ [Hkey Hrest]
    · iframe Hkey Hrest
    iframe X
    ipureintro; simp [hrest]
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len'
      ((p.toNat, c.toNat) :: live) (F + 2) v p c L hc hv) using [V0 V4 V8 Hinv Blk]
  · iunfold pre747
    iframe V0 V4 V8 Hinv Blk
    ipureintro; exact ⟨rfl, List.mem_cons_self⟩
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, V0, V4, V8, Hinv⟩
  subst hrs
  simp only [List.erase_cons_head]
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Q8⟩
  have hq8 : (ob.drop 8).length = 8 := by simp; omega
  ihave Q8 := memBytes_addr (show out.toNat + 8 = (out + 8).toNat by simp [UInt32.toNat_add]; omega) $$ Q8
  mstep; mstep; mstep [Q8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [Q0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mcredits R
  iframe Hc
  iunfold post415
  isplitr
  · ipureintro; simp
  iframe Hg HI Hvt Hm Hp Hhost
  isplitl [Lo A0 A80 A88 Az0 Az4 Az8 Az16]
  · ihave Az16 := BorshFT.stkB (b := s.toNat - 8) (k := 8) _
      (by simp [UInt32.toNat_add, h48]; omega) (by simp [bytes32]) $$ Az16
    ihave Az8 := BorshFT.stkB (b := s.toNat - 16) (k := 8) _ (by omega) (by simp [bytes32]) $$ Az8
    ihave X := BorshFT.stkJ (a := s.toNat - 16) (b := s.toNat - 8) (k1 := 8) (k2 := 8) (k := 16)
      (by omega) rfl $$ [Az8 Az16]
    · iframe Az8 Az16
    ihave Az4 := BorshFT.stkW (b := s.toNat - 20) _ (by simp [UInt32.toNat_add, h48]; omega) $$ Az4
    ihave X := BorshFT.stkJ (a := s.toNat - 20) (b := s.toNat - 16) (k1 := 4) (k2 := 16) (k := 20)
      (by omega) rfl $$ [Az4 X]
    · iframe Az4 X
    ihave Az0 := BorshFT.stkW (b := s.toNat - 24) _ (by omega) $$ Az0
    ihave X := BorshFT.stkJ (a := s.toNat - 24) (b := s.toNat - 20) (k1 := 4) (k2 := 20) (k := 24)
      (by omega) rfl $$ [Az0 X]
    · iframe Az0 X
    ihave A88 := BorshFT.stkB (b := s.toNat - 32) (k := 8) _
      (by simp [UInt32.toNat_add, h48]; omega) (by simp [bytes32]) $$ A88
    ihave X := BorshFT.stkJ (a := s.toNat - 32) (b := s.toNat - 24) (k1 := 8) (k2 := 24) (k := 32)
      (by omega) rfl $$ [A88 X]
    · iframe A88 X
    ihave A80 := BorshFT.stkB (b := s.toNat - 40) (k := 8) _
      (by simp [UInt32.toNat_add, h48]; omega) (by simp [bytes32]) $$ A80
    ihave X := BorshFT.stkJ (a := s.toNat - 40) (b := s.toNat - 32) (k1 := 8) (k2 := 32) (k := 40)
      (by omega) rfl $$ [A80 X]
    · iframe A80 X
    ihave X := BorshFT.stkJ (a := s.toNat - 48) (b := s.toNat - 40) (k1 := 8) (k2 := 40) (k := 48)
      (by omega) rfl $$ [A0 X]
    · iframe A0 X
    ihave Lo := BorshFT.stkA (b := s.toNat - 352) (by omega) $$ Lo
    iapply BorshFT.stkJ (a := s.toNat - 352) (b := s.toNat - 48) (k1 := 304) (k2 := 48) (k := 352) (by omega) rfl
    iframe Lo X
  isplitl [Hinv]
  · iexists len'
    rw [show F + 2 + 1 = F + 3 by omega]
    iframe Hinv
    ipureintro; exact hlen
  isplitl [V0 V4 V8]
  · ihave V := KeyGet.join64 n v.toNat p c $$ [V0 V4]
    · iframe V0 V4
    ihave V := BorshFT.joinB (n := n) (a := v.toNat) (b := v.toNat + 8)
      (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32]) $$ [V V8]
    · iframe V V8
    rw [← List.append_assoc]
    iexact V
  ihave Q8 := memBytes_addr (show (out + 8).toNat = out.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ Q8
  simp only [show UInt64.ofNat (Memory.decodeLE (bytes32 0 ++ bytes32 0)) = 0 by decide]
  iapply BorshFT.joinB (n := n) (a := out.toNat) (b := out.toNat + 8)
    (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ [Q0 Q8]
  iframe Q0 Q8

end Spec
end WNear.Binary.BalanceOfAbsent
