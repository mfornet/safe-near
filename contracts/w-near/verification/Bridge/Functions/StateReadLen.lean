import Bridge.Functions.StateReadModel

/-!
# `env::state_read` (219), with the memory length it leaves

`StateRead.f219_spec` and `StateReadModel.f219_spec_model` with a postcondition that also says
how the memory length `len'` of the heap `state_read` leaves relates to the length `len` it
started from (`LenStep`): `read_register`'s buffer may grow memory once (`grownLen len vlen`),
then the prefix's buffer once more (`grownLen len1 plen`). A later allocation's room
(`roomFor`) is stated at that length. The proof is `f219_spec`'s, with the two length facts
it already has (`hlen1`, `hlen2`) kept in the postcondition.
-/

namespace WNear.Binary.StateReadLen

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshLeaves WNear.Binary.BorshInt WNear.Binary.BorshVec WNear.Binary.BorshBytes
open WNear.Binary.BorshFT WNear.Binary.BorshContract WNear.Binary.DropVec WNear.Binary.StateRead
open WNear.Binary.StorageReadWrap (srCode pre548 post548 f548_spec_host costS)
open WNear.Binary.ReadRegister (optVecAt RegOk ifaceR)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro pair64 storeBytes_pair64
  ofNat_decode_pair roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.StateReadModel (contractBytes header_eq ftHead_eq accountsPrefix_length decode_u32_prefix
  header_length)

/-- The memory length after `state_read`: at most two grows, for the value's buffer (`vlen`
bytes) and for the prefix's (`plen`). -/
def LenStep (len vlen plen len' : Nat) : Prop :=
  ∃ len1, (len1 = len ∨ len1 = grownLen len (UInt32.ofNat vlen)) ∧
    (len' = len1 ∨ len' = grownLen len1 (UInt32.ofNat plen))

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `StateRead.post219` with the length step. -/
def post219L (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (pre b0 b1 c0 : List UInt8) (vlen : Nat) (h : NearState) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
    (∃ (pv p : UInt32) (pad : List UInt8) (len' : Nat), ⌜pad.length = 4 ∧ LenStep len vlen pre.length len'⌝ ∗
      n ↦[wms][ out.toNat ] (ftHead b0 b1 c0 p pre ++ pad) ∗
      heapInv n maxP len' (((p.toNat, pre.length) :: (pv.toNat, vlen) :: live).erase (pv.toNat, vlen)) 2 ∗
      n ↦[wms][ p.toNat ] pre) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- **`env::state_read::<Contract>`** (function 219 of `contract.wasm`) on a host whose storage at
`"STATE"` is `hd ++ pre ++ b0 ++ b1 ++ c0`, the Borsh encoding of a `Contract` (prefix `pre`,
`total_supply` `b0 ++ b1`, `account_storage_usage` `c0`): `Some(contract)` at `out`. -/
theorem f219_spec_len (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 40 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 40) (h : NearState)
    (hd4 pre b0 b1 c0 : List UInt8) (hhd : hd4.length = 4) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
    (hc0 : c0.length = 8) (hL : Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length)
    (hv : h.storage StateRead.stateKey = some (stateBytes hd4 pre b0 b1 c0))
    (hv28 : (stateBytes hd4 pre b0 b1 c0).length < 2 ^ 28)
    (hroom1 : roomFor len maxP (UInt32.ofNat (stateBytes hd4 pre b0 b1 c0).length))
    (hroom2 : ∀ len', len' = len ∨ len' = grownLen len (UInt32.ofNat (stateBytes hd4 pre b0 b1 c0).length) →
      roomFor len' maxP (UInt32.ofNat pre.length))
    (st : Near.TrieOverlay.State)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen StateRead.stateKey.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage StateRead.stateKey = viewVal st (contractKey h.context.currentAccountId StateRead.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen (stateBytes hd4 pre b0 b1 c0).length = true) :
    stateCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f219 Cg
        (pre219 n g ta A gt s out idx maxP len live ob h)
        (fun _ => 105 * cfg.regularOpCost +
          (40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5) +
            costS cfg h (some (stateBytes hd4 pre b0 b1 c0))) +
          cost161 cfg (UInt32.ofNat pre.length) + 726 * cfg.regularOpCost + 334 * cfg.regularOpCost)
        (post219L n g ta A gt s out idx maxP len live pre b0 b1 c0 (stateBytes hd4 pre b0 b1 c0).length h
          (StorageReadPost h StateRead.stateKey 0 st)) := by
  iintro #Hcode
  ihave #Hcode' := Hcode
  iunfold stateCode at Hcode'
  icases Hcode' with ⟨#Hsr, #Hsl, #Hdr, #H548, #H779, #H68⟩
  ihave #Hsl' := Hsl
  iunfold sliceCode, contractCode, ftCode, bytesCode, rdCode at Hsl'
  icases Hsl' with ⟨⟨⟨⟨⟨#Hi, -⟩, -⟩, -⟩, -, #H951, -⟩, #H161⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha548 := hm.funcs 548 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha161 := hm.funcs 161 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h96 : (s - 96).toNat = s.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 96 + 8).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, h96]; omega
  have e24 : (s - 96 + 24).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, h96]; omega
  have e40 : (s - 96 + 40).toNat = s.toNat - 56 := by simp [UInt32.toNat_add, h96]; omega
  have e48 : (s - 96 + 40 + 8).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, h96]; omega
  generalize hV : stateBytes hd4 pre b0 b1 c0 = v at hv hv28 hroom1 hroom2 hreg ⊢
  have hvl : v.length = 4 + pre.length + 24 := by rw [← hV]; simp [stateBytes, hhd, hb0, hb1, hc0]; omega
  have hok : RegOk maxP len (h.storage StateRead.stateKey) := by
    rw [hv]; exact ⟨by omega, hv28, hroom1⟩
  have S548 := f548_spec_host (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 96) (s - 96 + 8) 1049788 5 (by omega) (by omega) (by omega) StateRead.stateKey idx maxP len live
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre219 at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hk, Hhost⟩
  subst hargs
  icases stkSp 496 96 rfl $$ Hs with ⟨Lo, Hs⟩
  icases stkSp 8 88 rfl $$ Hs with ⟨F0, Hs⟩
  icases stkSp 12 76 rfl $$ Hs with ⟨F8, Hs⟩
  icases stkSp 4 72 rfl $$ Hs with ⟨F20, Hs⟩
  icases stkSp 12 60 rfl $$ Hs with ⟨F24, Hs⟩
  icases stkSp 4 56 rfl $$ Hs with ⟨F36, Hs⟩
  icases stkSp 4 52 rfl $$ Hs with ⟨F40, Hs⟩
  icases stkSp 4 48 rfl $$ Hs with ⟨F44, F48⟩
  icases stk_bytes' $$ F0 with ⟨%f0, %hf0, F0⟩
  icases stk_bytes' $$ F8 with ⟨%f8, %hf8, F8⟩
  icases stk_bytes' $$ F24 with ⟨%f24, %hf24, F24⟩
  icases stk_bytes' $$ F40 with ⟨%f40, %hf40, F40⟩
  icases stk_bytes' $$ F48 with ⟨%f48, %hf48, F48⟩
  icases stkSp 304 192 rfl $$ Lo with ⟨LoA, LoB⟩
  simp only [f219]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  have S := S548 f8 hf8 h st rfl (by decide) hacc hlim hb hz hlink hproof (fun v' hv' => by
      rw [hv] at hv'; cases hv'; exact hreg) hok
  rw [hv] at S
  mcall S using [Hg HI LoB Hvt Hinv F8 Hk Hhost]
  · iunfold pre548
    ihave LoB := stkA (a := s.toNat - 592 + 304) (b := (s - 96).toNat - 192) (by omega) $$ LoB
    ihave F8 := memBytes_addr (a := s.toNat - 592 + 496 + 8) (b := (s - 96 + 8).toNat) (by omega) $$ F8
    ihave Hk := memBytes_addr (a := 1049788) (b := (1049788 : UInt32).toNat) rfl $$ Hk
    iframe Hg HI LoB Hvt Hinv F8 Hk Hhost
    ipureintro; rfl
  iunfold post548 at HQ
  icases HQ with ⟨%hrs, Hg, HI, LoB, Hvt, Hk, OV, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  rw [hv]
  simp only [optVecAt]
  icases OV with ⟨%pv, O8, O12, O16, %len1, %⟨hpv, hlen1⟩, Hinv, Hv⟩
  ihave J1 : (stk n (s.toNat - 592 + 496 + 8 + 12) 4 ∗ stk n (s.toNat - 592 + 496 + 8 + 12 + 4 + 12) 4 ∗
      stk n (s.toNat - 592 + 496 + 8 + 12 + 4 + 12 + 4 + 4) 4 ∗ ifaceR n ta A ∗ n ↦[wms][ (1049788 : UInt32).toNat ] StateRead.stateKey ∗
      mhostPt h') $$ [F20 F36 F44 HI Hk Hhost]
  · iframe F20 F36 F44 HI Hk Hhost
  ihave O8 := memBytes_addr (a := (s - 96 + 8).toNat) (b := s.toNat - 88) (by omega) $$ O8
  ihave O12 := memBytes_addr (a := (s - 96 + 8).toNat + 4) (b := s.toNat - 84) (by omega) $$ O12
  ihave O16 := memBytes_addr (a := (s - 96 + 8).toNat + 8) (b := s.toNat - 80) (by omega) $$ O16
  ihave F24 := U128From.memBytes_split n _ 8 f24 (by omega) $$ F24
  icases F24 with ⟨F24, F32⟩
  ihave F24 := memBytes_addr (b := s.toNat - 72) (by omega) $$ F24
  ihave F32 := memBytes_addr (b := s.toNat - 64) (by omega) $$ F32
  mstep; mstep; mstep
  mstep; mstep [O8]; mstep with simp [hpv]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [O16]; mstep [F32]
  ihave O8 := join64' (a := s.toNat - 88) (b := s.toNat - 84) pv _ (by omega) $$ [O8 O12]
  · iframe O8 O12
  mstep; mstep; mstep [O8]
  rw [ofNat_decode_pair]
  mstep [F24]
  rw [storeBytes_pair64]
  ihave V := joinB (a := s.toNat - 72) (b := s.toNat - 64) (bytes32 pv ++ bytes32 (UInt32.ofNat v.length)) (bytes32 (UInt32.ofNat v.length)) (by simp; omega) $$ [F24 F32]
  · iframe F24 F32
  mstep; mstep; mstep; mstep
  mcall (VecDerefAuto.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 96) (s - 96 + 24) f0
      (bytes32 pv ++ bytes32 (UInt32.ofNat v.length) ++ bytes32 (UInt32.ofNat v.length)) hf0 (by simp))
    using [F0 V]
  · iunfold VecDeref.pre
    ihave F0 := memBytes_addr (b := (s - 96).toNat) (by omega) $$ F0
    ihave V := memBytes_addr (b := (s - 96 + 24).toNat) (by omega) $$ V
    iframe F0 V
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, F0, V⟩
  subst hrs
  ihave J2 : (n ↦[i32][ s.toNat - 80 ] UInt32.ofNat v.length ∗
      n ↦[wms][ s.toNat - 88 ] (bytes32 pv ++ bytes32 (UInt32.ofNat v.length))) $$ [O16 O8]
  · iframe O16 O8
  have hvb : ∀ (a b : UInt32), (bytes32 a ++ (bytes32 b ++ bytes32 b)).take 4 ++ (bytes32 a ++ (bytes32 b ++ bytes32 b)).drop 8
      = bytes32 a ++ bytes32 b := by
    intro a b; simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  ihave F0 := memBytes_addr (b := s.toNat - 96) (by omega) $$ F0
  icases split64' (a := s.toNat - 96) (b := s.toNat - 92) pv _ (by omega) $$ F0 with ⟨F0, F4⟩
  ihave Hinv := AllocZeroed.heapInv_bound n maxP len1 _ 1 $$ Hinv
  icases Hinv with ⟨%⟨hbd, hl32⟩, Hinv⟩
  have hpvb := hbd pv.toNat v.length (by simp)
  have hLn : (UInt32.ofNat v.length).toNat = v.length := by simp; omega
  have hvl' := hvl
  rw [← hV] at hvl'
  icases splitV (n := n) pv hhd hb0 hb1 hV $$ Hv with ⟨Hd4, Hpre, B0, B1, C0⟩
  ihave F48 := U128From.memBytes_split n _ 40 f48 (by omega) $$ F48
  icases F48 with ⟨F48, F88⟩
  ihave Lo := stkJ (a := s.toNat - 592) (b := (s - 96).toNat - 192) (k1 := 304) (k2 := 192) (k := 496) (by omega) rfl
    $$ [LoA LoB]
  · iframe LoA LoB
  mstep; mstep; mstep; mstep; mstep [F0]; mstep; mstep [F4]
  mcall (f161_spec cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 96) (s - 96 + 40) pv
      (UInt32.ofNat v.length) idx maxP len1 ((pv.toNat, v.length) :: live) f40 (List.take 40 f48) hd4 pre b0 b1 c0
      hf40 (by simp; omega) hhd hb0 hb1 hc0 hL hL0 (by omega) (hroom2 len1 hlen1) (by omega) (by omega)
      (by rw [hLn]; omega) (by omega) (by omega))
    using [Hg Lo Hvt Hinv F40 F48 Hd4 Hpre B0 B1 C0]
  · iunfold pre161
    ihave Lo := stkA (b := (s - 96).toNat - 496) (by omega) $$ Lo
    ihave F40 := memBytes_addr (b := (s - 96 + 40).toNat) (by omega) $$ F40
    ihave F48 := memBytes_addr (b := (s - 96 + 40).toNat + 8) (by omega) $$ F48
    iframe Hg Lo Hvt Hinv F40 F48 Hd4 Hpre B0 B1 C0
    ipureintro; rfl
  iunfold post161 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, T40, CA, Hd4, Hpre, B0, B1, C0⟩
  subst hrs
  iunfold contractAt at CA
  icases CA with ⟨%p, %pad, %hpad, FT, HW⟩
  have hft : (ftHead b0 b1 c0 p pre ++ pad).length = 40 := by
    rw [List.length_append, ftHead_length b0 b1 c0 p pre hb0 hb1 hc0, hpad]
  mstep; mstep [T40]; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (memcpy_spec cfg lim (d + 1) inst mi n hn Cg out (s - 96 + 40 + 8) 40 (by omega) (by omega) ob
      (ftHead b0 b1 c0 p pre ++ pad) hob hft (by omega) (by omega)) using [Ho FT]
  · iunfold MemCpy.pre
    ihave FT := memBytes_addr (b := (s - 96 + 40 + 8).toNat) (by omega) $$ FT
    iframe Ho FT
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho, FT⟩
  subst hrs
  iunfold heapWith at HW
  icases HW with ⟨%len2, %⟨hp0, hlen2⟩, Hinv, Hpb⟩
  ihave Hv := joinV (n := n) pv hhd hb0 hb1 hV $$ [Hd4 Hpre B0 B1 C0]
  · iframe Hd4 Hpre B0 B1 C0
  ihave V := memBytes_addr (b := s.toNat - 72) (by omega) $$ V
  icases splitB (a := s.toNat - 72) (b := s.toNat - 68) (bytes32 pv) _ (by simp; omega) $$ V with ⟨V0, V⟩
  icases split64' (a := s.toNat - 68) (b := s.toNat - 64) _ _ (by omega) $$ V with ⟨V4, V8⟩
  iapply (tail219 cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s out (by omega) maxP len2
    ((p.toNat, pre.length) :: (pv.toNat, v.length) :: live) pv v hLn (by omega) (by simp) R)
  iframe Hdr H68 Hi Hg V0 V4 V8 Hinv Hv
  isplitl [Hc]
  · iapply credits_mono (by omega) $$ Hc
  iintro ⟨Hc, Hg, V0, V4, V8, Hinv⟩
  dsimp only
  icases J1 with ⟨F20, F36, F44, HI, Hk, Hhost⟩
  icases J2 with ⟨O16, O8⟩
  ihave V0 := stkW (b := s.toNat - 72) _ (by omega) $$ V0
  ihave V4 := stkW (b := s.toNat - 68) _ (by omega) $$ V4
  ihave V8 := stkW (b := s.toNat - 64) _ (by omega) $$ V8
  ihave F0 := stkW (b := s.toNat - 96) _ rfl $$ F0
  ihave F4 := stkW (b := s.toNat - 92) _ rfl $$ F4
  ihave O8 := stkB (b := s.toNat - 88) (k := 8) _ rfl (by simp) $$ O8
  ihave O16 := stkW (b := s.toNat - 80) _ rfl $$ O16
  ihave F20 := stkA (b := s.toNat - 76) (by omega) $$ F20
  ihave F36 := stkA (b := s.toNat - 60) (by omega) $$ F36
  ihave T40 := stkW (b := s.toNat - 56) _ (by omega) $$ T40
  ihave F44 := stkA (b := s.toNat - 52) (by omega) $$ F44
  ihave FT := stkB (b := s.toNat - 48) (k := 40) _ (by omega) hft $$ FT
  ihave F88 := stkB (b := s.toNat - 8) (k := 8) _ (by omega) (by simp; omega) $$ F88
  ihave Lo := stkA (b := s.toNat - 592) (by omega) $$ Lo
  ihave FT := stkJ (a := s.toNat - 48) (b := s.toNat - 8) (k1 := 40) (k2 := 8) (k := 48) (by omega) rfl $$ [FT F88]
  · iframe FT F88
  ihave F44 := stkJ (a := s.toNat - 52) (b := s.toNat - 48) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [F44 FT]
  · iframe F44 FT
  ihave T40 := stkJ (a := s.toNat - 56) (b := s.toNat - 52) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [T40 F44]
  · iframe T40 F44
  ihave F36 := stkJ (a := s.toNat - 60) (b := s.toNat - 56) (k1 := 4) (k2 := 56) (k := 60) (by omega) rfl $$ [F36 T40]
  · iframe F36 T40
  ihave V8 := stkJ (a := s.toNat - 64) (b := s.toNat - 60) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [V8 F36]
  · iframe V8 F36
  ihave V4 := stkJ (a := s.toNat - 68) (b := s.toNat - 64) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [V4 V8]
  · iframe V4 V8
  ihave V0 := stkJ (a := s.toNat - 72) (b := s.toNat - 68) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [V0 V4]
  · iframe V0 V4
  ihave F20 := stkJ (a := s.toNat - 76) (b := s.toNat - 72) (k1 := 4) (k2 := 72) (k := 76) (by omega) rfl $$ [F20 V0]
  · iframe F20 V0
  ihave O16 := stkJ (a := s.toNat - 80) (b := s.toNat - 76) (k1 := 4) (k2 := 76) (k := 80) (by omega) rfl $$ [O16 F20]
  · iframe O16 F20
  ihave O8 := stkJ (a := s.toNat - 88) (b := s.toNat - 80) (k1 := 8) (k2 := 80) (k := 88) (by omega) rfl $$ [O8 O16]
  · iframe O8 O16
  ihave F4 := stkJ (a := s.toNat - 92) (b := s.toNat - 88) (k1 := 4) (k2 := 88) (k := 92) (by omega) rfl $$ [F4 O8]
  · iframe F4 O8
  ihave F0 := stkJ (a := s.toNat - 96) (b := s.toNat - 92) (k1 := 4) (k2 := 92) (k := 96) (by omega) rfl $$ [F0 F4]
  · iframe F0 F4
  ihave Stk := stkJ (a := s.toNat - 592) (b := s.toNat - 96) (k1 := 496) (k2 := 96) (k := 592) (by omega) rfl $$ [Lo F0]
  · iframe Lo F0
  iframe Hc
  iunfold post219L
  iframe Hg HI Stk Hvt Hk
  isplitr
  · ipureintro; simp [htype]
  isplitl [Ho Hinv Hpb]
  · iexists pv, p, pad, len2
    iframe Ho Hinv Hpb
    ipureintro; exact ⟨hpad, len1, hlen1, hlen2⟩
  iexists h'
  iframe Hhost
  ipureintro; exact hq

/-- After `state_read` on the model state `s`, with the length step. -/
def postModelL (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (st : UInt32) (out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (s : WNear.State) (h : NearState) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 st⟩ ∗ ifaceR n ta A ∗ stk n (st.toNat - 592) 592 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
    (∃ (pv p : UInt32) (pad : List UInt8) (len' : Nat), ⌜pad.length = 4 ∧ LenStep len 29 1 len'⌝ ∗
      n ↦[wms][ out.toNat ] (contractBytes s p ++ pad) ∗
      heapInv n maxP len' (((p.toNat, 1) :: (pv.toNat, 29) :: live).erase (pv.toNat, 29)) 2 ∗
      n ↦[wms][ p.toNat ] WNear.accountsPrefix) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxRecDepth 100000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `StateReadModel.f219_spec_model` with the length step. -/
theorem f219_spec_model_len (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out : UInt32) (hs : 592 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (hout : out.toNat + 40 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 40) (h : NearState) (s : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header s))
    (hroom1 : roomFor len maxP 29)
    (hroom2 : ∀ len', len' = len ∨ len' = grownLen len 29 → roomFor len' maxP 1)
    (st : Near.TrieOverlay.State)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true) :
    stateCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f219 Cg
        (pre219 n g ta A gt sp out idx maxP len live ob h)
        (fun _ => 105 * cfg.regularOpCost +
          (40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5) +
            costS cfg h (some (WNear.header s))) +
          cost161 cfg 1 + 726 * cfg.regularOpCost + 334 * cfg.regularOpCost)
        (postModelL n g ta A gt sp out idx maxP len live s h (StorageReadPost h StateRead.stateKey 0 st)) := by
  rw [← stateKey_eq] at hv hlink hproof
  have hl := header_length s
  have e := f219_spec_len (GF := GF) cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt sp out hs hal hout idx
    maxP len live ob hob h (WNear.Borsh.u32 WNear.accountsPrefix.length) WNear.accountsPrefix
    ((WNear.Borsh.u128 s.totalSupply).take 8) ((WNear.Borsh.u128 s.totalSupply).drop 8)
    (WNear.Borsh.u64 s.accountStorageUsage) (by simp [NearSdk.Borsh.u32])
    (by simp [NearSdk.Borsh.u128]) (by simp [NearSdk.Borsh.u128]) (by simp [NearSdk.Borsh.u64])
    decode_u32_prefix (by rw [accountsPrefix_length]; decide) (by rw [← header_eq]; exact hv)
    (by rw [← header_eq, hl]; decide) (by rw [← header_eq, hl]; exact hroom1)
    (by rw [← header_eq, hl, accountsPrefix_length]; exact hroom2) st hacc hlim hb hz hlink hproof
    (by rw [← header_eq, hl]; exact hreg)
  rw [← header_eq, accountsPrefix_length] at e
  have hpost : post219L (GF := GF) n g ta A gt sp out idx maxP len live WNear.accountsPrefix
      ((WNear.Borsh.u128 s.totalSupply).take 8) ((WNear.Borsh.u128 s.totalSupply).drop 8)
      (WNear.Borsh.u64 s.accountStorageUsage) (WNear.header s).length h (StorageReadPost h StateRead.stateKey 0 st) =
      postModelL n g ta A gt sp out idx maxP len live s h (StorageReadPost h StateRead.stateKey 0 st) := by
    funext args rs
    simp only [post219L, postModelL, ftHead_eq, hl, accountsPrefix_length]
  rw [hpost] at e
  exact e

end Spec

end WNear.Binary.StateReadLen
