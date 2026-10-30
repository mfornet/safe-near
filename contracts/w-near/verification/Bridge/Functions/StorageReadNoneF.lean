import Bridge.Functions.StorageReadWrapF

/-! The absent-key `storage_read` path preserves an arbitrary allocator bound. -/

namespace WNear.Binary.StorageReadWrapF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ReadRegister
open WNear.Binary.ReadRegisterF (rrCodeF optVecAtF)
open WNear.Binary.StorageRead (foundU64 storageReadResult_eq f459_spec)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def post548NoneF (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out kp : UInt32) (key : List UInt8)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 192) 192 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ kp.toNat ] key ∗
    optVecAtF n maxP len live F out none ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Absent storage read, retaining the exact allocator state and host postcondition. -/
theorem f548_noneF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (_hout : out.toNat + 12 ≤ 2 ^ 32) (key : List UInt8) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (Q : NearState → Prop) (kh : Nat) (hsk : h.storage key = none)
    (hc : ReadContractP (metered e "storage_read" storageReadFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 0] (storageReadResult (h.storage key))
      kp.toNat key kh Cg) :
    srCodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f548 Cg
        (pre548F n g ta A gt s out kp kl key idx maxP len live F ob h)
        (fun _ => 40 * cfg.regularOpCost + (249 * cfg.regularOpCost + kh) + 20 * cfg.regularOpCost)
        (post548NoneF n g ta A gt s out kp key idx maxP len live F Q) := by
  iintro #Hsr
  iunfold srCodeF at Hsr
  icases Hsr with ⟨#Hrr, #F459, #F523, #F498⟩
  ihave #HcR : ifaceCodeR e inst mi A n mx $$ []
  · iunfold rrCodeF at Hrr
    icases Hrr with ⟨#Hrr, -⟩
    iunfold rrCode at Hrr
    icases Hrr with ⟨#H, -⟩
    iexact H
  ihave #Hcode : ifaceCode e inst mi A n mx $$ []
  · iunfold ifaceCodeR at HcR
    icases HcR with ⟨#H, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  rw [storageReadResult_eq] at hc
  have hn := hm.mem
  have hg := hm.glob
  have ha459 := hm.funcs 459 (by decide)
  have ha523 := hm.funcs 523 (by decide)
  have ha498 := hm.funcs 498 (by decide)
  have t30 : types[30]!.params.length = 2 := by rfl
  have t5 : types[5]!.params.length = 2 := by rfl
  have t39 : types[39]!.params.length = 5 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have e48 : (s - 32 - 16).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h32] <;> omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre548F at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hk, Hhost⟩
  subst hargs
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  -- the stack: R (144) F (16) U (8) SL (8) O (16)
  icases stk_split n (s.toNat - 192) 144 48 $$ Hs with ⟨Rg, Hs⟩
  icases stk_split n (s.toNat - 192 + 144) 16 32 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 192 + 144 + 16) 8 24 $$ Hs with ⟨U, Hs⟩
  icases stk_split n (s.toNat - 192 + 144 + 16 + 8) 8 16 $$ Hs with ⟨SL, O⟩
  rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega, show s.toNat - 48 + 16 = s.toNat - 32 by omega,
    show s.toNat - 32 + 8 = s.toNat - 24 by omega, show s.toNat - 24 + 8 = s.toNat - 16 by omega]
  icases VecFromElem.stk_split n (s.toNat - 24) 4 4 $$ SL with ⟨SL0, SL4⟩
  icases stk4_word n _ $$ SL0 with ⟨%x0, SL0⟩
  icases stk4_word n _ $$ SL4 with ⟨%x4, SL4⟩
  icases stk_frame4 n (s.toNat - 48) (s - 32 - 16) e48 $$ Fr with ⟨%w0, %w4, %w8, %w12, Fr⟩
  simp only [f548]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [SL4]
  mstep; mstep; mstep [SL0]
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep
  mcall (f459_spec cfg lim (d + 1) types[30]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 32)⟩ (s - 32) rfl (by omega) (by omega) h Q (s - 32 + 8) kp kl key
      (foundU64 (h.storage key)) kh hc w0 w4 w8 w12) using [Hg HI SL0 SL4 Fr Hk Hhost]
  · iunfold StorageRead.withPre
    ihave SL0 := memBytes_addr (show s.toNat - 24 = (s - 32 + 8).toNat by omega) $$ SL0
    ihave SL4 := memBytes_addr (show s.toNat - 24 + 4 = (s - 32 + 8).toNat + 4 by omega) $$ SL4
    iframe Hg HI SL0 SL4 Fr Hk Hhost
    ipureintro; rfl
  iunfold StorageRead.withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, SL0, SL4, Fr, Hk, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  simp only [hsk, foundU64]
  mcredits (20 * cfg.regularOpCost + R)
  have ho4 : (ob.take 4).length = 4 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  mstep; mstep; mstep; mstep
  mstep; mstep
  simp only [show UInt64.toUInt32 0 = 0 from rfl]
  mstep
  try mpay
  mstep; mstep; mstep [Ho0]; mstep
  try mpay
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post548NoneF
  simp only [optVecAtF]
  isplitr
  · ipureintro; simp
  iframe Hg Hvt Hk Ho0 Hinv
  isplitl [HI HS12]
  · iunfold ifaceR; iframe HI HS12
  isplitr [Ho4 Hhost]
  · ihave Fr := frame4_stk n (s.toNat - 48) _ e48 _ _ _ _ $$ Fr
    ihave SL0 := stk_word n _ _ $$ SL0
    ihave SL4 := stk_word n _ _ $$ SL4
    ihave SL := stk_join n _ 4 4 $$ [SL0 SL4]
    · iframe SL0 SL4
    ihave SL := stk_addr (show (s - 32 + 8).toNat = s.toNat - 24 by omega) $$ SL
    ihave U := stk_join n (s.toNat - 32) 8 8 $$ [U SL]
    · rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]; iframe U SL
    ihave U := stk_join n (s.toNat - 32) 16 16 $$ [U O]
    · rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega]; iframe U O
    ihave Fr := stk_join n (s.toNat - 48) 16 32 $$ [Fr U]
    · rw [show s.toNat - 48 + 16 = s.toNat - 32 by omega]; iframe Fr U
    iapply stk_join n (s.toNat - 192) 144 48
    rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega]
    iframe Rg Fr
  isplitl [Ho4]
  · iexists ob.drop 4; iframe Ho4; ipureintro; simp; omega
  iexists h'
  iframe Hhost
  ipureintro; exact hq


open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- Absent-key read with the real metered host and its trie proof budget. -/
theorem f548_noneF_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (key : List UInt8) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (st : Near.TrieOverlay.State) (hkl : key.length = kl.toNat) (hpos : 0 < kl.toNat)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal st (contractKey h.context.currentAccountId key))
    {bud : Nat} (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ bud)
    (hsk : h.storage key = none) :
    srCodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f548 Cg
        (pre548F n g ta A gt s out kp kl key idx maxP len live F ob h)
        (fun _ => 40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h key kl.toNat) +
          20 * cfg.regularOpCost)
        (post548NoneF n g ta A gt s out kp key idx maxP len live F (StorageReadPost h key 0 st)) := by
  have hlen : UInt64.ofNat kl.toNat ≠ u64Max := by
    have := kl.toNat_lt
    intro h'
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hc := storageRead_readContract (C := Cg) e h (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat) 0 key st
    hlen (by rw [ValueReturn.toNat_ofNat32]; exact hkl) (by rw [ValueReturn.toNat_ofNat32]; exact hpos) hacc hlim
    hb hz hlink hproof hbud (fun v hv _ => by rw [hsk] at hv; cases hv)
  rw [ValueReturn.toNat_ofNat32, ValueReturn.toNat_ofNat32] at hc
  exact f548_noneF cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s out kp kl hs hal hout key idx maxP len
    live F ob hob h _ _ hsk hc

end Spec

end WNear.Binary.StorageReadWrapF
