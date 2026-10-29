import Bridge.Functions.StorageReadWrap
import Bridge.Functions.ReadRegisterF

/-!
# `env::storage_read` (548) on `heapInv … F`, a key present

`StorageReadWrap.f548_spec` on a key holding a value, on any free-list bound `F ≥ 1` (`okG F`),
with `ReadRegisterF.f523_specF` in place of `f523_spec`: the value in a fresh heap block
(`optVecAtF … (some v)`).

* `f548_someF`: for any read contract `hc` whose postcondition is `QOk`.
* `f548_someF_host`: with `storageRead_readContract` (register 0).
-/

namespace WNear.Binary.StorageReadWrapF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ReadRegister
open WNear.Binary.ReadRegisterF (rrCodeF pre523F post523F cost523F f523_specF optVecAtF)
open WNear.Binary.StorageRead (foundU64 storageReadResult_eq f459_spec)
open WNear.Binary.StorageReadWrap (QOk storageReadPost_ok pre498 post498 f498_spec)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr vecCode roomFor)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.VecWithCap (okG)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem cost523F_eq (cfg : WasmConfig) (F : Nat) {h h' : NearState} {val : List UInt8}
    (hr : h'.registers 0 = some val) (hch : ∀ cs, chargesUse h' cs = chargesUse h cs) :
    cost523F cfg F h' 0 = cost523F cfg F (h.setRegister 0 val) 0 := by
  have h2 : (h.setRegister 0 val).registers 0 = some val := by simp [NearState.setRegister]
  have h1 : ∀ cs, chargesUse h' cs = chargesUse (h.setRegister 0 val) cs := fun cs =>
    (hch cs).trans (StorageReadWrap.chargesUse_congr' (a := h) (b := h.setRegister 0 val) rfl rfl cs)
  unfold cost523F ReadRegisterF.costRestF registerLenUse readRegisterUse
  rw [show (0 : UInt64).toNat = 0 from rfl, hr, h2]
  simp only [h1]

/-- The code `storage_read` runs on `heapInv … F` (persistent). -/
def srCodeF (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCodeF e inst mi A n maxP mx ∗ A 459 ↪[wf] FuncInst.wasm types[30]! inst f459 ∗
    A 523 ↪[wf] FuncInst.wasm types[5]! inst f523 ∗ A 498 ↪[wf] FuncInst.wasm types[39]! inst f498)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (srCodeF (GF := GF) e inst mi A n maxP mx) := by
  unfold srCodeF; infer_instance

def pre548F (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out kp kl : UInt32) (key : List UInt8)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (h : NearState)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗
    stk n (s.toNat - 192) 192 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ kp.toNat ] key ∗ mhostPt h)

def post548F (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out kp : UInt32) (key : List UInt8)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (val : List UInt8)
    (Q : NearState → Prop) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 192) 192 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ kp.toNat ] key ∗
    optVecAtF n maxP len live F out (some val) ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

/-- The cost of `storage_read` past the host call, a value present. -/
def costSF (cfg : WasmConfig) (F : Nat) (h : NearState) (val : List UInt8) : Nat :=
  70 * cfg.regularOpCost + cost523F cfg F (h.setRegister 0 val) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`env::storage_read(key)`** (548) on `heapInv … F`, the key holding `val`: `Some(vec)` at `out`
with `val` in a fresh heap block, the host some `h'` with `Q h'`. -/
theorem f548_someF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (key : List UInt8) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (Q : NearState → Prop) (kh : Nat) (val : List UInt8) (hsk : h.storage key = some val)
    (hc : ReadContractP (metered e "storage_read" storageReadFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 0] (storageReadResult (h.storage key))
      kp.toNat key kh Cg)
    (hQ : QOk h key Q) (hok : RegOk maxP len (some val)) :
    srCodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f548 Cg
        (pre548F n g ta A gt s out kp kl key idx maxP len live F ob h)
        (fun _ => 40 * cfg.regularOpCost + (249 * cfg.regularOpCost + kh) + costSF cfg F h val)
        (post548F n g ta A gt s out kp key idx maxP len live F val Q) := by
  iintro #Hsr
  iunfold srCodeF at Hsr
  icases Hsr with ⟨#Hrr, #F459, #F523, #F498⟩
  ihave #HcR : ifaceCodeR e inst mi A n mx $$ []
  · iunfold rrCodeF, rrCode at Hrr
    icases Hrr with ⟨⟨#H, -⟩, -⟩
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
  unfold costSF
  generalize hK523 : cost523F cfg F (h.setRegister 0 val) 0 = K523
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
  obtain ⟨hreg, hch⟩ := hQ h' hq
  simp only [hsk, foundU64]
  have hr0 := hreg val hsk
  icases stk_split n (s.toNat - 16) 12 4 $$ O with ⟨O, O12⟩
  iunfold stk at O
  icases O with ⟨%obb, %hobb, O⟩
  have hr0' : h'.registers (UInt64.toNat 0) = some val := hr0
  have h523 := f523_specF (GF := GF) cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
    gt (s - 32) (s - 32 + 16) (by omega) (by omega) (by omega) 0 idx maxP len live F hF obb hobb h'
    (by rw [hr0']; exact hok)
  rw [cost523F_eq cfg F hr0 hch, hK523] at h523
  ihave #S523 := h523 $$ Hrr
  mcredits (70 * cfg.regularOpCost + K523 + R)
  mstep; mstep; mstep; mstep
  mstep; mstep
  simp only [show UInt64.toUInt32 1 = 1 from rfl]
  mstep
  try mpay
  mstep; mstep; mstep; mstep
  mcall S523 using [Hg HI HS12 Rg Fr Hvt Hinv O Hhost]
  · iunfold pre523F
    ihave Fr := frame4_stk n (s.toNat - 48) _ e48 _ _ _ _ $$ Fr
    ihave Rg := stk_join n (s.toNat - 192) 144 16 $$ [Rg Fr]
    · rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega]; iframe Rg Fr
    ihave Rg := stk_addr (show s.toNat - 192 = (s - 32).toNat - 160 by omega) $$ Rg
    ihave O := memBytes_addr (show s.toNat - 16 = (s - 32 + 16).toNat by omega) $$ O
    iunfold ifaceR
    iframe Hg HI HS12 Rg Hvt Hinv O Hhost
    ipureintro; rfl
  iunfold post523F at HQ
  icases HQ with ⟨%hrs, Hg, HI, Rg, Hvt, HO, Hhost⟩
  subst hrs
  rw [hr0']
  iunfold optVecAtF at HO
  icases HO with ⟨%p, P0, P4, P8, %len', %⟨hp0, hl'⟩, Hinv, Hb⟩
  mcredits (40 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f498_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg out (s - 32 + 16) p
      (UInt32.ofNat val.length) (UInt32.ofNat val.length) ob hob hp0 hout (by omega)) using [P0 P4 P8 Ho]
  · iunfold pre498
    iframe P0 P4 P8 Ho
    ipureintro; exact ⟨_, _, _, rfl⟩
  iunfold post498 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, Ho0, Ho4, Ho8⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post548F
  simp only [optVecAtF]
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hvt Hk
  isplitl [HI]
  · iexact HI
  isplitr [Ho0 Ho4 Ho8 Hinv Hb Hhost]
  · ihave Rg := stk_addr (show (s - 32).toNat - 160 = s.toNat - 192 by omega) $$ Rg
    icases stk_split n (s.toNat - 192) 144 16 $$ Rg with ⟨Rg, Fr⟩
    ihave Fr := stk_addr (show s.toNat - 192 + 144 = s.toNat - 48 by omega) $$ Fr
    ihave SL0 := stk_word n _ _ $$ SL0
    ihave SL4 := stk_word n _ _ $$ SL4
    ihave SL := stk_join n _ 4 4 $$ [SL0 SL4]
    · iframe SL0 SL4
    ihave SL := stk_addr (show (s - 32 + 8).toNat = s.toNat - 24 by omega) $$ SL
    ihave P0 := stk_word n _ _ $$ P0
    ihave P4 := stk_word n _ _ $$ P4
    ihave P8 := stk_word n _ _ $$ P8
    ihave P := stk_join n _ 4 4 $$ [P0 P4]
    · iframe P0 P4
    ihave P := stk_join n _ 8 4 $$ [P P8]
    · iframe P P8
    ihave P := stk_addr (show (s - 32 + 16).toNat = s.toNat - 16 by omega) $$ P
    ihave O := stk_join n (s.toNat - 16) 12 4 $$ [P O12]
    · iframe P O12
    ihave U := stk_join n (s.toNat - 32) 8 8 $$ [U SL]
    · rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]; iframe U SL
    ihave U := stk_join n (s.toNat - 32) 16 16 $$ [U O]
    · rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega]; iframe U O
    ihave Fr := stk_join n (s.toNat - 48) 16 32 $$ [Fr U]
    · rw [show s.toNat - 48 + 16 = s.toNat - 32 by omega]; iframe Fr U
    iapply stk_join n (s.toNat - 192) 144 48
    rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega]
    iframe Rg Fr
  isplitr [Hhost]
  · iexists p
    iframe Ho0 Ho4 Ho8
    iexists len'
    iframe Hinv Hb
    ipureintro; exact ⟨hp0, hl'⟩
  iexists h'
  iframe Hhost
  ipureintro; exact hq

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `f548_someF` with the host's `storageRead_readContract` (register 0). -/
theorem f548_someF_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (key : List UInt8) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (st : Near.TrieOverlay.State) (hkl : key.length = kl.toNat) (hpos : 0 < kl.toNat)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal st (contractKey h.context.currentAccountId key))
    {bud : Nat} (hproof : ProofBudget h st bud)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId key) ≤ bud)
    (val : List UInt8) (hsk : h.storage key = some val)
    (hreg : withinLimit h.config.maxRegisterLen val.length = true)
    (hok : RegOk maxP len (some val)) :
    srCodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f548 Cg
        (pre548F n g ta A gt s out kp kl key idx maxP len live F ob h)
        (fun _ => 40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h key kl.toNat) +
          costSF cfg F h val)
        (post548F n g ta A gt s out kp key idx maxP len live F val (StorageReadPost h key 0 st)) := by
  have hlen : UInt64.ofNat kl.toNat ≠ u64Max := by
    have := kl.toNat_lt
    intro h'
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hc := storageRead_readContract (C := Cg) e h (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat) 0 key st
    hlen (by rw [ValueReturn.toNat_ofNat32]; exact hkl) (by rw [ValueReturn.toNat_ofNat32]; exact hpos) hacc hlim
    hb hz hlink hproof hbud (fun v hv _ => by rw [hsk] at hv; cases hv; exact hreg)
  rw [ValueReturn.toNat_ofNat32, ValueReturn.toNat_ofNat32] at hc
  exact f548_someF cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s out kp kl hs hal hout key idx maxP len
    live F hF ob hob h _ _ val hsk hc (storageReadPost_ok h key st) hok

end Spec

end WNear.Binary.StorageReadWrapF
