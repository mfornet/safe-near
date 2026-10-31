import Bridge.Functions.StateReadNone
import Bridge.Functions.StateReadLenF
import Bridge.Functions.StorageReadNoneF

namespace WNear.Binary.StateReadNoneFree

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshLeaves WNear.Binary.BorshInt WNear.Binary.BorshVec WNear.Binary.BorshBytes
open WNear.Binary.BorshFT WNear.Binary.BorshContract WNear.Binary.DropVec
open WNear.Binary.StateRead (noneAt bytes32_zero')
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.StorageReadWrapF (srCodeF pre548F post548NoneF f548_noneF_host)
open WNear.Binary.ReadRegister (RegOk ifaceR)
open WNear.Binary.ReadRegisterF (optVecAtF)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.Interface (IfaceMod)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The 40 bytes at `out` with the word at offset 24 zeroed: `None : Option<Contract>`. -/
def noneAt (ob : List UInt8) : List UInt8 := ob.take 24 ++ [0, 0, 0, 0] ++ ob.drop 28

/-- After `state_read` on an absent `"STATE"`: `None` at `out` (`noneAt ob`), the heap
unchanged, the host after `storage_read`. -/
def post219NoneF (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
    n ↦[wms][ out.toNat ] noneAt ob ∗ heapInv n maxP len live F ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- **`env::state_read::<Contract>`** (function 219 of `contract.wasm`) on a host with no value
at `"STATE"`: `None` at `out` (the word at offset 24 zeroed). -/
theorem f219_spec_noneF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (_hout : out.toNat + 40 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (hob : ob.length = 40) (h : NearState)
    (hv : h.storage StateRead.stateKey = none)
    (st : Near.TrieOverlay.State)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen StateRead.stateKey.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage StateRead.stateKey = viewVal st (contractKey h.context.currentAccountId StateRead.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey))) :
    stateCodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f219 Cg
        (pre219F n g ta A gt s out idx maxP len live F ob h)
        (fun _ => 34 * cfg.regularOpCost +
          (40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5) +
            20 * cfg.regularOpCost))
        (post219NoneF n g ta A gt s out idx maxP len live F ob (StorageReadPost h StateRead.stateKey 0 st)) := by
  iintro #Hcode
  ihave #Hcode' := Hcode
  iunfold stateCodeF at Hcode'
  icases Hcode' with ⟨#Hsr, #Hsl, -, #H548, -, -⟩
  ihave #Hsl' := Hsl
  iunfold BorshContractF.sliceCode, BorshContractF.contractCode, BorshFTF.ftCode, BorshBytesF.bytesCode, rdCode at Hsl'
  icases Hsl' with ⟨⟨⟨⟨⟨#Hi, -⟩, -⟩, -⟩, -, -, -⟩, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha548 := hm.funcs 548 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h96 : (s - 96).toNat = s.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 96 + 8).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, h96]; omega
  have S548 := f548_noneF_host (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 96) (s - 96 + 8) 1049788 5 (by omega) (by omega) (by omega) StateRead.stateKey idx maxP len live F
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre219F at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hk, Hhost⟩
  subst hargs
  icases stkSp 496 96 rfl $$ Hs with ⟨Lo, Hs⟩
  icases stkSp 8 88 rfl $$ Hs with ⟨F0, Hs⟩
  icases stkSp 12 76 rfl $$ Hs with ⟨F8, Rest⟩
  icases stk_bytes' $$ F8 with ⟨%f8, %hf8, F8⟩
  icases stkSp 304 192 rfl $$ Lo with ⟨LoA, LoB⟩
  simp only [f219]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  have S := S548 f8 hf8 h st rfl (by decide) hacc hlim hb hz hlink hproof
    (by simp only [readProofCost, hv, Option.map_none, Option.getD_none, Nat.add_zero]; exact Nat.le_refl _) hv
  mcall S using [Hg HI LoB Hvt Hinv F8 Hk Hhost]
  · iunfold pre548F
    ihave LoB := stkA (a := s.toNat - 592 + 304) (b := (s - 96).toNat - 192) (by omega) $$ LoB
    ihave F8 := memBytes_addr (a := s.toNat - 592 + 496 + 8) (b := (s - 96 + 8).toNat) (by omega) $$ F8
    ihave Hk := memBytes_addr (a := 1049788) (b := (1049788 : UInt32).toNat) rfl $$ Hk
    iframe Hg HI LoB Hvt Hinv F8 Hk Hhost
    ipureintro; rfl
  iunfold post548NoneF at HQ
  icases HQ with ⟨%hrs, Hg, HI, LoB, Hvt, Hk, OV, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  iunfold optVecAtF at OV
  icases OV with ⟨O8, ⟨%bs, %hbs, O12⟩, Hinv⟩
  ihave O8 := memBytes_addr (a := (s - 96 + 8).toNat) (b := s.toNat - 88) (by omega) $$ O8
  have hsp : ob = ob.take 24 ++ (ob.drop 24).take 4 ++ ob.drop 28 := by
    have e := List.take_append_drop 4 (ob.drop 24)
    simp only [List.drop_drop] at e
    rw [List.append_assoc, e, List.take_append_drop]
  ihave Ho := (show (n ↦[wms][ out.toNat ] ob : IProp GF) ⊢
      n ↦[wms][ out.toNat ] (ob.take 24 ++ (ob.drop 24).take 4 ++ ob.drop 28) by rw [← hsp]) $$ Ho
  icases splitB (a := out.toNat) (b := out.toNat + 24 + 4) (ob.take 24 ++ (ob.drop 24).take 4) (ob.drop 28)
    (by simp only [List.length_append, List.length_take, List.length_drop, hob]; omega) $$ Ho with ⟨Ho, O28⟩
  icases splitB (a := out.toNat) (b := out.toNat + 24) (ob.take 24) ((ob.drop 24).take 4)
    (by simp only [List.length_take, hob]; omega) $$ Ho with ⟨Ho, O24⟩
  have hl4 : ((ob.drop 24).take 4).length = 4 := by simp [hob]
  generalize (ob.drop 24).take 4 = m4 at hl4 ⊢
  clear hsp
  mstep; mstep; mstep; mstep; mstep [O8]
  mstep; mstep; mstep; mstep [O24]
  mstep; mstep; mstep; mstep; mstep [Hg]
  rw [show s - 96 + 96 = s by simp]
  mstep
  mcredits R
  ihave O8 := stkW (b := s.toNat - 88) _ rfl $$ O8
  ihave O12 := stkB (b := s.toNat - 84) (k := 8) _ (by omega) hbs $$ O12
  ihave Lo := stkJ (a := s.toNat - 592) (b := (s - 96).toNat - 192) (k1 := 304) (k2 := 192) (k := 496)
    (by omega) rfl $$ [LoA LoB]
  · iframe LoA LoB
  ihave O8 := stkJ (a := s.toNat - 88) (b := s.toNat - 84) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl
    $$ [O8 O12]
  · iframe O8 O12
  ihave O8 := stkJ (a := s.toNat - 88) (b := s.toNat - 592 + 496 + 8 + 12) (k1 := 12) (k2 := 76) (k := 88)
    (by omega) rfl $$ [O8 Rest]
  · iframe O8 Rest
  ihave F0 := stkJ (a := s.toNat - 592 + 496) (b := s.toNat - 88) (k1 := 8) (k2 := 88) (k := 96) (by omega) rfl
    $$ [F0 O8]
  · iframe F0 O8
  ihave Stk := stkJ (a := s.toNat - 592) (b := s.toNat - 592 + 496) (k1 := 496) (k2 := 96) (k := 592)
    (by omega) rfl $$ [Lo F0]
  · iframe Lo F0
  ihave Ho := joinB (a := out.toNat) (b := out.toNat + 24) (ob.take 24) (bytes32 0) (by simp [hob]) $$ [Ho O24]
  · iframe Ho O24
  ihave Ho := joinB (a := out.toNat) (b := out.toNat + 24 + 4) (ob.take 24 ++ bytes32 0) (ob.drop 28)
    (by simp [hob]) $$ [Ho O28]
  · iframe Ho O28
  iframe Hc
  iunfold post219NoneF
  rw [show noneAt ob = ob.take 24 ++ bytes32 0 ++ ob.drop 28 by simp [noneAt, bytes32_zero']]
  iframe Hg HI Stk Hvt Hk Ho Hinv
  isplitr
  · ipureintro; simp
  iexists h'
  iframe Hhost
  ipureintro; exact hq

end Spec

end WNear.Binary.StateReadNoneFree
