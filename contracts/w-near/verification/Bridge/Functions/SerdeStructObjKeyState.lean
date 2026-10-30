import Bridge.Functions.SerdeStructObjState
import Bridge.Functions.SerdeKeyReuse

/-! # Concrete key reading inside the changing-state object loop -/

namespace WNear.Binary.SerdeStructObjKeyState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (strRun borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Pure bounds on reachable heap and scratch coordinates at each reader position. -/
abbrev Bounds := Nat → Nat → Nat → UInt32 → Prop

/-- All shared parser resources, with the concrete heap/scratch coordinates exposed. -/
def core (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (B : Bounds) (i : Nat) : IProp GF :=
  iprop(∃ (hl F : Nat) (p cap sl : UInt32), ⌜B i hl F cap ∧ cap.toNat < 2 ^ 25⌝ ∗
    vt n 1057464 idx ta alloc ∗ SerdeValueState.tables n ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
    scratchPre n maxP hl live F de p cap sl)

/-- The saved String's bytes and allocation stay live through every later key. -/
def member (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (B Bsaved : Bounds) (i : Nat) : Option (WNear.AccountId × UInt32 × UInt32) → IProp GF
  | none => core n maxP ta alloc idx de live B i
  | some (a, p, cap) => iprop(⌜cap = UInt32.ofNat a.val.utf8ByteSize ∧ p ≠ 0⌝ ∗
      n ↦[wms][ p.toNat ] a.val.toUTF8.toList ∗
      core n maxP ta alloc idx de ((p.toNat, cap.toNat) :: live) Bsaved i)

/-- A saved descriptor lends the parser state and accepts it back at a later reader cursor. -/
theorem seen_core (n maxP ta alloc : Nat) (idx de s : UInt32) (live : List (Nat × Nat))
    (B Bsaved : Bounds) (i : Nat) (seen : Option WNear.AccountId) :
    SerdeStructObjState.seenRes (GF := GF) n s (member n maxP ta alloc idx de live B Bsaved) i seen ⊢
      ∃ (C : Bounds) (lv : List (Nat × Nat)), ⌜C = B ∨ C = Bsaved⌝ ∗ core n maxP ta alloc idx de lv C i ∗
        (∀ j, core n maxP ta alloc idx de lv C j -∗
          SerdeStructObjState.seenRes n s (member n maxP ta alloc idx de live B Bsaved) j seen) := by
  iintro H
  cases seen with
  | none =>
    iunfold SerdeStructObjState.seenRes at H
    icases H with ⟨%b8, %hb8, S40, S44, Hcore⟩
    iexists B, live
    isplitr
    · ipureintro; exact Or.inl rfl
    dsimp only [member]
    iframe Hcore
    iintro %j Hcore
    iunfold SerdeStructObjState.seenRes
    iexists b8
    dsimp only [member]
    iframe S40 S44 Hcore
    ipureintro; exact hb8
  | some a =>
    iunfold SerdeStructObjState.seenRes at H
    icases H with ⟨%p, %cap, %hp, S40, S44, S48, Hmember⟩
    iunfold member at Hmember
    icases Hmember with ⟨%hv, Hb, Hcore⟩
    iexists Bsaved, (p.toNat, cap.toNat) :: live
    isplitr
    · ipureintro; exact Or.inr rfl
    iframe Hcore
    iintro %j Hcore
    iunfold SerdeStructObjState.seenRes
    iexists p, cap
    isplitr
    · ipureintro; exact hp
    iframe S40 S44 S48
    iunfold member
    dsimp only
    iframe Hb Hcore
    ipureintro; exact hv

/-- The common key result retains the exact capacity and free-list endpoint on both paths. -/
theorem key_exact (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr ptrS capS : UInt32) (bs bytes rest : List UInt8) (q : Nat)
    (hok : strRun (bs.drop q) [] = .ok bytes rest) :
    SerdeKeyEsc.keyState (GF := GF) n maxP hl live F de ptr ptrS capS bs bytes rest q ⊢
      ∃ (p cap sl : UInt32) (hl' : Nat),
        ⌜cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧ hl ≤ hl' ∧
          hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop q) []) * 65536⌝ ∗
        rd n de ptr bs (bs.length - rest.length) ∗
        scratchPre n maxP hl' live (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) de p cap sl := by
  iintro H
  iunfold SerdeKeyEsc.keyState at H
  icases H with ⟨Hrd, Hs⟩
  by_cases hb : borrowed (bs.drop q)
  · simp only [if_pos hb]
    have hchunks := (SerdeValueReuse.borrowed_parts _ _ _ hb hok).2.2
    simp only [hchunks, endState, endFreeBound, growthPages, Nat.zero_mul, Nat.add_zero]
    iexists ptrS, capS, 0, hl
    iframe Hrd Hs
    ipureintro; exact ⟨rfl, le_rfl, le_rfl⟩
  · simp only [if_neg hb]
    icases Hs with ⟨%p, %cap, %hl', %F', %ht, Hs⟩
    iexists p, cap, UInt32.ofNat bytes.length, hl'
    rw [← ht.2.2.1]
    iframe Hrd Hs
    ipureintro; exact ⟨ht.2.1, ht.1, ht.2.2.2⟩

/-- Enlarging a pure cursor bound transports the whole member state without touching memory. -/
theorem member_mono (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (B Bsaved : Bounds) (hB : ∀ i j hl F cap, i ≤ j → B i hl F cap → B j hl F cap)
    (hSaved : ∀ i j hl F cap, i ≤ j → Bsaved i hl F cap → Bsaved j hl F cap)
    (i j : Nat) (seen : Option (WNear.AccountId × UInt32 × UInt32)) (hij : i ≤ j) :
    member (GF := GF) n maxP ta alloc idx de live B Bsaved i seen ⊢ member n maxP ta alloc idx de live B Bsaved j seen := by
  have hc (C : Bounds) (hC : ∀ i j hl F cap, i ≤ j → C i hl F cap → C j hl F cap)
      (lv : List (Nat × Nat)) : core (GF := GF) n maxP ta alloc idx de lv C i ⊢ core n maxP ta alloc idx de lv C j := by
    iintro H
    iunfold core at H
    icases H with ⟨%hl, %F, %p, %cap, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hs⟩
    iunfold core
    iexists hl, F, p, cap, sl
    iframe Hvt Htables Hkey Hident Hs
    ipureintro; exact ⟨hC i j hl F cap hij hb, hcap⟩
  cases seen with
  | none => exact hc B hB live
  | some v =>
    obtain ⟨a, p, cap⟩ := v
    iintro H
    iunfold member at H
    icases H with ⟨%hv, Hb, Hcore⟩
    iunfold member
    dsimp only
    iframe Hb
    isplitr
    · ipureintro; exact hv
    iapply hc Bsaved hSaved
    iexact Hcore

/-- An allocator's alignment belongs to actual memory, not every integer in a growth interval. -/
theorem alignment_not_interval (hl : Nat) (ha : hl % 65536 = 0) :
    ¬ (∀ hl', hl ≤ hl' → hl' ≤ hl + 65536 → hl' % 65536 = 0) := by
  intro h
  have hb := h (hl + 1) (by omega) (by omega)
  omega

/-- Read alignment and positivity from the actual allocator while retaining reusable scratch. -/
theorem scratch_alignment (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de p cap sl : UInt32) :
    scratchPre (GF := GF) n maxP hl live F de p cap sl ⊢
      ⌜hl % 65536 = 0 ∧ 0 < hl⌝ ∗ scratchPre n maxP hl live F de p cap sl := by
  iintro H
  iunfold scratchPre at H
  icases H with ⟨S8, S0, S4, Hsb⟩
  icases ParseEscape.sbuf_split $$ Hsb with ⟨Hheap, Hraw⟩
  icases SerdeDeStrEsc.heapInv_alignment n maxP hl
    (if cap = 0 then live else (p.toNat, cap.toNat) :: live) F $$ Hheap with ⟨%ha, Hheap⟩
  isplitr
  · ipureintro; exact ha
  iunfold scratchPre
  iframe S8 S0 S4
  iapply ParseEscape.sbuf_join
  iframe Hheap Hraw

/-- The remaining key obligations concern only reachable resource bounds and the fixed charge. -/
def KeyConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : Bounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.keyRoom maxP hl cap (bs.drop q) ∧ SerdeKeyReuse.keyCost cfg F cap bs key.toUTF8.toList rest q ≤ K q ∧
    (∀ hl', hl ≤ hl' → hl' ≤ hl + growthPages cap 0 (appendChunks (bs.drop q) []) * 65536 →
      B (bs.length - rest.length) hl' (endFreeBound F cap 0 (appendChunks (bs.drop q) []))
        (endState cap 0 (appendChunks (bs.drop q) [])).1)

set_option maxRecDepth 100000 in
/-- The concrete general key reader discharges the loop's key-call hypothesis from pure bounds. -/
theorem keyHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : Bounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hc : KeyConditions cfg maxP bs B K) (hcSaved : KeyConditions cfg maxP bs Bsaved K) (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A) :
    SerdeStructObjState.KeyHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs K
      (member n maxP ta (A 578) idx de live B Bsaved) Cd := by
  intro d s first i q key rest seen hd hsp hsend hi hq hmodel
  have hql := SerdeStructObj.keyQ_le hq
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  have hs32 : (s + 32).toNat = s.toNat + 32 := by simp [UInt32.toNat_add]; omega
  iintro #HCd
  ihave Hcode := hcode $$ HCd
  icases Hcode with ⟨#C193, #C646⟩
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, M32, M36, Hg, Hstack, Hrd, Hseen⟩
  icases seen_core n maxP ta (A 578) idx de s live B Bsaved i seen $$ Hseen with ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %ptrS, %capS, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hc' : KeyConditions cfg maxP bs C K := by
    rcases hC with rfl | rfl
    · exact hc
    · exact hcSaved
  icases scratch_alignment n maxP hl lv F de ptrS capS sl $$ Hscratch with ⟨%⟨halign, hpositive⟩, Hscratch⟩
  obtain ⟨hr, hcost, hstep⟩ := hc' first i q key rest hl F capS hi hq hmodel hb hcap halign hpositive
  have callKey := SerdeKeyReuse.f193_key_model (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt
    s (s + 32) de ptr idx ptrS capS sl bs first i q maxP hl F lv key rest hlen hptr hde
    (by rw [hs32]; omega) (by omega) hi hql hq hcap hr hmodel
  rw [hs32, show s.toNat + 32 + 4 = s.toNat + 36 by omega] at callKey
  ihave #S := callKey $$ [C193 C646]
  · iframe C193 C646
  clear callKey
  iunfold MFunSpec at S
  ihave Hc := credits_mono (C := Cg)
    (show (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost +
      SerdeKeyReuse.keyCost cfg F capS bs key.toUTF8.toList rest q + R ≤
      (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost + K q + R by omega) $$ Hc
  icases VecFromElem.stk_split n (s.toNat - 304) 96 208 $$ Hstack with ⟨H96, H208⟩
  rw [show s.toNat - 304 + 96 = s.toNat - 208 by omega]
  iapply mwpInvoke_wand
  isplitl [M32 M36 Hg H208 Hrd Hvt Htables Hkey Hscratch Hc]
  · iapply S $$ %args %R [M32 M36 Hg H208 Hrd Hvt Htables Hkey Hscratch] Hc
    dsimp only
    iframe M32 M36 Hg H208 Hvt Htables Hkey Hscratch Hrd
    ipureintro; exact ha
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %hrs, M32, M36, Hg, H208, Hvt, Htables, Hkey, Hresult⟩
    icases key_exact n maxP hl lv F de ptr ptrS capS bs key.toUTF8.toList rest q hok $$ Hresult with
      ⟨%p', %cap', %sl', %hl', %⟨hcapEq, hlo, hhi⟩, Hrd, Hscratch⟩
    have hcap' : cap'.toNat < 2 ^ 25 := hcapEq ▸ SerdeObjectState.parsed_capacity bs key.toUTF8.toList rest q capS hlen hcap hok
    have hb' : C (bs.length - rest.length) hl' (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) cap' :=
      hcapEq ▸ hstep hl' hlo hhi
    iframe Hc M32 M36 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H96 H208]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 96 208
      rw [show s.toNat - 304 + 96 = s.toNat - 208 by omega]
      iframe H96 H208
    iapply Hsaved $$ %(bs.length - rest.length)
    iunfold core
    iexists hl', endFreeBound F capS 0 (appendChunks (bs.drop q) []), p', cap', sl'
    iframe Hvt Htables Hkey Hident Hscratch
    ipureintro; exact ⟨hb', hcap'⟩
  · iintro Htrap; iexact Htrap

end Resource
end WNear.Binary.SerdeStructObjKeyState
