import Bridge.Functions.SerdeHexSuccess
import Bridge.Functions.ParseEscapeSuccessCost

/-! # Successful ignored escapes without allocator ownership -/

namespace WNear.Binary.SerdeIgnoreEscape

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeEsc (okPack hexTable)
open WNear.Binary.ParseEscape
open NearInterface.Json (hex4 unicodeEscape)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Only callees reached by successful ignored escapes; error allocation code is unnecessary. -/
def code (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 637 ↪[wf] FuncInst.wasm types[11]! inst f637 ∗
    A 655 ↪[wf] FuncInst.wasm types[11]! inst f655 ∗ A 653 ↪[wf] FuncInst.wasm types[11]! inst f653)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code (GF := GF) inst mi A) := by
  unfold code; infer_instance

set_option hygiene false in
local macro "finish652" : tactic => `(tactic| (
  repeat (first | mstep | mstep_taken with decide | mstep_not_taken with decide)
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hs Hrd Ht
  ipureintro; simp [htype]))

set_option hygiene false in
local macro "simple652 " v:term:max k1:term:max k2:term:max : tactic => `(tactic| (
  have hk : ([4, 1, 1, 1, 4, 1, 4, 2] : List Nat)[(($v : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = $k1 := by decide
  iapply FromUtf8Gen.mwpi_br_table_k hk
  isplitr
  · ipureintro; rfl
  clear hk
  mctrl_norm; repeat mpay
  first
  | finish652
  | (iterate 4 mstep
     have hk : ([4, 1, 1, 1, 4] : List Nat)[(($v : UInt8).toUInt32 + 4294967198).toNat]?.getD 0 = $k2 := by decide
     iapply FromUtf8Gen.mwpi_br_table_k hk
     isplitr
     · ipureintro; rfl
     clear hk
     mctrl_norm; repeat mpay
     finish652)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Every successful non-Unicode ignored escape returns zero and advances one byte. -/
theorem f652_nu_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr : UInt32) (bs : List UInt8) (j : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 16 < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 112 ≤ s.toNat)
    (hvalid : (escDecode (bs.drop j)).isSome = true) (hnu : ∀ rest, bs.drop j ≠ 0x75 :: rest) :
    code inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f652 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs j ∗ n ↦[wms][ 1062712 ] hexTable))
      (fun _ => 400 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs (j + 1) ∗ n ↦[wms][ 1062712 ] hexTable)) := by
  iintro #HC
  iunfold code at HC
  icases HC with ⟨#Hi, #F637, #F655, #F653⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have hjl : j < bs.length := by
    by_contra h
    have he : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    simp [he, escDecode] at hvalid
  have hlt := s.toNat_lt
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hg, Hs, Hrd, Ht⟩
  subst ha
  simp only [f652]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
    hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 16) de ptr bs j hjl (by omega) hptr hde)
    using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  have hb := okPack_bit de bs[j]
  iterate 17 mstep
  rw [okPack_byte]
  obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
  have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
  have hux : x ≠ 117 := by intro he; exact hnu _ (by rw [hdrop, he])
  have hxok : x = 110 ∨ x = 114 ∨ x = 116 ∨ x = 98 ∨ x = 102 ∨ x = 34 ∨ x = 47 ∨ x = 92 := by
    by_contra he
    simp only [not_or] at he
    rcases he with ⟨hn, hr, ht, hb, hf, hq, hs, hbs⟩
    simp [hdrop, escDecode, hn, hr, ht, hb, hf, hq, hs, hbs, hux] at hvalid
  rw [hx]
  iterate 3 mstep
  rcases hxok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simple652 110 4 0
  · simple652 114 4 0
  · simple652 116 4 0
  · simple652 98 0 4
  · simple652 102 0 4
  · simple652 34 0 0
  · simple652 47 0 0
  · simple652 92 0 0

/-- Scalar values outside the surrogate range pass 652's final character mask. -/
theorem valid_char_mask (cp : Nat) (h2 : cp < 2 ^ 27) (h : cp / 2048 ≠ 27) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat cp &&& 134215680) 55296) = 0 := by
  have e : UInt32.ofNat cp &&& 134215680 = UInt32.ofNat (cp / 2 ^ 11 * 2 ^ 11) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and, UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
      show (134215680 : UInt32).toNat = (2 ^ (27 - 11) - 1) * 2 ^ 11 from rfl, and_hiw cp 11 27 (by decide) h2]
    rw [Nat.mod_eq_of_lt (by have := Nat.div_mul_le_self cp (2 ^ 11); omega)]
  rw [e, eqc _ _ (by have := Nat.div_mul_le_self cp (2 ^ 11); omega)]
  rw [if_neg]
  intro he
  have : (55296 : UInt32).toNat = 55296 := rfl
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Successful BMP Unicode ignored escapes advance past all four hex digits. -/
theorem f652_u0_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr : UInt32) (bs : List UInt8) (j : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 16 < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 112 ≤ s.toNat)
    (hvalid : (escDecode (bs.drop j)).isSome = true) (hu : ∃ rest, bs.drop j = 0x75 :: rest)
    (hlo : ∀ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) → nv / 1024 ≠ 54) :
    code inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f652 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs j ∗ n ↦[wms][ 1062712 ] hexTable))
      (fun _ => 900 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs (j + 5) ∗ n ↦[wms][ 1062712 ] hexTable)) := by
  iintro #HC
  iunfold code at HC
  icases HC with ⟨#Hi, #F637, #F655, #F653⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have hjl : j < bs.length := by
    by_contra h
    have he : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    simp [he, escDecode] at hvalid
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hg, Hs, Hrd, Ht⟩
  subst ha
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ Lo
  simp only [f652]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
    hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 16) de ptr bs j hjl (by omega) hptr hde)
    using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  have hb := okPack_bit de bs[j]
  iterate 17 mstep
  rw [okPack_byte]
  obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
  have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
  have hx117 : x = 117 := by obtain ⟨r, hr⟩ := hu; rw [hdrop] at hr; simp at hr; exact hr.1
  rw [hx]
  subst hx117
  iterate 3 mstep
  have hk : ([4, 1, 1, 1, 4, 1, 4, 2] : List Nat)[((117 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 2 := by decide
  iapply FromUtf8Gen.mwpi_br_table_k hk
  isplitr
  · ipureintro; rfl
  clear hk
  mctrl_norm; repeat mpay
  have hhValid : (hex4 (bs.drop (j + 1))).isSome = true := by
    cases hh : hex4 (bs.drop (j + 1)) with
    | none =>
      have he : escDecode (bs.drop j) = none := by rw [hdrop]; simp [escDecode, unicodeEscape, hh]
      simpa [he] using hvalid
    | some pr => rfl
  have key := SerdeHexSuccess.f653_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
    (by omega) Cg gt (s - 16) de ptr bs (j + 1) hde (by omega) (by omega) hptr (by omega) hhValid
  ihave #S653 := key $$ Hi
  repeat mstep
  mcall S653 using [Hg Lo Hrd Ht]
  · iframe Hg Lo Hrd Ht
  icases HQ with ⟨Hg, Lo, Ht, HQ⟩
  mcredits (400 * cfg.regularOpCost + R)
  cases hh : hex4 (bs.drop (j + 1)) with
  | none => exfalso; simpa [hh] using hhValid
  | some pr =>
    obtain ⟨nv, r1⟩ := pr
    simp only [SerdeHexSuccess.result, hh]
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    have hh' := hh
    rw [SerdeEsc.hex4_eq] at hh'
    split at hh'
    case isFalse => simp at hh'
    rename_i h4
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hh'
    obtain ⟨nv', hacc4, rfl, rfl⟩ := hh'
    have hnv := SerdeEsc.hexAcc_lt _ _ hacc4
    have h4' : 4 ≤ bs.length - (j + 1) := by simpa using h4
    simp only [List.length_take, List.length_drop, show min 4 (bs.length - (j + 1)) = 4 by omega] at hnv
    have hnv' : nv' < 65536 := by simpa using hnv
    have hb := hexPack_low nv' hnv'
    repeat mstep
    rw [hexPack_val nv' hnv']
    repeat mstep
    rw [mask10 nv' hnv']
    repeat mstep
    rw [eqc _ _ (by omega)]
    by_cases hhi : nv' / 1024 = 54
    · exfalso; exact hlo _ _ hh hhi
    rw [if_neg (by intro h; apply hhi; have : (55296 : UInt32).toNat = 55296 := rfl; omega)]
    repeat mstep
    rw [eqc _ _ (by omega)]
    by_cases hlo : nv' / 1024 = 55
    · rw [if_pos (by rw [hlo]; rfl)]
      have hd : escDecode (bs.drop j) = none := by
        rw [hdrop]; simp [escDecode, ue_lo _ _ _ hh (by omega)]
      exfalso; simpa [hd] using hvalid
    rw [if_neg (by intro h; apply hlo; have : (56320 : UInt32).toNat = 56320 := rfl; omega)]
    repeat mstep
    rw [show UInt32.ofNat nv' &&& 65535 = UInt32.ofNat nv' by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      simp; omega]
    repeat mstep
    have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat nv') 1114111) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat']
      omega
    rw [hgt]
    repeat mstep
    rw [valid_char_mask nv' (by omega) (by omega)]
    repeat mstep
    rw [show j + 1 + 4 = j + 5 by omega]
    ihave Lo := stk_addr (show (s - 16).toNat - 96 = s.toNat - 112 by omega) $$ Lo
    ihave Hs := stk_join n (s.toNat - 112) 96 16 $$ [Lo Fr]
    · rw [show s.toNat - 112 + 96 = s.toNat - 16 by omega]
      iframe Lo Fr
    finish652

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful surrogate pair is validated and skipped without allocating decoded bytes. -/
theorem f652_u1_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr : UInt32) (bs : List UInt8) (j : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 16 < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 112 ≤ s.toNat)
    (hvalid : (escDecode (bs.drop j)).isSome = true) (hu : ∃ rest, bs.drop j = 0x75 :: rest)
    (hhi' : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54) :
    code inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f652 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs j ∗ n ↦[wms][ 1062712 ] hexTable))
      (fun _ => 2000 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs (j + 11) ∗ n ↦[wms][ 1062712 ] hexTable)) := by
  iintro #HC
  iunfold code at HC
  icases HC with ⟨#Hi, #F637, #F655, #F653⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have hjl : j < bs.length := by
    by_contra h
    have he : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    simp [he, escDecode] at hvalid
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hg, Hs, Hrd, Ht⟩
  subst ha
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ Lo
  simp only [f652]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
    hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 16) de ptr bs j hjl (by omega) hptr hde)
    using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  have hb := okPack_bit de bs[j]
  iterate 17 mstep
  rw [okPack_byte]
  obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
  have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
  have hx117 : x = 117 := by obtain ⟨r, hr⟩ := hu; rw [hdrop] at hr; simp at hr; exact hr.1
  rw [hx]
  subst hx117
  iterate 3 mstep
  have hk : ([4, 1, 1, 1, 4, 1, 4, 2] : List Nat)[((117 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 2 := by decide
  iapply FromUtf8Gen.mwpi_br_table_k hk
  isplitr
  · ipureintro; rfl
  clear hk
  mctrl_norm; repeat mpay
  have hhValid : (hex4 (bs.drop (j + 1))).isSome = true := by
    cases hh : hex4 (bs.drop (j + 1)) with
    | none =>
      have he : escDecode (bs.drop j) = none := by rw [hdrop]; simp [escDecode, unicodeEscape, hh]
      simpa [he] using hvalid
    | some pr => rfl
  have key := SerdeHexSuccess.f653_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
    (by omega) Cg gt (s - 16) de ptr bs (j + 1) hde (by omega) (by omega) hptr (by omega) hhValid
  ihave #S653 := key $$ Hi
  repeat mstep
  mcall S653 using [Hg Lo Hrd Ht]
  · iframe Hg Lo Hrd Ht
  icases HQ with ⟨Hg, Lo, Ht, HQ⟩
  mcredits (1400 * cfg.regularOpCost + R)
  cases hh : hex4 (bs.drop (j + 1)) with
  | none => exfalso; simpa [hh] using hhValid
  | some pr =>
    obtain ⟨nv, r1⟩ := pr
    simp only [SerdeHexSuccess.result, hh]
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    have hh' := hh
    rw [SerdeEsc.hex4_eq] at hh'
    split at hh'
    case isFalse => simp at hh'
    rename_i h4
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hh'
    obtain ⟨nv', hacc4, rfl, rfl⟩ := hh'
    have hnv := SerdeEsc.hexAcc_lt _ _ hacc4
    have h4' : 4 ≤ bs.length - (j + 1) := by simpa using h4
    simp only [List.length_take, List.length_drop, show min 4 (bs.length - (j + 1)) = 4 by omega] at hnv
    have hnv' : nv' < 65536 := by simpa using hnv
    have hb := hexPack_low nv' hnv'
    repeat mstep
    rw [hexPack_val nv' hnv']
    repeat mstep
    rw [mask10 nv' hnv']
    repeat mstep
    rw [eqc _ _ (by omega)]
    have hhi : nv' / 1024 = 54 := by
      obtain ⟨nv, r, hh', hhHi⟩ := hhi'
      rw [hh] at hh'
      simp only [Option.some.injEq, Prod.mk.injEq] at hh'
      omega
    rw [if_pos (by rw [hhi]; rfl)]
    have hnv1 : 0xD800 ≤ nv' ∧ nv' < 0xDC00 := by omega
    have huv : (unicodeEscape (bs.drop (j + 1))).isSome = true := by
      rw [hdrop] at hvalid
      simpa [escDecode] using hvalid
    obtain ⟨r2, mv, r3, hshape, hh2, hmv1⟩ := ParseEscapeSurrogateSuccess.valid_high_tail _ _ _ hh hnv1 huv
    have hshape5 : bs.drop (j + 1 + 4) = 0x5C :: 0x75 :: r2 := by
      simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshape
    have hrestLen := congrArg List.length hshape5
    simp only [List.length_drop, List.length_cons] at hrestLen
    have hj5 : j + 1 + 4 < bs.length := by omega
    have hj6 : j + 1 + 4 + 1 < bs.length := by omega
    have hb1 : bs[j + 1 + 4] = 92 := by
      have h := hshape5
      rw [List.drop_eq_getElem_cons hj5] at h
      exact (List.cons.inj h).1
    have hshape6 : bs.drop (j + 1 + 4 + 1) = 0x75 :: r2 := by
      have h := congrArg (List.drop 1) hshape5
      simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hb2 : bs[j + 1 + 4 + 1] = 117 := by
      have h := hshape6
      rw [List.drop_eq_getElem_cons hj6] at h
      exact (List.cons.inj h).1
    have hr2 : r2 = bs.drop (j + 1 + 4 + 1 + 1) := by
      have h := congrArg (List.drop 1) hshape6
      simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
    subst r2
    obtain ⟨h4b, rfl⟩ := hex4_some _ _ _ hh2
    have h11 : j + 1 + 4 + 1 + 1 + 4 ≤ bs.length := by
      simp only [List.length_drop] at h4b
      omega
    have hmv' : mv < 65536 := by omega
    have hmlo : mv / 1024 = 55 := by omega
    have hr1 : List.drop 4 (List.drop (j + 1) bs) = bs.drop (j + 1 + 4) := by simp [List.drop_drop]
    repeat mstep
    mcredits (1300 * cfg.regularOpCost + R)
    mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
      hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 16) de ptr bs (j + 1 + 4) hj5
      (by omega) hptr hde) using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mcredits (1150 * cfg.regularOpCost + R)
    rw [hb1]
    have hb := okPack_bit de 92
    repeat mstep
    rw [okPack_ff00, t5c, if_pos rfl]
    repeat mstep
    mcredits (1050 * cfg.regularOpCost + R)
    mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
      hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 16) de ptr bs (j + 1 + 4 + 1) hj6
      (by omega) hptr hde) using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mcredits (900 * cfg.regularOpCost + R)
    rw [hb2]
    have hb := okPack_bit de 117
    repeat mstep
    rw [okPack_ff00, t75, if_pos rfl]
    repeat mstep
    have key2 := SerdeHexSuccess.f653_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
      (by omega) Cg gt (s - 16) de ptr bs (j + 1 + 4 + 1 + 1) hde (by omega)
      (by omega) hptr (by omega) (by simp [hh2])
    ihave #S653b := key2 $$ Hi
    mcredits (850 * cfg.regularOpCost + R)
    mcall S653b using [Hg Lo Hrd Ht]
    · iframe Hg Lo Hrd Ht
    icases HQ with ⟨Hg, Lo, Ht, HQ⟩
    mcredits (500 * cfg.regularOpCost + R)
    simp only [SerdeHexSuccess.result, hh2]
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    have hb := hexPack_low mv hmv'
    repeat mstep
    rw [hexPack_val mv hmv']
    repeat mstep
    rw [mask10 mv hmv', eqc _ _ (by omega), if_pos (by rw [hmlo]; rfl)]
    clear key key2 hh hh2 hacc4 hvalid hu hhi' huv hshape hshape5 hshape6 hhValid hdrop hx
    iclear S653 S653b Hi F637 F655 F653
    repeat mstep
    rw [sub_k nv' 0xD800 4294912000 (by omega) hnv' rfl]
    repeat mstep
    rw [ne16 _ (by omega)]
    repeat mstep
    rw [sub_k mv 0xDC00 4294910976 (by omega) hmv' rfl]
    repeat mstep
    rw [ne16 _ (by omega)]
    iterate 10 mstep
    rw [raw_eq _ _ (by omega) (by omega)]
    iterate 2 mstep
    generalize hraw : (nv' - 55296) * 1024 + (mv - 56320) = raw
    have hraw1 : raw < 1048576 := by omega
    clear hraw hnv1 hmv1 hhi hmlo hnv' hmv' h4' hnv
    rw [show UInt32.ofNat raw + 65536 = UInt32.ofNat (raw + 65536) by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp <;> omega]
    mstep
    mstep
    mstep
    mstep
    have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat (raw + 65536)) 1114111) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat']
      omega
    rw [hgt]
    mstep_not_taken with decide
    have hcpn : (UInt32.ofNat (raw + 65536)).toNat = raw + 65536 := by simp; omega
    generalize hcpv : UInt32.ofNat (raw + 65536) = cpv at hcpn ⊢
    have hmask : Numeric.bool (Numeric.irelop32 IRelOp.eq (cpv &&& 134215680) 55296) = 0 := by
      rw [← hcpv]
      exact mask27 _ (by omega) (by omega)
    have hmaskH : FromUtf8Gen.Hide (Numeric.bool (Numeric.irelop32 IRelOp.eq (cpv &&& 134215680) 55296) = 0) := hmask
    clear hcpv hcpn hmask
    generalize hmasked : cpv &&& 134215680 = masked at hmaskH
    have h_and : Numeric.ibinop32 IBinOp.and cpv 134215680 = .ok masked := by
      change Except.ok (cpv &&& 134215680) = Except.ok masked
      exact congrArg Except.ok hmasked
    mstep
    mstep
    mcredits (400 * cfg.regularOpCost + R)
    iapply mwpi_cons
    iapply NearLogic.mwpi_i32_binop' (op := IBinOp.and) (a := cpv) (b := 134215680) (r := masked) (rest := [])
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨rfl, by omega, h_and⟩
    inext
    iintro Hc
    clear h_and hmasked
    simp only [List.reverse_nil, List.nil_append, Post.mseq_normal]
    rw [show 400 * cfg.regularOpCost + R - cfg.regularOpCost = 399 * cfg.regularOpCost + R by omega]
    mstep
    mstep
    have hmask : Numeric.bool (Numeric.irelop32 IRelOp.eq masked 55296) = 0 := hmaskH
    rw [hmask]
    clear hmask hmaskH hgt
    mstep_not_taken with decide
    repeat mstep
    rw [show j + 1 + 4 + 1 + 1 + 4 = j + 11 by omega]
    ihave Lo := stk_addr (show (s - 16).toNat - 96 = s.toNat - 112 by omega) $$ Lo
    ihave Hs := stk_join n (s.toNat - 112) 96 16 $$ [Lo Fr]
    · rw [show s.toNat - 112 + 96 = s.toNat - 16 by omega]
      iframe Lo Fr
    finish652

/-- Bytes following the leading backslash that a successful escape consumes. -/
def consumed (l : List UInt8) : Nat :=
  if l.head? = some 0x75 then
    match hex4 (l.drop 1) with
    | some (nv, _) => if nv / 1024 = 54 then 11 else 5
    | none => 5
  else 1

/-- The branch lengths used by the Wasm proof agree exactly with the model's decoded escape. -/
theorem consumed_eq (l out : List UInt8) (m : Nat) (he : escDecode l = some (out, m)) :
    consumed l = m := by
  cases l with
  | nil => simp [escDecode] at he
  | cons b tail =>
    by_cases hb : b = 0x75
    · subst hb
      have he' := he
      change (unicodeEscape tail).map (fun p => (String.utf8EncodeChar p.1, 1 + (tail.length - p.2.length))) =
        some (out, m) at he'
      obtain ⟨⟨c, r⟩, hue, hp⟩ := Option.map_eq_some_iff.mp he'
      have hm : m = 1 + (tail.length - r.length) := (congrArg Prod.snd hp).symm
      cases hh : hex4 tail with
      | none => simp [unicodeEscape, hh] at hue
      | some p =>
        obtain ⟨nv, r1⟩ := p
        have hfirst := hex4_some tail r1 nv hh
        by_cases hhi : nv / 1024 = 54
        · have hnv : 0xD800 ≤ nv ∧ nv < 0xDC00 := by omega
          obtain ⟨r2, mv, r3, hshape, hh2, hmv⟩ :=
            ParseEscapeSurrogateSuccess.valid_high_tail tail r1 nv hh hnv (by simp [hue])
          have hsecond := hex4_some r2 r3 mv hh2
          rw [ue_hi tail r1 r2 nv hh hnv hshape, hh2] at hue
          simp only [Option.bind_some, if_pos hmv, Option.some.injEq, Prod.mk.injEq] at hue
          have hr : r3 = r := hue.2
          have hshapeLen := congrArg List.length hshape
          have hfirstLen := congrArg List.length hfirst.2
          have hsecondLen := congrArg List.length hsecond.2
          simp only [List.length_cons, List.length_drop] at hshapeLen hfirstLen hsecondLen
          simp only [consumed, List.head?_cons, ite_true, List.drop_succ_cons, List.drop_zero, hh, if_pos hhi]
          rw [hr] at hsecondLen
          omega
        · unfold unicodeEscape at hue
          simp only [hh, Option.bind_eq_bind, Option.bind_some] at hue
          rw [if_neg (by simp; omega)] at hue
          split at hue
          · simp at hue
          · split at hue
            · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hue
              have hr : r1 = r := hue.2
              have hl := congrArg List.length hfirst.2
              simp only [List.length_drop] at hl
              simp only [consumed, List.head?_cons, ite_true, List.drop_succ_cons, List.drop_zero, hh, if_neg hhi]
              rw [hr] at hl
              omega
            · simp at hue
    · simp only [consumed, List.head?_cons, Option.some.injEq, if_neg hb]
      unfold escDecode at he
      dsimp only at he
      split_ifs at he <;> simp_all

/-- Every model-accepted ignored escape, with the exact modeled reader endpoint. -/
theorem f652_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr : UInt32) (bs out : List UInt8) (j m : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 16 < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 112 ≤ s.toNat)
    (he : escDecode (bs.drop j) = some (out, m)) :
    code inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f652 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs j ∗ n ↦[wms][ 1062712 ] hexTable))
      (fun _ => ParseEscapeSuccessCost.successOps (bs.drop j) * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs (j + m) ∗ n ↦[wms][ 1062712 ] hexTable)) := by
  have hv : (escDecode (bs.drop j)).isSome = true := by simp only [he, Option.isSome_some]
  by_cases hu : ∃ tail, bs.drop j = 0x75 :: tail
  · obtain ⟨tail, hprefix⟩ := hu
    have ht : bs.drop (j + 1) = tail := by
      simpa [List.drop_drop, Nat.add_comm] using congrArg (List.drop 1) hprefix
    by_cases hhi : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54
    · obtain ⟨nv, r, hh, hn⟩ := hhi
      have hhi' : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54 := ⟨nv, r, hh, hn⟩
      rw [ht] at hh
      have hc := ParseEscapeSuccessCost.successOps_u1 _ _ _ nv hprefix hh hn
      have hcount : m = 11 := by
        simpa [consumed, hprefix, hh, hn] using (consumed_eq _ _ _ he).symm
      subst m
      rw [hc]
      exact f652_u1_success cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr bs j hde hlen hptr hs hv
        ⟨tail, hprefix⟩ hhi'
    · have hlo : ∀ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) → nv / 1024 ≠ 54 := by
        intro nv r hh hn
        exact hhi ⟨nv, r, hh, hn⟩
      have hlo' : ∀ nv r, hex4 tail = some (nv, r) → nv / 1024 ≠ 54 := by
        simpa only [ht] using hlo
      have hc := ParseEscapeSuccessCost.successOps_u0 _ _ hprefix hlo'
      have hcount : m = 5 := by
        have hl := consumed_eq _ _ _ he
        rw [hprefix] at hl
        cases hh : hex4 tail with
        | none => simpa [consumed, hh] using hl.symm
        | some v =>
          obtain ⟨nv, r⟩ := v
          simpa [consumed, hh, hlo' nv r hh] using hl.symm
      subst m
      rw [hc]
      exact f652_u0_success cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr bs j hde hlen hptr hs hv
        ⟨tail, hprefix⟩ hlo
  · have hnu : ∀ tail, bs.drop j ≠ 0x75 :: tail := by intro tail h; exact hu ⟨tail, h⟩
    have hhead : (bs.drop j).head? ≠ some 0x75 := by
      intro hh
      cases hl : bs.drop j with
      | nil => simp [hl] at hh
      | cons b tail =>
        simp only [hl, List.head?_cons, Option.some.injEq] at hh
        exact hnu tail (by rw [hl, hh])
    have hcount : m = 1 := by simpa only [consumed, if_neg hhead] using (consumed_eq _ _ _ he).symm
    subst m
    rw [ParseEscapeSuccessCost.successOps_nu _ hnu]
    exact f652_nu_success cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr bs j hde hlen hptr hs hv hnu

/-- Successful ignored escapes fit 200 regular operations per encoded byte, including the backslash. -/
theorem f652_success_linear (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr : UInt32) (bs out : List UInt8) (j m : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 16 < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 112 ≤ s.toNat)
    (he : escDecode (bs.drop j) = some (out, m)) :
    code inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f652 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs j ∗ n ↦[wms][ 1062712 ] hexTable))
      (fun _ => (200 * (m + 1)) * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
        rd n de ptr bs (j + m) ∗ n ↦[wms][ 1062712 ] hexTable)) := by
  apply (f652_success (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr bs out j m
    hde hlen hptr hs he).trans
  apply AllocGen.MFunSpec_cost
  intro args
  exact Nat.mul_le_mul_right cfg.regularOpCost (ParseEscapeSuccessCost.successOps_le _ _ _ he)

end Proof
end WNear.Binary.SerdeIgnoreEscape
