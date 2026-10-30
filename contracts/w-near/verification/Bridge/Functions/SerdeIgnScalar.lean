import Bridge.Functions.SerdeIgnScalarDone

/-! # The actual successful scalar dispatch of the complete ignored-value reader -/

namespace WNear.Binary.SerdeIgnScalar

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.SerdeRead (rd optByte)
open WNear.Binary.SerdeIgnValue (fr81 ob16 band255 eqb_zero dig_ne dig_lt)
open NearInterface.Json (isWhitespace stringBody)

/-- The last scalar byte test retains the actual invalid-value error path. -/
def digitBody : List Instr :=
  [.local_get 6, .i32_const 116, .i32_relop .eq, .br_if 0,
   .local_get 6, .i32_const 123, .i32_relop .eq, .br_if 5,
   .local_get 7, .i32_const 4294967248, .i32_binop .add, .i32_const 255, .i32_binop .and,
   .i32_const 10, .i32_relop .lt_u, .br_if 3,
   .local_get 1, .i32_const 10, .store .i32 none ⟨2, 16⟩,
   .local_get 0, .local_get 1, .i32_const 16, .i32_binop .add, .call 322, .local_set 6, .br 12]

def falseBody : List Instr :=
  [.local_get 6, .i32_const 102, .i32_relop .eq, .br_if 0,
   .local_get 6, .i32_const 110, .i32_relop .eq, .br_if 5, .block .empty digitBody,
   .local_get 0, .call 333, .local_get 0, .i32_const 1048580, .i32_const 3,
   .call 323, .local_tee 6, .i32_eqz, .br_if 6, .br 11]

def negativeBody : List Instr :=
  [.local_get 6, .i32_const 45, .i32_relop .eq, .br_if 0,
   .local_get 6, .i32_const 91, .i32_relop .eq, .br_if 3, .block .empty falseBody,
   .local_get 0, .call 333, .local_get 0, .i32_const 1048576, .i32_const 4,
   .call 323, .local_tee 6, .i32_eqz, .br_if 5, .br 10]

def stringBodyCode : List Instr :=
  [.local_get 5, .i64_const 16, .i64_binop .shr_u, .cvt .i32_wrap_i64, .local_tee 7,
   .i32_const 255, .i32_binop .and, .local_tee 6, .i32_const 34, .i32_relop .eq, .br_if 0,
   .block .empty [.block .empty negativeBody, .local_get 0, .call 333],
   .local_get 0, .call 83, .local_tee 6, .i32_eqz, .br_if 3, .br 8]

/-- The complete first block of the real value dispatch, including container and error branches. -/
def valueCode : List Instr :=
  [.block .empty [.block .empty
    ([.block .empty [.block .empty stringBodyCode, .local_get 0, .call 333,
        .local_get 0, .call 650, .local_tee 6, .i32_eqz, .br_if 2, .br 7]] ++
      SerdeIgnSegments.openCode ++ [.br 2]),
    .local_get 0, .call 333, .local_get 0, .i32_const 1048583, .i32_const 3,
    .call 323, .local_tee 6, .br_if 5]]

theorem valueCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 2]).take 1 = valueCode := by rfl

/-- The real value-loop presence guard, retaining its positioned EOF error path. -/
def presentCode : List Instr :=
  [.block .empty [.local_get 5, .i64_const 256, .i64_binop .and, .i64_const 0,
    .i64_relop .ne, .br_if 0, .local_get 1, .i32_const 5, .store .i32 none ⟨2, 16⟩,
    .local_get 0, .local_get 1, .i32_const 16, .i32_binop .add, .call 322, .local_set 6, .br 4]]

theorem presentCode_at : ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 1).take 1 =
    presentCode := by rfl

/-- Scalar dispatch followed by completion is the entire actual value-dispatch body. -/
theorem dispatchBody_at : SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 2] =
    valueCode ++ SerdeIgnScalarDone.scalarCode := by rfl

/-- The actual enclosing value-dispatch block in the outer loop. -/
def dispatchBlock : List Instr := [.block .empty (valueCode ++ SerdeIgnScalarDone.scalarCode)]

theorem dispatchBlock_at : ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 2).take 1 =
    dispatchBlock := by rfl

/-- A successful non-container value exposes its scalar result and full pending-frame continuation. -/
theorem scalar_step (N : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (b : UInt8) (t : List UInt8) (hskip : NearInterface.Json.skipWhitespace bs = b :: t)
    (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames bs = some (r, ops)) :
    ∃ rest, vSkip (b :: t) = some rest ∧
      SerdeIgnMachineTrace.pop false frames rest
        (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames t) =
          some (r, ops) := by
  simp only [SerdeIgnMachineTrace.run, hskip] at h
  split at h
  · rename_i t' ht
    cases ht
    exact absurd rfl hb5B
  · rename_i t' ht
    cases ht
    exact absurd rfl hb7B
  · simpa only [Option.bind_eq_some_iff] using h

/-- The complete trace yields the concrete scalar reader's exact cursor and a monotone continuation endpoint. -/
theorem scalar_indices (N : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i : Nat) (b : UInt8) (hb : bs[i]? = some b) (hws : isWhitespace b = false)
    (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames
      (bs.drop i) = some (r, ops)) :
    ∃ rest e, vSkip (bs.drop i) = some rest ∧ e = bs.length - rest.length ∧
      i < e ∧ e ≤ bs.length - r.length ∧
      SerdeIgnMachineTrace.pop false frames (bs.drop e)
        (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames t) =
          some (r, ops) := by
  have hi := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hi hb
  have hskip : NearInterface.Json.skipWhitespace (bs.drop i) = b :: bs.drop (i + 1) := by
    rw [hdr, WNear.JsonFuel.skip_of_not _ hws]
  obtain ⟨rest, hv, hpop⟩ := scalar_step N frames (bs.drop i) r ops b _ hskip hb5B hb7B h
  rw [← hdr] at hv
  have hsuf := IgnoreShallow.vSkip_suf hv
  have hdrop := JsonSuffix.drop_suf' hsuf
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hg := SerdeIgnMachineTrace.good_pop false frames rest
    (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames t)
    (fun f frames t => SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
      (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N (.cont f) frames t)
  have hrest := (hg r ops hpop).2.1
  refine ⟨rest, bs.length - rest.length, hv, rfl, by omega, by omega, ?_⟩
  rw [hdrop]
  exact hpop

/-- Scalar entry, including whitespace, fits the existing inside-container value allowance. -/
theorem pending_cost (cfg : WasmConfig) (w consumed : Nat) (hconsumed : 0 < consumed) :
    (125 + 96 * w) * cfg.regularOpCost + 7 * cfg.regularOpCost +
      (470 * consumed - 72) * cfg.regularOpCost ≤
        (60 + 470 * (w + consumed)) * cfg.regularOpCost := by
  have h : 125 + 96 * w + 7 + (470 * consumed - 72) ≤ 60 + 470 * (w + consumed) := by omega
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- Scalar entry plus the actual success epilogue fits the existing top-level value allowance. -/
theorem top_cost (cfg : WasmConfig) (w consumed : Nat) (hconsumed : 0 < consumed) :
    (125 + 96 * w) * cfg.regularOpCost + 7 * cfg.regularOpCost +
      (470 * consumed - 30) * cfg.regularOpCost + 7 * cfg.regularOpCost ≤
        (109 + 470 * (w + consumed)) * cfg.regularOpCost := by
  have h : 125 + 96 * w + 7 + (470 * consumed - 30) + 7 ≤ 109 + 470 * (w + consumed) := by omega
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- Every successful scalar follows the actual dispatch to its exact model endpoint.
The allowance leaves 81 operations per scalar for surrounding loop/control costs. -/
theorem scalar (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr l3 l4 l6 l7 l8 : UInt32)
    (bs rest : List UInt8) (i e : Nat) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hb : bs[i]? = some b) (he : e = bs.length - rest.length)
    (hws : isWhitespace b = false) (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hv : vSkip (bs.drop i) = some rest) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
      credits Cg ((470 * (e - i) - 81) * cfg.regularOpCost + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some b)) l6 l7 l8) [] valueCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  have hlt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hlt hb
  have hr1s := IgnoreShallow.vSkip_suf hv
  have hp1 : bs.drop e = rest := by rw [he]; exact JsonSuffix.drop_suf' hr1s
  have hP1 : bs.length - rest.length = e := he.symm
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hie : i < e := by omega
  have hmin : 470 * cfg.regularOpCost ≤ 470 * (e - i) * cfg.regularOpCost :=
    Nat.mul_le_mul_right cfg.regularOpCost (by omega)
  rw [hdr] at hv
  iintro ⟨#HC, #CE, #F652, Hc, Hg, SB, Hrd, He, Hhex, Hid, HF⟩
  iunfold SerdeIgnValue.code81 at HC
  icases HC with ⟨#HN, #F339, #F82, #F674, #F85, #F84, #HA, #F650, #F323, #F673, #F83⟩
  ihave #HN' := HN
  iunfold SerdeIgnNum.numCode at HN'
  icases HN' with ⟨#F324, #F332, #F333, #F329, #F88, #F87, #F86, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha333 := hm.funcs 333 (by decide)
  have ha83 := hm.funcs 83 (by decide)
  have ha650 := hm.funcs 650 (by decide)
  have ha323 := hm.funcs 323 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t32 : types[32]!.params.length = 1 := rfl
  have t15 : types[15]!.params.length = 3 := rfl
  rw [Nat.sub_mul]
  unfold valueCode stringBodyCode negativeBody falseBody digitBody SerdeIgnSegments.openCode
  simp only [List.cons_append, List.nil_append, fr81]
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [ob16 b, band255 b]
  rcases SerdeIgnPure.vSkip_byte hws hv with ⟨rfl, s0, hsb⟩ | ⟨rfl, hix⟩ | ⟨hdg, hix⟩ | ⟨rfl, hlit⟩ |
      ⟨rfl, hlit⟩ | ⟨rfl, hlit⟩ | rfl | rfl
  · -- a string: 333, 650
    have hsb' : stringBody (bs.drop (i + 1)) [] = some (s0, rest) := hsb
    have hrestLen := WNear.JsonFuel.stringBody_len hsb'
    simp only [List.length_drop] at hrestLen
    have hpos : i + 1 < e := by omega
    have hS : (120 + 300 * (e - (i + 1))) * cfg.regularOpCost + 300 * cfg.regularOpCost ≤
        470 * (e - i) * cfg.regularOpCost := by
      have he : e - i = (e - (i + 1)) + 1 := by omega
      have hc : 120 + 300 * (e - (i + 1)) + 300 ≤ 470 * (e - i) := by omega
      simpa only [Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost hc
    generalize hS' : 470 * (e - i) * cfg.regularOpCost = S at hS ⊢
    generalize hM : (120 + 300 * (e - (i + 1))) * cfg.regularOpCost = M at hS
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs i hlt (by omega)
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    have s650 := SerdeIgnoreString.f650_model (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
      (by omega) Cg gt s de ptr bs rest s0 (i + 1) hlen hptr hde hs (by omega) hsb'
    rw [hP1, hM] at s650
    mstep
    ihave #S650 := s650 $$ [CE F652]
    · iframe CE F652
    clear s650
    mcall S650 using [Hg SB Hrd He Hhex]
    · iframe Hg SB Hrd He Hhex
    icases HQ with ⟨%hrs, Hg, SB, Hrd, He, Hhex⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    mcredits R
    iframe Hc Hg SB Hrd He Hhex Hid HF
    ipureintro; trivial
  · -- `-`: 333, then 83
    have hlt1 : i + 1 < bs.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hix
      simp [SerdeNumModel.intR] at hix
    have hK := Nat.mul_le_mul_right cfg.regularOpCost (SerdeIgnInt.cost83_le hlt1 hix)
    rw [hP1, Nat.add_mul, Nat.add_mul] at hK
    have eS : 470 * (e - i) * cfg.regularOpCost =
        470 * cfg.regularOpCost + 470 * (e - (i + 1)) * cfg.regularOpCost := by
      rw [show e - i = (e - (i + 1)) + 1 by omega]; ring
    rw [eS]
    generalize hS' : 470 * (e - (i + 1)) * cfg.regularOpCost = S at hK ⊢
    generalize hK83 : SerdeIgnInt.cost83 bs (i + 1) rest * cfg.regularOpCost = K83 at hK
    have s83 := SerdeIgnInt.f83_acc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm
      (by omega) Cg gt s de ptr bs rest (i + 1) (by omega) hptr (by omega) hlt1 hix
    rw [hK83, hP1] at s83
    ihave #S83 := s83 $$ HN
    clear s83
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs i hlt (by omega)
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep
    mcall S83 using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    mcredits R
    iframe Hc Hg SB Hrd He Hhex Hid HF
    ipureintro; trivial
  · -- a digit: 83
    have hix' : NearInterface.Json.isDigit b = true ∧ SerdeNumModel.intR (bs.drop i) = some rest := by
      rw [hdr]; exact ⟨hdg, hix⟩
    have hK := Nat.mul_le_mul_right cfg.regularOpCost (SerdeIgnInt.cost83_le hlt hix'.2)
    rw [hP1, Nat.add_mul, Nat.add_mul] at hK
    generalize hS' : 470 * (e - i) * cfg.regularOpCost = S at hK ⊢
    generalize hK83 : SerdeIgnInt.cost83 bs i rest * cfg.regularOpCost = K83 at hK
    have s83 := SerdeIgnInt.f83_acc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm
      (by omega) Cg gt s de ptr bs rest i (by omega) hptr (by omega) hlt hix'.2
    rw [hK83, hP1] at s83
    ihave #S83 := s83 $$ HN
    clear s83
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with exact dig_lt b hix'.1
    mstep
    mcall S83 using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    mcredits R
    iframe Hc Hg SB Hrd He Hhex Hid HF
    ipureintro; trivial
  · -- `true`: 333, then 323 on `rue`
    have hpos : e = i + 4 := by
      have e1 := congrArg List.length hlit; have e2 := congrArg List.length hp1
      simp at e1 e2; omega
    have hlitk : ∀ k, k < 3 → bs[i + 1 + k]? = SerdeIdent.identBytes[4 + k]? := by
      intro k hk
      rw [← List.getElem?_drop, hlit]
      interval_cases k <;> rfl
    have s323 := SerdeIdent.f323_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n g hn hg
      (A 324) (A 673) (hm.funcs 324 (by decide)) (hm.funcs 673 (by decide)) (by omega) Cg gt s de ptr
      1048580 3 bs (i + 1) 4 3 (by rfl) (by rfl) (by decide) (by omega) hlitk (by omega) hptr (by omega) (by omega)
    simp only [SerdeIdent.cost323, Nat.reduceMul, Nat.reduceAdd] at s323
    rw [show 470 * (e - i) * cfg.regularOpCost = 1880 * cfg.regularOpCost by
      rw [show e - i = 4 by omega]]
    icases stk_split n (s.toNat - 128) 96 32 $$ SB with ⟨SB1, SB2⟩
    ihave SB2 := stk_addr (show s.toNat - 128 + 96 = s.toNat - 32 by omega) $$ SB2
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs i hlt (by omega)
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    mcall s323 using [Hg SB2 Hrd Hid]
    · iframe Hg SB2 Hrd Hid
    icases HQ with ⟨%hrs, Hg, SB2, Hrd, Hid⟩
    subst hrs
    ihave SB2 := stk_addr (show s.toNat - 32 = s.toNat - 128 + 96 by omega) $$ SB2
    ihave SB := stk_join n (s.toNat - 128) 96 32 $$ [SB1 SB2]
    · iframe SB1 SB2
    rw [show i + 1 + 3 = e by omega]
    mstep; mstep
    mstep_taken with decide
    mcredits R
    iframe Hc Hg SB Hrd He Hhex Hid HF
    ipureintro; trivial
  · -- `false`: 333, then 323 on `alse`
    have hpos : e = i + 5 := by
      have e1 := congrArg List.length hlit; have e2 := congrArg List.length hp1
      simp at e1 e2; omega
    have hlitk : ∀ k, k < 4 → bs[i + 1 + k]? = SerdeIdent.identBytes[0 + k]? := by
      intro k hk
      rw [← List.getElem?_drop, hlit]
      interval_cases k <;> rfl
    have s323 := SerdeIdent.f323_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n g hn hg
      (A 324) (A 673) (hm.funcs 324 (by decide)) (hm.funcs 673 (by decide)) (by omega) Cg gt s de ptr
      1048576 4 bs (i + 1) 0 4 (by rfl) (by rfl) (by decide) (by omega) hlitk (by omega) hptr (by omega) (by omega)
    simp only [SerdeIdent.cost323, Nat.reduceMul, Nat.reduceAdd] at s323
    rw [show 470 * (e - i) * cfg.regularOpCost = 2350 * cfg.regularOpCost by
      rw [show e - i = 5 by omega]]
    icases stk_split n (s.toNat - 128) 96 32 $$ SB with ⟨SB1, SB2⟩
    ihave SB2 := stk_addr (show s.toNat - 128 + 96 = s.toNat - 32 by omega) $$ SB2
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs i hlt (by omega)
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    mcall s323 using [Hg SB2 Hrd Hid]
    · iframe Hg SB2 Hrd Hid
    icases HQ with ⟨%hrs, Hg, SB2, Hrd, Hid⟩
    subst hrs
    ihave SB2 := stk_addr (show s.toNat - 32 = s.toNat - 128 + 96 by omega) $$ SB2
    ihave SB := stk_join n (s.toNat - 128) 96 32 $$ [SB1 SB2]
    · iframe SB1 SB2
    rw [show i + 1 + 4 = e by omega]
    mstep; mstep
    mstep_taken with decide
    mcredits R
    iframe Hc Hg SB Hrd He Hhex Hid HF
    ipureintro; trivial
  · -- `null`: 333, then 323 on `ull`
    have hpos : e = i + 4 := by
      have e1 := congrArg List.length hlit; have e2 := congrArg List.length hp1
      simp at e1 e2; omega
    have hlitk : ∀ k, k < 3 → bs[i + 1 + k]? = SerdeIdent.identBytes[7 + k]? := by
      intro k hk
      rw [← List.getElem?_drop, hlit]
      interval_cases k <;> rfl
    have s323 := SerdeIdent.f323_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n g hn hg
      (A 324) (A 673) (hm.funcs 324 (by decide)) (hm.funcs 673 (by decide)) (by omega) Cg gt s de ptr
      1048583 3 bs (i + 1) 7 3 (by rfl) (by rfl) (by decide) (by omega) hlitk (by omega) hptr (by omega) (by omega)
    simp only [SerdeIdent.cost323, Nat.reduceMul, Nat.reduceAdd] at s323
    rw [show 470 * (e - i) * cfg.regularOpCost = 1880 * cfg.regularOpCost by
      rw [show e - i = 4 by omega]]
    icases stk_split n (s.toNat - 128) 96 32 $$ SB with ⟨SB1, SB2⟩
    ihave SB2 := stk_addr (show s.toNat - 128 + 96 = s.toNat - 32 by omega) $$ SB2
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs i hlt (by omega)
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    mcall s323 using [Hg SB2 Hrd Hid]
    · iframe Hg SB2 Hrd Hid
    icases HQ with ⟨%hrs, Hg, SB2, Hrd, Hid⟩
    subst hrs
    ihave SB2 := stk_addr (show s.toNat - 32 = s.toNat - 128 + 96 by omega) $$ SB2
    ihave SB := stk_join n (s.toNat - 128) 96 32 $$ [SB1 SB2]
    · iframe SB1 SB2
    rw [show i + 1 + 3 = e by omega]
    mstep
    mstep_not_taken with decide
    mcredits R
    iframe Hc Hg SB Hrd He Hhex Hid HF
    ipureintro; trivial
  · exact absurd rfl hb5B
  · exact absurd rfl hb7B

set_option maxRecDepth 100000 in
/-- Scalar dispatch retains the entire complete-machine continuation and its unchanged frame-growth credits. -/
theorem scalar_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 l8 : UInt32)
    (bs r frames : List UInt8) (ops : List SerdeIgnTrace.Op) (i F N : Nat) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hb : bs[i]? = some b) (hws : isWhitespace b = false) (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames
      (bs.drop i) = some (r, ops)) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
      credits Cg ((470 * (bs.length - r.length - i) - 81) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap (SerdeIgnMachineTrace.depth .val frames) ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some b)) l6 l7 l8) [] valueCode
      { normal := fun vs fr => iprop(∃ e,
          ⌜i < e ∧ e ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.pop false frames (bs.drop e)
              (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
                (.cont f) frames t) = some (r, ops)⌝ ∗
          credits Cg (470 * (bs.length - r.length - e) * cfg.regularOpCost +
            SerdeIgnTrace.extraCost cfg F cap (SerdeIgnMachineTrace.depth .val frames) ops + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  obtain ⟨rest, e, hv, he, hie, heQ, hnext⟩ := scalar_indices N frames bs r ops i b hb hws hb5B hb7B hmodel
  have hsplit : bs.length - r.length - i = (e - i) + (bs.length - r.length - e) := by omega
  have hcost : (470 * (e - i) - 81) * cfg.regularOpCost +
      (470 * (bs.length - r.length - e) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap (SerdeIgnMachineTrace.depth .val frames) ops + R) =
      (470 * (bs.length - r.length - i) - 81) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap (SerdeIgnMachineTrace.depth .val frames) ops + R := by
    rw [hsplit]
    have he81 : 81 ≤ 470 * (e - i) := by omega
    rw [Nat.mul_add]
    rw [show 470 * (e - i) + 470 * (bs.length - r.length - e) - 81 =
      (470 * (e - i) - 81) + 470 * (bs.length - r.length - e) by omega, Nat.add_mul]
    omega
  iintro ⟨#HC, #CE, #F652, Hc, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex Hid HF]
  · iapply scalar cfg lim d inst mi A n g ta hm hd Cg
      (470 * (bs.length - r.length - e) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap (SerdeIgnMachineTrace.depth .val frames) ops + R)
      gt de s ptr l3 l4 l6 l7 l8 bs rest i e b Fr hs hde hlen hptr hb he hws hb5B hb7B hv
    iframe HC CE F652 Hg H128 Hrd He Hhex Hid HF
    rw [hcost]
    iexact Hc
  iunfold Post.wand
  isplit
  · iintro %vs %fr H
    iexists e
    isplitr
    · ipureintro; exact ⟨hie, heQ, hnext⟩
    iexact H
  isplit
  · iintro %k %vs %fr H; iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

set_option maxRecDepth 100000 in
/-- The actual presence guard accepts a peeked byte without consuming it or touching caller resources. -/
theorem present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l3 l4 l6 l7 l8 : UInt32) (b : UInt8) (Fr : IProp GF) :
    credits Cg (7 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some b)) l6 l7 l8) [] presentCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some b)) l6 l7 l8⌝ ∗ Fr) } := by
  iintro ⟨Hc, HF⟩
  unfold presentCode
  simp only [fr81]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with exact SerdeIgnValue.some_ne b
  mcredits R
  iframe Hc HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
/-- The entire actual scalar-dispatch body returns a pending container to its continuation.
This composes the reader with its seven-operation completion tail. -/
theorem pending (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr l3 l6 l7 l8 : UInt32)
    (bs rest : List UInt8) (i e : Nat) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hb : bs[i]? = some b) (he : e = bs.length - rest.length)
    (hws : isWhitespace b = false) (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hv : vSkip (bs.drop i) = some rest) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
      credits Cg ((470 * (e - i) - 74) * cfg.regularOpCost + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 0 (optByte (some b)) l6 l7 l8) []
      (valueCode ++ SerdeIgnScalarDone.scalarCode)
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hie : i < e := by omega
  have hc : (470 * (e - i) - 74) * cfg.regularOpCost + R =
      (470 * (e - i) - 81) * cfg.regularOpCost + (7 * cfg.regularOpCost + R) := by
    have heq : 470 * (e - i) - 74 = (470 * (e - i) - 81) + 7 := by omega
    rw [heq, Nat.add_mul]; omega
  iintro ⟨#HC, #CE, #F652, Hc, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex Hid HF]
  · iapply scalar cfg lim d inst mi A n g ta hm hd Cg (7 * cfg.regularOpCost + R)
      gt de s ptr l3 0 l6 l7 l8 bs rest i e b Fr hs hde hlen hptr hb he hws hb5B hb7B hv
    iframe HC CE F652 Hg H128 Hrd He Hhex Hid HF
    rw [← hc]
    iexact Hc
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
    subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply SerdeIgnScalarDone.scalar_pending cfg lim d inst mi Cg R de s l3 0 b.toUInt32 l8
      (optByte (some b)) (iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
    iframe Hc Hg H128 Hrd He Hhex Hid HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; simp only [Post.mseq_ret]; iexact H
  · iintro H; simp only [Post.mseq_trap]; iexact H

set_option maxRecDepth 100000 in
/-- The complete actual scalar-dispatch body takes the top-level empty-stack success branch.
The cleared scratch allocation and all 160 caller stack bytes are retained for the epilogue. -/
theorem top (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr p cap l3 l6 l7 l8 : UInt32)
    (bs rest : List UInt8) (i e maxP hl F : Nat) (live : List (Nat × Nat)) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32) (hs32 : s.toNat + 32 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hb : bs[i]? = some b) (he : e = bs.length - rest.length)
    (hws : isWhitespace b = false) (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hv : vSkip (bs.drop i) = some rest) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
      credits Cg ((470 * (e - i) - 31) * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 1 (optByte (some b)) l6 l7 l8) []
      (valueCode ++ SerdeIgnScalarDone.scalarCode)
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 3 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 1 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hie : i < e := by omega
  have hc : (470 * (e - i) - 31) * cfg.regularOpCost + R =
      (470 * (e - i) - 81) * cfg.regularOpCost + (50 * cfg.regularOpCost + R) := by
    have heq : 470 * (e - i) - 31 = (470 * (e - i) - 81) + 50 := by omega
    rw [heq, Nat.add_mul]; omega
  iintro ⟨#HC, #CE, #F652, Hc, H32, Hst, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hg H128 Hrd He Hhex Hid HF]
  · iapply scalar cfg lim d inst mi A n g ta hm hd Cg (50 * cfg.regularOpCost + R)
      gt de s ptr l3 1 l6 l7 l8 bs rest i e b
      (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗ Fr))
      hs (by omega) hlen hptr hb he hws hb5B hb7B hv
    iframe HC CE F652 Hg H128 Hrd He Hhex Hid H32 Hst HF
    rw [← hc]
    iexact Hc
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, Hid, H32, Hst, HF⟩
    subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply SerdeIgnScalarDone.scalar_top cfg lim d inst mi A n g ta hm (by omega) Cg R
      de s p cap l3 0 b.toUInt32 l8 (optByte (some b)) maxP hl F live
      (iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) hs32 hde
    iframe HC Hc H32 Hst Hg H128 Hrd He Hhex Hid HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; simp only [Post.mseq_ret]; iexact H
  · iintro H; simp only [Post.mseq_trap]; iexact H

set_option maxRecDepth 100000 in
/-- The enclosing block translates pending scalar completion into normal container-phase entry. -/
theorem pending_block (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr l3 l6 l7 l8 : UInt32)
    (bs rest : List UInt8) (i e : Nat) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hb : bs[i]? = some b) (he : e = bs.length - rest.length)
    (hws : isWhitespace b = false) (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hv : vSkip (bs.drop i) = some rest) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
      credits Cg ((470 * (e - i) - 72) * cfg.regularOpCost + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 0 (optByte (some b)) l6 l7 l8) []
      dispatchBlock
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hie : i < e := by omega
  have hmin : 470 * cfg.regularOpCost ≤ 470 * (e - i) * cfg.regularOpCost :=
    Nat.mul_le_mul_right cfg.regularOpCost (by omega)
  iintro ⟨#HC, #CE, #F652, Hc, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  unfold dispatchBlock
  rw [Nat.sub_mul]
  mstep
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex Hid HF]
  · iapply pending cfg lim d inst mi A n g ta hm hd Cg (cfg.regularOpCost + R)
      gt de s ptr l3 l6 l7 l8 bs rest i e b Fr hs hde hlen hptr hb he hws hb5B hb7B hv
    iframe HC CE F652 Hg H128 Hrd He Hhex Hid HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    rw [Nat.sub_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
    subst hk; subst hvs; subst hfr
    simp only [Post.mblock_br_zero, List.length_nil, List.drop_nil, List.nil_append]
    isplitr
    · ipureintro; omega
    mpay
    iframe Hc Hg H128 Hrd He Hhex Hid HF
    ipureintro; trivial
  isplit
  · iintro %vs %fr H; simp only [Post.mblock_ret]; iexact H
  · iintro H; simp only [Post.mblock_trap]; iexact H

set_option maxRecDepth 100000 in
/-- The enclosing block translates top-level scalar completion to the actual success exit. -/
theorem top_block (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr p cap l3 l6 l7 l8 : UInt32)
    (bs rest : List UInt8) (i e maxP hl F : Nat) (live : List (Nat × Nat)) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32) (hs32 : s.toNat + 32 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hb : bs[i]? = some b) (he : e = bs.length - rest.length)
    (hws : isWhitespace b = false) (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hv : vSkip (bs.drop i) = some rest) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
      credits Cg ((470 * (e - i) - 30) * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 1 (optByte (some b)) l6 l7 l8) []
      dispatchBlock
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 2 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 1 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hie : i < e := by omega
  have hmin : 470 * cfg.regularOpCost ≤ 470 * (e - i) * cfg.regularOpCost :=
    Nat.mul_le_mul_right cfg.regularOpCost (by omega)
  iintro ⟨#HC, #CE, #F652, Hc, H32, Hst, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  unfold dispatchBlock
  rw [Nat.sub_mul]
  mstep
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hg H128 Hrd He Hhex Hid HF]
  · iapply top cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr p cap l3 l6 l7 l8
      bs rest i e maxP hl F live b Fr hs hde hs32 hlen hptr hb he hws hb5B hb7B hv
    iframe HC CE F652 H32 Hst Hg H128 Hrd He Hhex Hid HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    rw [Nat.sub_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, H32, Hst, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
    subst hk; subst hvs; subst hfr
    simp only [Post.mblock_br_succ, List.nil_append]
    iframe Hc H32 Hst Hg H128 Hrd He Hhex Hid HF
    ipureintro; trivial
  isplit
  · iintro %vs %fr H; simp only [Post.mblock_ret]; iexact H
  · iintro H; simp only [Post.mblock_trap]; iexact H

end Proof
end WNear.Binary.SerdeIgnScalar
