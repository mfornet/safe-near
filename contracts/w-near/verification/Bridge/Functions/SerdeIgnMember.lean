import Bridge.Functions.SerdeIgnSegments
import Bridge.Functions.SerdeIgnoreString

/-! # The actual ignored-container member/key path back to the value loop -/

namespace WNear.Binary.SerdeIgnMember

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen optByte)
open WNear.Binary.SerdeIgnValue (fr81)

/-- 81's successful whitespace/peek guards, retaining their actual rejecting branches. -/
def peekCode : List Instr :=
  [.block .empty [.local_get 0, .call 339, .local_tee 5, .i64_const 1, .i64_binop .and,
      .i64_eqz, .br_if 0, .local_get 5, .i64_const 32, .i64_binop .shr_u,
      .cvt .i32_wrap_i64, .local_set 6, .br 4],
   .block .empty [.local_get 5, .i64_const 256, .i64_binop .and, .i64_const 0,
      .i64_relop .ne, .br_if 0, .local_get 1, .i32_const 3, .store .i32 none ⟨2, 16⟩,
      .local_get 0, .local_get 1, .i32_const 16, .i32_binop .add, .call 322, .local_set 6, .br 4]]

/-- The complete member tail, including the array fast path and the object key/colon reader. -/
def memberCode : List Instr :=
  [.i32_const 0, .local_set 4, .i32_const 1, .local_set 3, .local_get 8,
    .i32_const 255, .i32_binop .and, .i32_const 123, .i32_relop .ne, .br_if 0] ++
  peekCode ++
  [.local_get 5, .i64_const 16711680, .i64_binop .and, .i64_const 2228224,
    .i64_relop .ne, .br_if 1, .local_get 0, .call 333, .local_get 0, .call 650,
    .local_tee 6, .br_if 3] ++
  peekCode ++
  [.block .empty [.local_get 5, .i64_const 16711680, .i64_binop .and, .i64_const 3801088,
    .i64_relop .ne, .br_if 0, .local_get 0, .call 333, .br 1]]

/-- The checked member tail is the actual rest of 81's value-loop body after its four blocks. -/
theorem memberCode_eq : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 4 = memberCode := by rfl

/-- Byte-dependent successful cost, with both whitespace scans and the full escaped key reader. -/
def cost (cfg : WasmConfig) (i q e j : Nat) : Nat :=
  (600 + 96 * (q - i) + 300 * (e - (q + 1)) + 96 * (j - e)) * cfg.regularOpCost

/-- The successful key/colon path leaves the value-loop entry allowance inside the existing per-byte budget. -/
theorem cost_le_value (cfg : WasmConfig) (i q e j : Nat) (hq : i ≤ q) (he : q + 1 ≤ e) (hj : e ≤ j) :
    cost cfg i q e j + 60 * cfg.regularOpCost ≤ 470 * (j + 1 - i) * cfg.regularOpCost := by
  have h : 600 + 96 * (q - i) + 300 * (e - (q + 1)) + 96 * (j - e) + 60 ≤ 470 * (j + 1 - i) := by omega
  simpa only [cost, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- A successful traced key transition supplies the exact syntactic key and colon endpoints. -/
theorem key_parts {α : Type} (bs : List UInt8) (k : List UInt8 → Option α) (x : α)
    (h : SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody bs k = some x) :
    ∃ r1 key rest r3,
      NearInterface.Json.skipWhitespace bs = 0x22 :: r1 ∧
      NearInterface.Json.stringBody r1 [] = some (key, rest) ∧
      NearInterface.Json.skipWhitespace rest = 0x3A :: r3 ∧ k r3 = some x := by
  unfold SerdeIgnMachineTrace.key at h
  split at h
  · rename_i r1 h1
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨rest, h2, h⟩ := h
    simp only [SerdeIgnMachineTrace.keyBody, Option.map_eq_some_iff] at h2
    obtain ⟨⟨key, rest'⟩, hkey, he⟩ := h2
    dsimp only at he
    subst he
    split at h
    · rename_i r3 h3
      exact ⟨r1, key, rest', r3, h1, hkey, h3, h⟩
    · cases h
  · cases h

/-- Complete-machine key success derives every cursor premise of the concrete object-member segment. -/
theorem key_indices {α : Type} (bs : List UInt8) (i : Nat) (k : List UInt8 → Option α) (x : α)
    (hi : i ≤ bs.length)
    (h : SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody (bs.drop i) k = some x) :
    ∃ (q e j : Nat) (key : Option String) (rest : List UInt8),
      q = i + wsLen (bs.drop i) ∧ e = bs.length - rest.length ∧ j = e + wsLen (bs.drop e) ∧
      bs[q]? = some 0x22 ∧ bs[j]? = some 0x3A ∧
      NearInterface.Json.stringBody (bs.drop (q + 1)) [] = some (key, rest) ∧
      q + 1 ≤ e ∧ k (bs.drop (j + 1)) = some x := by
  obtain ⟨r1, key, rest, r3, h1, hkey, h3, hk⟩ := key_parts _ _ _ h
  let q := i + wsLen (bs.drop i)
  have hq : NearInterface.Json.skipWhitespace (bs.drop i) = bs.drop q := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
  have hquote : bs[q]? = some 0x22 := (SerdeStructLoop.drop_cons (hq.symm.trans h1)).1
  have hq_lt := SerdeNextKey.getElem_lt hquote
  have hr1 : r1 = bs.drop (q + 1) := by
    rw [hq, SerdeIgnInt.drop_cons hq_lt hquote] at h1
    exact (List.cons.inj h1).2.symm
  rw [hr1] at hkey
  let e := bs.length - rest.length
  have hr2 : rest = bs.drop e := (JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hkey)).symm
  let j := e + wsLen (bs.drop e)
  have hj : NearInterface.Json.skipWhitespace rest = bs.drop j := by
    rw [hr2, SerdeRead.skipWhitespace_eq, List.drop_drop]
  have hcolon : bs[j]? = some 0x3A := (SerdeStructLoop.drop_cons (hj.symm.trans h3)).1
  have hj_lt := SerdeNextKey.getElem_lt hcolon
  have hr3 : r3 = bs.drop (j + 1) := by
    rw [hj, SerdeIgnInt.drop_cons hj_lt hcolon] at h3
    exact (List.cons.inj h3).2.symm
  have hlen := WNear.JsonFuel.stringBody_len hkey
  simp only [List.length_drop] at hlen
  refine ⟨q, e, j, key, rest, rfl, rfl, rfl, hquote, hcolon, hkey, ?_, ?_⟩
  · dsimp only [e]; omega
  · rw [← hr3]; exact hk

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def code (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(SerdeIgnSegments.code n maxP inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
    A 652 ↪[wf] FuncInst.wasm types[32]! inst f652)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code (GF := GF) n maxP inst mi A) := by
  unfold code; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- An array's next value reenters the actual outer loop without changing the reader or caller resources. -/
theorem array_next (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l3 l4 l6 l7 : UInt32) (l5 : UInt64) (Fr : IProp GF) :
    credits Cg (10 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 0x5B) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 l5 l6 l7 0x5B⌝ ∗ Fr) } := by
  iintro ⟨Hc, HF⟩
  unfold memberCode
  simp only [List.cons_append, List.nil_append, fr81]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mcredits R
  iframe Hc HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A complete ignored object key (including escapes or invalid raw UTF-8) and colon reenter the value loop. -/
theorem object_next (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (maxP i q e j : Nat) (bs rest : List UInt8) (key : Option String) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (he : e = bs.length - rest.length)
    (hj : j = e + wsLen (bs.drop e)) (hquote : bs[q]? = some 0x22) (hcolon : bs[j]? = some 0x3A)
    (hmodel : NearInterface.Json.stringBody (bs.drop (q + 1)) [] = some (key, rest)) :
    code (GF := GF) n maxP inst mi A ∗ credits Cg (cost cfg i q e j + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 0x7B) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some 0x3A)) 0 l7 0x7B⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs (j + 1) ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hquote
  have hj_lt := SerdeNextKey.getElem_lt hcolon
  have he_le : e ≤ bs.length := by omega
  have hw1 : wsLen (bs.drop i) = q - i := by omega
  have hw2 : wsLen (bs.drop e) = j - e := by omega
  have hiq : i + (q - i) = q := by omega
  have hej : e + (j - e) = j := by omega
  have reader := SerdeIgnoreString.f650_model (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt s de ptr bs rest key (q + 1) hlen hptr hde hs (by omega) hmodel
  rw [← he] at reader
  iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
  iunfold code at HC
  icases HC with ⟨#CS, #CE, #F652⟩
  iunfold SerdeIgnSegments.code at CS
  icases CS with ⟨#C81, -⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, #F339, -, -, -, -, -, #F650, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, #F332, #F333, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha650 := hm.funcs 650 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  have t32 : types[32]!.params.length = 1 := rfl
  unfold cost
  simp only [Nat.add_mul] at reader ⊢
  generalize hWS1 : 96 * (q - i) * cfg.regularOpCost = WS1
  generalize hM : 300 * (e - (q + 1)) * cfg.regularOpCost = M at reader ⊢
  generalize hWS2 : 96 * (j - e) * cfg.regularOpCost = WS2
  unfold memberCode peekCode
  simp only [List.cons_append, List.nil_append, fr81]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  repeat mstep
  have peek := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! rfl inst mi n hn
    (A 332) (A 333) (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs i hi (by omega) hptr hde
  rw [hw1, Nat.add_mul, hWS1] at peek
  mcall peek using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hiq, hquote]
  clear peek
  repeat mstep
  mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs q hq_lt
    (by omega) hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  repeat mstep
  mcall reader using [Hg H128 Hrd He Hhex]
  · iframe Hg H128 Hrd He Hhex
  icases HQ with ⟨%hrs, Hg, H128, Hrd, He, Hhex⟩
  subst hrs
  clear reader hM
  repeat mstep
  have peek := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! rfl inst mi n hn
    (A 332) (A 333) (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs e he_le (by omega) hptr hde
  rw [hw2, Nat.add_mul, hWS2] at peek
  mcall peek using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hej, hcolon]
  clear peek
  repeat mstep
  mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs j hj_lt
    (by omega) hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hg H128 Hrd He Hhex HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
/-- Complete-machine key success drives the real member path with its remaining byte and growth credits. -/
theorem object_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody (bs.drop i)
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x7B :: frames)) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (470 * (bs.length - r.length - i) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 0x7B) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ j,
          ⌜i ≤ j + 1 ∧ j + 1 ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x7B :: frames)
              (bs.drop (j + 1)) = some (r, ops)⌝ ∗
          credits Cg ((60 + 470 * (bs.length - r.length - (j + 1))) * cfg.regularOpCost +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some 0x3A)) 0 l7 0x7B⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs (j + 1) ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  obtain ⟨q, e, j, key, rest, hq, he, hj, hquote, hcolon, hkey, hqe, hnext⟩ :=
    key_indices bs i _ _ hi hmodel
  have hgood := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
    (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N .val (0x7B :: frames) (bs.drop (j + 1))
  have hrest := (hgood r ops hnext).2.1
  have hj_lt := SerdeNextKey.getElem_lt hcolon
  simp only [List.length_drop] at hrest
  have hjQ : j + 1 ≤ bs.length - r.length := by omega
  have hQi : i ≤ j + 1 := by omega
  have hsplit : bs.length - r.length - i = (j + 1 - i) + (bs.length - r.length - (j + 1)) := by omega
  have hkcost := cost_le_value cfg i q e j (by omega) hqe (by omega)
  have hcost : cost cfg i q e j +
      ((60 + 470 * (bs.length - r.length - (j + 1))) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      470 * (bs.length - r.length - i) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R := by
    rw [hsplit]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex HF]
  · iapply object_next cfg lim d inst mi A n g ta hm hd Cg
      ((60 + 470 * (bs.length - r.length - (j + 1))) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
      gt de s ptr l3 l4 l6 l7 l5 maxP i q e j bs rest key Fr hs hde hlen hptr hi hq he hj hquote hcolon hkey
    iframe HC Hg H128 Hrd He Hhex HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexact H
  isplit
  · iintro %k %vs %fr H
    iexists j
    isplitr
    · ipureintro; exact ⟨hQi, hjQ, hnext⟩
    iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

/-- The complete pure continuation at the member tail: an array value, or an object key and value. -/
def nextModel (N : Nat) (f : UInt8) (frames bs : List UInt8) : Option SerdeIgnMachineTrace.Result :=
  if f = 0x5B then SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (f :: frames) bs
  else SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody bs
    (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (f :: frames))

set_option maxRecDepth 100000 in
/-- Either actual member branch establishes the common complete value-loop entry state. -/
theorem next_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (f : UInt8) (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hf : Br f) (hmodel : nextModel N f frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (((if f = 0x5B then 75 else 0) + 470 * (bs.length - r.length - i)) * cfg.regularOpCost +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 f.toUInt32) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ (j : Nat) (l5' : UInt64) (l6' : UInt32),
          ⌜i ≤ j ∧ j ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (f :: frames)
              (bs.drop j) = some (r, ops) ∧
            k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 l5' l6' l7 f.toUInt32⌝ ∗
          credits Cg ((60 + 470 * (bs.length - r.length - j)) * cfg.regularOpCost +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs j ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  rcases hf with rfl | rfl
  · rw [show (0x5B : UInt8).toUInt32 = (0x5B : UInt32) from by decide +kernel]
    simp only [nextModel, ite_true] at hmodel
    have hgood := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
      (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N .val (0x5B :: frames) (bs.drop i)
    have hrest := (hgood r ops hmodel).2.1
    simp only [List.length_drop] at hrest
    have hiQ : i ≤ bs.length - r.length := by omega
    iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
    iapply mwpi_wand
    isplitl [Hc Hg H128 Hrd He Hhex HF]
    · iapply array_next cfg lim d inst mi Cg
        ((60 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
        de s l3 l4 l6 l7 l5 iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr)
      iframe Hg H128 Hrd He Hhex HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      simp only [ite_true, Nat.add_mul]
      omega
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexact H
    isplit
    · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, HF⟩
      iexists i, l5, l6
      iframe Hc Hg H128 Hrd He Hhex HF
      ipureintro; exact ⟨by omega, hiQ, hmodel, hk, hvs, hfr⟩
    isplit
    · iintro %vs %fr H; iexact H
    · iintro H; iexact H
  · rw [show (0x7B : UInt8).toUInt32 = (0x7B : UInt32) from by decide +kernel]
    simp only [nextModel, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at hmodel
    iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
    iapply mwpi_wand
    isplitl [Hc Hg H128 Hrd He Hhex HF]
    · iapply object_traced cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr cap l3 l4 l6 l7 l5
        maxP F N i frames bs r ops Fr hs hde hlen hptr hi hmodel
      iframe HC Hg H128 Hrd He Hhex HF
      simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false, Nat.zero_add]
      iexact Hc
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexact H
    isplit
    · iintro %k %vs %fr ⟨%j, %⟨hij, hjQ, hn⟩, Hc, %⟨hk, hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, HF⟩
      iexists j + 1, optByte (some 0x3A), 0
      iframe Hc Hg H128 Hrd He Hhex HF
      ipureintro; exact ⟨hij, hjQ, hn, hk, hvs, hfr⟩
    isplit
    · iintro %vs %fr H; iexact H
    · iintro H; iexact H

end Proof
end WNear.Binary.SerdeIgnMember
