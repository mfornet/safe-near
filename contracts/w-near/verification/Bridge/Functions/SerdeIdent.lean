import Bridge.Functions.AccountIdValid
import Bridge.Functions.SerdeRead

/-!
# `parse_ident` (323): the rest of `null`, `true`, `false` (M6)

`ignore_value` (81) eats the first byte of a literal, then calls `parse_ident(de, lit, len)` (323)
with the rest of it, from the data segment at 1048576, which begins `alserueull` (`identBytes`):
`alse` at 1048576, `rue` at 1048580, `ull` at 1048583.

```wat
;; 323 parse_ident(de, p, len) -> i32       (a 32-byte frame for the slice iterator)
(cur, end) := into_iter(p, len)              ;; 673
loop
  cur = end → return 0
  v := next_char(de)                         ;; 324
  None → EofWhileParsingValue (325)
  b := [cur]; cur += 1
  b = byte(v) → continue
ExpectedSomeIdent (325)
```

* `f323_spec`: where the input at `i` holds the `len` bytes of `identBytes` from `off`, `0`, the
  reader at `i + len`, at `cost323 len = 72 + 75·len`.
-/

namespace WNear.Binary.SerdeIdent

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte)

/-- The data segment's first ten bytes, `alserueull`. -/
def identBytes : List UInt8 := [0x61, 0x6C, 0x73, 0x65, 0x72, 0x75, 0x65, 0x75, 0x6C, 0x6C]

/-- 323's cost on a literal of `len` bytes, activation excluded. -/
def cost323 (len : Nat) : Nat := 72 + 75 * len

/-- The comparison of a literal byte with the byte read. -/
theorem lit_eq (b : UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 ((optByte (some b) >>> (16 % 75)).toUInt32 &&& 255)) ≠ 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem some_bit (b : UInt8) : Numeric.bool (optByte (some b) &&& 256 == 0) = 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

section L323

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 323's frame: `(de, cur, b, sp', end, v)`. -/
def fr323 (inst : Nat) (mi : ModuleInst) (de cur b sp e : UInt32) (v : UInt64) : Frame :=
  ⟨#[.i32 de, .i32 cur, .i32 b, .i32 sp, .i32 e, .i64 v], inst, mi⟩

/-- 323's loop: `k` bytes compared. -/
def inv323 (n inst : Nat) (mi : ModuleInst) (Cg c₀ W E R : Nat) (de p sp ptr : UInt32) (bs : List UInt8) (i len : Nat)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (b : UInt32) (v : UInt64), ⌜X = [] ∧
      g = fr323 inst mi de (p + UInt32.ofNat k) b sp (p + UInt32.ofNat len) v ∧ k ≤ len⌝ ∗
    credits Cg (W * (len - k) * c₀ + E * c₀ + R) ∗ rd n de ptr bs (i + k) ∗ P)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`parse_ident(de, p, len)`** (323) where the input at `i` holds the literal's `len` bytes
(`identBytes` from `off`, at `p`): `0`, the reader past them. -/
theorem f323_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a324 a673 : Nat)
    (ha324 : mi.funcAddrs[324]? = some a324) (ha673 : mi.funcAddrs[673]? = some a673)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (sp de ptr p len32 : UInt32)
    (bs : List UInt8) (i off len : Nat) (hp : p.toNat = 1048576 + off) (hl32 : len32.toNat = len)
    (hoff : off + len ≤ 10) (hil : i + len ≤ bs.length)
    (hlit : ∀ k, k < len → bs[i + k]? = identBytes[off + k]?)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hsp : 32 ≤ sp.toNat) :
    a324 ↪[wf] FuncInst.wasm types[11]! inst f324 ∗ a673 ↪[wf] FuncInst.wasm types[31]! inst f673 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f323 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 p, .i32 len32]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ rd n de ptr bs i ∗ n ↦[wms][ 1048576 ] identBytes))
        (fun _ => cost323 len * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ rd n de ptr bs (i + len) ∗ n ↦[wms][ 1048576 ] identBytes)) := by
  iintro ⟨#F324, #F673, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hrd, Hlit⟩
  subst hargs
  have t31 : types[31]!.params.length = 3 := by rfl
  have t11 : types[11]!.params.length = 1 := by rfl
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 32 + 8).toNat = sp.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, h32]; simp; omega
  simp only [f323, cost323]
  icases stk_split n (sp.toNat - 32) 8 24 $$ Hs with ⟨Hs8, Hs⟩
  icases stk_split n (sp.toNat - 32 + 8) 8 16 $$ Hs with ⟨Hs, Hs16⟩
  iunfold stk at Hs
  icases Hs with ⟨%ob, %hob, Hs⟩
  ihave Hs := AllocNewCell.memBytes_addr (show sp.toNat - 32 + 8 = (sp - 32 + 8).toNat by rw [h8]) $$ Hs
  rw [show (72 + 75 * len) * cfg.regularOpCost + R = 56 * cfg.regularOpCost + ((75 * len + 16) * cfg.regularOpCost + R) by
    rw [Nat.add_mul, Nat.add_mul]; omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mcall (AccountIdValid.f673_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 32 + 8) p len32 ob hob
    (by rw [h8]; omega)) using [Hs]
  · iframe Hs
  icases HQ with ⟨%hrs, I0, I4⟩
  subst hrs
  mstep
  mstep [I4] with (rw [UInt32.toNat_add, h32]; simp; omega)
  mstep; mstep
  mstep [I0] with (rw [UInt32.toNat_add, h32]; simp; omega)
  mstep; mstep; mstep
  rw [show (75 * len + 16) * cfg.regularOpCost = cfg.regularOpCost + (75 * (len - 0) * cfg.regularOpCost + 15 * cfg.regularOpCost) by
    rw [Nat.sub_zero, Nat.add_mul]; omega]
  mcredits (cfg.regularOpCost + (75 * (len - 0) * cfg.regularOpCost + 15 * cfg.regularOpCost + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 75 * (len - 0) * cfg.regularOpCost + 15 * cfg.regularOpCost + R)
    (I := inv323 n inst mi Cg cfg.regularOpCost 75 15 R de p (sp - 32) ptr bs i len
      iprop(g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗ stk n (sp.toNat - 32) 8 ∗ n ↦[i32][ (sp - 32 + 8).toNat ] p ∗
        n ↦[i32][ (sp - 32 + 8).toNat + 4 ] (p + len32) ∗ stk n (sp.toNat - 32 + 8 + 8) 16 ∗
        n ↦[wms][ 1048576 ] identBytes)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv323 at HI
    icases HI with ⟨%k, %b, %v, %⟨hX, hfr, hk⟩, Hc, Hrd, Hg, Hs8, I0, I4, Hs16, Hlit⟩
    subst hX
    rw [hfr]
    simp only [fr323]
    have hcne : ∀ k1 k2 : Nat, k1 ≤ len → k2 ≤ len → (p + UInt32.ofNat k1 = p + UInt32.ofNat k2 ↔ k1 = k2) := by
      intro k1 k2 h1 h2
      constructor
      · intro h; have := congrArg UInt32.toNat h; simp [UInt32.toNat_add] at this; omega
      · intro h; rw [h]
    have hl32' : p + len32 = p + UInt32.ofNat len := by rw [← hl32]; simp
    by_cases hkl : k = len
    · subst hkl
      mstep; mstep; mstep; mstep
      mstep_not_taken with (simp [Numeric.bool, Numeric.irelop32, hl32'])
      mstep; mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep; mstep [Hg]
      rw [show sp - 32 + 32 = sp by simp]
      repeat mstep
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe Hg Hrd Hlit
      isplitr
      · ipureintro; simp [htype]
      ihave I0 := stk_word $$ I0
      ihave I4 := stk_word $$ I4
      rw [h8]
      ihave S8 := stk_join n (sp.toNat - 32 + 8) 4 4 $$ [I0 I4]
      · iframe I0 I4
      ihave S16 := stk_join n (sp.toNat - 32 + 8) (4 + 4) 16 $$ [S8 Hs16]
      · iframe S8 Hs16
      ihave S := stk_join n (sp.toNat - 32) 8 (4 + 4 + 16) $$ [Hs8 S16]
      · iframe Hs8 S16
      iexact S
    · have hkl' : k < len := by omega
      rw [show 75 * (len - k) * cfg.regularOpCost + 15 * cfg.regularOpCost + R =
        75 * cfg.regularOpCost + (75 * (len - (k + 1)) * cfg.regularOpCost + 15 * cfg.regularOpCost + R) by
          rw [show 75 * (len - k) = 75 + 75 * (len - (k + 1)) by omega, Nat.add_mul]; omega]
      generalize hZ : 75 * (len - (k + 1)) * cfg.regularOpCost = Z
      have hne : p + UInt32.ofNat len ≠ p + UInt32.ofNat k := fun h => hkl ((hcne _ _ le_rfl hk).mp h).symm
      have hc1 : Numeric.bool (Numeric.irelop32 IRelOp.ne (p + UInt32.ofNat len) (p + UInt32.ofNat k)) ≠ 0 := by
        simp [Numeric.bool, Numeric.irelop32, hne]
      mstep; mstep; mstep; mstep
      mstep_taken with exact hc1
      mstep; mstep
      mcall (SerdeRead.f324_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn Cg de ptr bs (i + k)
        (by omega) hlen hptr hde) using [Hrd]
      · iframe Hrd
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      have hik : i + k < bs.length := by omega
      obtain ⟨x, hx⟩ : ∃ x, bs[i + k]? = some x := ⟨_, List.getElem?_eq_getElem hik⟩
      have hxl := hlit k hkl'
      rw [hx] at hxl ⊢
      rw [show min (i + k + 1) bs.length = i + (k + 1) by omega]
      have hok : Numeric.bool (optByte (some x) &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
      mstep; mstep; mstep; mstep
      mstep_taken with exact hok
      mstep; mstep; mstep; mstep
      mstep_not_taken with exact some_bit x
      have hok' : off + k < identBytes.length := by simp [identBytes]; omega
      ihave Hlit := MemCpy.memBytes_pick n 1048576 (off + k) identBytes hok' $$ Hlit
      icases Hlit with ⟨B1, Bk, B2⟩
      have hxb : identBytes[off + k] = x := by
        rw [List.getElem?_eq_getElem hok'] at hxl; exact (Option.some.inj hxl).symm
      rw [hxb]
      mstep
      have hA : (p + UInt32.ofNat k).toNat + 0 = 1048576 + (off + k) := by
        rw [UInt32.toNat_add, hp, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega),
          Nat.mod_eq_of_lt (by omega)]; omega
      mstep [Bk] with (first | exact hA | exact hn | exact List.cons_ne_nil _ _ | rfl)
      simp only [SerdeKey.load8]
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with exact lit_eq x
      simp only [Post.mloop, List.reverse_nil]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iunfold inv323
      iexists k + 1
      iexists x.toUInt32
      iexists optByte (some x)
      ihave Hlit := MemCpy.memBytes_unpick n 1048576 (off + k) (identBytes.take (off + k)) x
        (identBytes.drop (off + k + 1)) (by simp; omega) $$ [B1 Bk B2]
      · iframe B1 Bk B2
      have es : List.take (off + k) identBytes ++ x :: List.drop (off + k + 1) identBytes = identBytes := by
        rw [← hxb]; simp
      rw [es]
      iframe Hrd Hg Hs8 I0 I4 Hs16 Hlit
      isplitr
      · ipureintro
        refine ⟨rfl, ?_, by omega⟩
        simp only [fr323, UInt32.add_assoc, SerdeRead.ofNat_succ k (by omega)]
      rw [← hZ]
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
  · iframe Hc
    inext
    iintro Hc
    iunfold inv323
    iexists 0
    iexists len32
    iexists 0
    iframe Hc Hg Hs8 I0 I4 Hlit
    isplitr
    · ipureintro
      refine ⟨rfl, ?_, by omega⟩
      simp [fr323, ← hl32, UInt32.ofNat_toNat]
    rw [Nat.add_zero]
    iframe Hrd
    iexact Hs16

end L323

end WNear.Binary.SerdeIdent
