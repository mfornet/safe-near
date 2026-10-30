import Bridge.Functions.AllocLeaves
import Bridge.Functions.AllocGrow
import Bridge.Functions.U128From

/-!
# `LargeAllocPolicy::new_cell_for_free_list` (577), in the metered logic

`new_cell_for_free_list(out, policy, words, align)` asks `memory.grow` for
`cellPages words align = ceil((max(4 * words, 8 * (align + 64)) + 8) / 65536)`
pages and, on success, makes the new pages one free cell: header word 0 =
`end | NEXT_CELL_IS_INVALID`, word 1 (`prev`) = 0, `next_free` = 0. It writes
`Result<*const FreeCell, AllocErr>` to `out`: tag 0 and the cell, or tag 1
(and `-1`, the failed grow's result, in the payload word) when `memory.grow`
fails.

`f577_spec` covers both branches, for `words < 2^29` and `align < 2^20` (so
none of its overflow panics is reachable) and a page-aligned memory length
`len`. Cost: `166 regular_op_cost`s plus the `memory.grow` charge
`linear_op_base_cost + linear_op_unit_cost * cellPages` on success (the
failure path costs 107, the 59 left over are dropped), with the calls to 572,
569 (→ 568), 573 and 574 and their activations included; 577's own
activation (12) is paid by the caller.

Two pitfalls met on the way, worth knowing for 580/582: a points-to on
`List.replicate (k * 65536) 0` with symbolic `k` makes the *kernel* recurse
65536 deep (`Nat.mul` unfolded to find a `succ`), so `mwpi_memory_grow_either`
hands the new bytes as an abstract `bs` with `bs = replicate ..` as a pure
fact, which is turned into `∀ x ∈ bs, x = 0` and cleared before stepping;
and the whole proof needs `maxHeartbeats` above the default.
-/

namespace WNear.Binary.AllocNewCell

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.AllocLeaves WNear.Binary.AllocGrow
open WNear.Binary.U128From (memBytes_split memBytes_join)

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- `select` on a stack read from the top, for any credits `K`. -/
theorem mwpi_select_ite (t : Option (List ValType)) {a b : Value} {c : UInt32} {rest : List Value} :
    credits Cg K ∗ ⌜vs.reverse = .i32 c :: b :: a :: rest ∧ cfg.regularOpCost ≤ K⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal (rest.reverse ++ [if c = 0 then b else a]) f)
      ⊢ mwpi cfg lim d f vs [.select t] Φ := by
  iintro ⟨Hc, %⟨hs, hK⟩, H⟩
  have hv : vs = rest.reverse ++ [a, b, .i32 c] := by
    rw [← List.reverse_reverse vs, hs]; simp
  subst hv
  rw [show K = cfg.regularOpCost + (K - cfg.regularOpCost) by omega]
  by_cases h : c = 0
  · subst h
    iapply mwpi_select_false t a b
    iframe Hc
    rw [Nat.add_sub_cancel_left]
    simp only [ite_true]
    iexact H
  · iapply mwpi_select_true t a b c h
    iframe Hc
    rw [Nat.add_sub_cancel_left]
    simp only [h, ite_false]
    iexact H

end Flex

theorem select_gt (x y : UInt32) :
    (if Numeric.bool (Numeric.irelop32 .gt_u x y) = 0 then Value.i32 y else Value.i32 x) =
      .i32 (if y < x then x else y) := by
  by_cases h : y < x <;> simp [Numeric.bool, Numeric.irelop32, h]

/-- The bytes of the new cell: the larger of the request and `(align + 64) * 8`. -/
def cellBytes (sw al : UInt32) : UInt32 :=
  if (al + 64) <<< (3 % 32) < sw <<< 2 then sw <<< 2 else (al + 64) <<< (3 % 32)

theorem shl2_toNat (w : UInt32) (h : w.toNat < 2 ^ 30) : (w <<< 2).toNat = w.toNat * 4 := by
  rw [UInt32.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

theorem shl3_toNat (w : UInt32) (h : w.toNat < 2 ^ 29) : (w <<< (3 % 32)).toNat = w.toNat * 8 := by
  rw [UInt32.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

theorem cellBytes_toNat (sw al : UInt32) (hsw : sw.toNat < 2 ^ 29) (hal : al.toNat < 2 ^ 20) :
    (cellBytes sw al).toNat = max (sw.toNat * 4) ((al.toNat + 64) * 8) := by
  have h64 : (al + 64).toNat = al.toNat + 64 := by rw [UInt32.toNat_add]; simp; omega
  have e1 := shl2_toNat sw (by omega)
  have e2 := shl3_toNat (al + 64) (by omega)
  unfold cellBytes
  split
  · rename_i h; rw [UInt32.lt_iff_toNat_lt, e1, e2, h64] at h; rw [e1]; omega
  · rename_i h; rw [UInt32.lt_iff_toNat_lt, e1, e2, h64] at h; rw [e2, h64]; omega

/-- The pages `memory.grow` asks for: `ceil((cellBytes + 8) / 65536)`. -/
def cellPages (sw al : UInt32) : UInt32 :=
  (cellBytes sw al + 8 + 65536 + 4294967295) / 65536

theorem cellPages_toNat (sw al : UInt32) (hsw : sw.toNat < 2 ^ 29) (hal : al.toNat < 2 ^ 20) :
    (cellPages sw al).toNat = ((cellBytes sw al).toNat + 65543) / 65536 := by
  have := cellBytes_toNat sw al hsw hal
  unfold cellPages
  rw [UInt32.toNat_div, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add]
  simp only [UInt32.reduceToNat]
  omega

theorem cellPages_bounds (sw al : UInt32) (hsw : sw.toNat < 2 ^ 29) (hal : al.toNat < 2 ^ 20) :
    1 ≤ (cellPages sw al).toNat ∧ (cellPages sw al).toNat < 2 ^ 16 := by
  rw [cellPages_toNat sw al hsw hal, cellBytes_toNat sw al hsw hal]
  omega

theorem page_shl (len : Nat) (h0 : len % 65536 = 0) (h : len / 65536 < 65536) :
    (UInt32.ofNat (len / 65536) <<< (16 % 32)).toNat = len := by
  rw [UInt32.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

theorem ne_neg1 (x : Nat) (h : x < 65536) :
    Numeric.bool (Numeric.irelop32 .ne (UInt32.ofNat x) 4294967295) ≠ 0 := by
  simp only [Numeric.bool, Numeric.irelop32, bne_iff_ne, ne_eq]
  intro e
  split at e
  · cases e
  · rename_i hh; apply hh; intro e2
    have := congrArg UInt32.toNat e2
    simp at this; omega
theorem mask_ne (x : Nat) (h : x < 65536) :
    Numeric.bool (Numeric.irelop32 .ne (UInt32.ofNat x &&& 65535) (UInt32.ofNat x)) = 0 := by
  have : UInt32.ofNat x &&& 65535 = UInt32.ofNat x := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and]; simp
    rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  simp [this, Numeric.bool, Numeric.irelop32]


theorem page_shl' (len : Nat) (h0 : len % 65536 = 0) (h : len / 65536 < 65536) :
    (UInt32.ofNat (len / pageSize) <<< (16 % 32)).toNat = len := page_shl len h0 h

theorem shl16_toNat (w : UInt32) (h : w.toNat < 2 ^ 16) : (w <<< 16).toNat = w.toNat * 65536 := by
  rw [UInt32.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem memBytes_addr {n a b : Nat} {bs : List UInt8} (h : a = b) :
    n ↦[wms][ a ] bs ⊢ (n ↦[wms][ b ] bs : IProp GF) := by
  subst h; exact .rfl

theorem memBytes_eq {n a : Nat} {bs bs' : List UInt8} (h : bs = bs') :
    n ↦[wms][ a ] bs ⊢ (n ↦[wms][ a ] bs' : IProp GF) := by
  subst h; exact .rfl

theorem take_zeros (bs : List UInt8) (hz : ∀ x ∈ bs, x = 0) (k : Nat) (hk : k ≤ bs.length) :
    bs.take k = List.replicate k 0 := by
  apply List.eq_replicate_iff.mpr
  exact ⟨by simp; omega, fun x hx => hz x (List.mem_of_mem_take hx)⟩

/-- What 577 leaves: on success (tag 0) the fresh chunk `[len, len + pages * 65536)`
as one free cell (header `end | 2`, `prev = 0`, `next_free = 0`, the rest zero) and
the memory grown; on failure (`memory.grow` returned `-1`) the tag 1 and nothing
else changed. -/
def post (n : Nat) (out sw al : UInt32) (len : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗
    ((n ↦[wms][ out.toNat ] bytes32 0 ∗ n ↦[wms][ out.toNat + 4 ] bytes32 (UInt32.ofNat len) ∗
      n ↦[wmlength] (len + (cellPages sw al).toNat * pageSize) ∗
      n ↦[wms][ len ] bytes32 ((UInt32.ofNat len + cellPages sw al <<< 16) ||| 2) ∗
      n ↦[wms][ len + 4 ] List.drop 4 (storeBytes (.i64 0) 8) ∗ n ↦[wms][ len + 8 ] bytes32 0 ∗
      ∃ rest : List UInt8, ⌜rest.length = (cellPages sw al).toNat * 65536 - 12 ∧ ∀ x ∈ rest, x = 0⌝ ∗
        n ↦[wms][ len + 12 ] rest) ∨
     (n ↦[wms][ out.toNat ] bytes32 1 ∗ n ↦[wms][ out.toNat + 4 ] bytes32 4294967295 ∗
      n ↦[wmlength] len)))

set_option maxHeartbeats 2000000 in
theorem f577_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n)
    (a572 a569 a568 a573 a574 : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h569 : mi.funcAddrs[569]? = some a569)
    (h568 : mi.funcAddrs[568]? = some a568) (h573 : mi.funcAddrs[573]? = some a573)
    (h574 : mi.funcAddrs[574]? = some a574)
    (ty572 ty569 ty568 ty573 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp569 : ty569.params.length = 1) (hr569 : ty569.results.length = 1)
    (hp568 : ty568.params.length = 2) (hr568 : ty568.results.length = 1)
    (hp573 : ty573.params.length = 1) (hr573 : ty573.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (out pol sw al : UInt32) (len : Nat) (o1 o2 : List UInt8)
    (hsw : sw.toNat < 2 ^ 29) (hal : al.toNat < 2 ^ 20)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hlen0 : len % 65536 = 0) (ho1 : o1.length = 4) (ho2 : o2.length = 4) :
    a572 ↪[wf] FuncInst.wasm ty572 inst f572 ∗ a569 ↪[wf] FuncInst.wasm ty569 inst f569 ∗
      a568 ↪[wf] FuncInst.wasm ty568 inst f568 ∗ a573 ↪[wf] FuncInst.wasm ty573 inst f573 ∗
      a574 ↪[wf] FuncInst.wasm ty574 inst f574 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f577 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 pol, .i32 sw, .i32 al]⌝ ∗
          n ↦[wms][ out.toNat ] o1 ∗ n ↦[wms][ out.toNat + 4 ] o2 ∗ n ↦[wmlength] len))
        (fun _ => 166 * cfg.regularOpCost + cfg.linearOpBaseCost +
          cfg.linearOpUnitCost * (cellPages sw al).toNat)
        (post n out sw al len) := by
  iintro ⟨#H572, #H569, #H568, #H573, #H574, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Ho1, Ho2, Hl⟩ Hc
  subst hargs
  simp only [f577]
  mstep
  mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg sw (by omega))
    with (simp [activationGas, entryLocals, f572, ValType.default, hp572]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep
  mstep_not_taken with ucond
  mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (simp [and_mask_eq (al + 64) 536870911 29 (by decide) (by simp; omega), Numeric.bool, Numeric.irelop32])
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply mwpi_select_ite
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega⟩
  inext
  iintro Hc
  rw [select_gt]
  mctrl_norm
  rw [show (if (al + 64) <<< (3 % 32) < sw <<< 2 then sw <<< 2 else (al + 64) <<< (3 % 32)) = cellBytes sw al from rfl]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (have := cellBytes_toNat sw al hsw hal; ucond)
  mstep; mstep; mstep
  mcall (f569_spec cfg lim (d + 1) ty569 hr569 inst mi a568 h568 ty568 hp568 hr568 (by omega) Cg
      (cellBytes sw al + 8) (by have := cellBytes_toNat sw al hsw hal; rw [UInt32.toNat_add]; simp; omega))
    with (simp [activationGas, entryLocals, f569, ValType.default, hp569]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep
  rw [show (cellBytes sw al + 8 + 65536 + 4294967295) / 65536 = cellPages sw al from rfl]
  rw [show 166 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages sw al).toNat + R -
      93 * cfg.regularOpCost = cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages sw al).toNat +
      (73 * cfg.regularOpCost + R) by omega]
  iapply mwpi_cons
  rw [show [Value.i32 (cellPages sw al)] = [] ++ [Value.i32 (cellPages sw al)] from rfl]
  iapply (mwpi_memory_grow_either (vs := []) n len (cellPages sw al) hn)
  isplitl [Hc]
  · iexact Hc
  isplitl [Hl]
  · iexact Hl
  inext
  isplit
  · iintro %hok %bs %hbs Hl Hnew Hc
    simp only [Post.mseq_normal, List.nil_append]
    have hkb := cellPages_bounds sw al hsw hal
    have hpg : len / 65536 < 65536 := by simp [pageSize, maxPages] at hok; omega
    mstep; mstep; mstep
    mstep_taken with (exact ne_neg1 _ hpg)
    mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with (exact mask_ne _ hpg)
    mstep
    mcall (f573_spec cfg lim (d + 1) ty573 hr573 inst mi Cg (cellPages sw al) hkb.2)
      with (simp [activationGas, entryLocals, f573, ValType.default, hp573]; omega)
    · ipureintro; trivial
    icases HQ with %hrs
    subst hrs
    mstep
    mcall (f574_spec cfg lim (d + 1) ty574 hr574 inst mi Cg (cellPages sw al <<< 16)
        (by rw [shl16_toNat _ hkb.2]; omega))
      with (simp [activationGas, entryLocals, f574, ValType.default, hp574]; omega)
    · ipureintro; trivial
    icases HQ with %hrs
    subst hrs
    have hbl : bs.length = (cellPages sw al).toNat * 65536 := by rw [hbs]; simp [pageSize]
    have hz : ∀ x ∈ bs, x = 0 := by rw [hbs]; intro x hx; exact List.eq_of_mem_replicate hx
    clear hbs
    icases memBytes_split n len 8 bs (by omega) $$ Hnew with ⟨H8, Hr⟩
    icases memBytes_split n (len + 8) 4 (bs.drop 8) (by simp; omega) $$ Hr with ⟨H4, Hr⟩
    have hX : UInt32.ofNat (len / pageSize) <<< (16 % 32) = UInt32.ofNat len := by
      apply UInt32.toNat_inj.mp; rw [page_shl' len hlen0 hpg]; simp; omega
    mstep; mstep; mstep; mstep
    rw [hX]; clear hX
    mstep
    ihave H8 := memBytes_eq (take_zeros bs hz 8 (by omega)) $$ H8
    ihave H4 := memBytes_eq (take_zeros (bs.drop 8) (fun x hx => hz x (List.mem_of_mem_drop hx)) 4
      (by simp; omega)) $$ H4
    simp only [List.replicate]
    mstep [H8]
    mstep; mstep; mstep; mstep
    mstep [H4]
    icases memBytes_split n len 4 _ (by simp [storeBytes]) $$ H8 with ⟨H8a, H8b⟩
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep [H8a]
    have hrest : (List.drop 4 (List.drop 8 bs)).length = (cellPages sw al).toNat * 65536 - 12 ∧
        ∀ x ∈ List.drop 4 (List.drop 8 bs), x = 0 :=
      ⟨by simp; omega, fun x hx => hz x (List.mem_of_mem_drop (List.mem_of_mem_drop hx))⟩
    ihave Hr : (∃ rest : List UInt8, ⌜rest.length = (cellPages sw al).toNat * 65536 - 12 ∧
        ∀ x ∈ rest, x = 0⌝ ∗ n ↦[wms][ len + 12 ] rest) $$ [Hr]
    · iexists _; iframe Hr; ipureintro; exact hrest
    clear hrest hz hbl
    mstep; mstep
    clear hok hpg hkb
    mstep [Ho2]; mstep; mstep; mstep [Ho1]; mstep
    iframe Hc
    iunfold post
    isplitr; · ipureintro; rfl
    ileft
    iframe Ho1 Ho2 Hl H8a H8b H4 Hr
  · iintro Hl Hc
    clear hlen0 hsw hal
    simp only [Post.mseq_normal, List.nil_append]
    mstep; mstep; mstep
    mstep_not_taken with (simp [Numeric.bool, Numeric.irelop32])
    mstep; mstep; mstep
    mstep; mstep; mstep [Ho2]; mstep; mstep; mstep [Ho1]; mstep
    mcredits R
    iframe Hc
    iunfold post
    isplitr; · ipureintro; rfl
    iright
    iframe Ho1 Ho2 Hl

end Spec

end WNear.Binary.AllocNewCell
