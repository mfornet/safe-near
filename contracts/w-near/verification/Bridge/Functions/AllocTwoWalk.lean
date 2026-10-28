import Bridge.Functions.AllocFirstFit
import Bridge.Functions.AllocDealloc

/-!
# `alloc_first_fit` (580) on a free list of two cells (milestone M4)

`AllocFirstFit.f580_one` walks a list of at most one cell. A `dealloc` pushes a cell (or links
it behind its free next neighbour with `CAN_MERGE`), so after one free the list `heapInv … 2`
allows has two cells `[a, b]`. This file proves the walk over such a list:

* `body7`: one iteration of the merge loop (`@7`) on a cell `c` without `CAN_MERGE`, whose
  `next_free` is any `v` (`f580_one` has `v = 0`): too small (`¬ fits`), not splittable, or
  split (`split_spec_v`, the generalisation of `AllocFirstFit.split_spec` to `v`);
* `merge7`: the iteration that merges a cell `a` with `CAN_MERGE` into its previous
  neighbour `b` (575, `Neighbors::remove`), `b` becoming the walk's cell;
* the outer loop (`@3`) over `[a, b]`.
-/

namespace WNear.Binary.AllocTwoWalk

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocLeaves WNear.Binary.AllocFirstFit
set_option maxRecDepth 20000

/-- The body of 580's merge loop (`@7`). -/
abbrev l7Body : List Instr :=
  [Instr.block BlockType.empty [Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 8 }, Instr.local_tee 9, Instr.i32_const 1, Instr.i32_binop IBinOp.and, Instr.br_if 0, Instr.local_get 1, Instr.i32_const 8, Instr.i32_binop IBinOp.add, Instr.local_set 9, Instr.local_get 0, Instr.call 572, Instr.local_set 10, Instr.local_get 1, Instr.call 576, Instr.local_get 10, Instr.i32_relop IRelOp.lt_u, Instr.br_if 3, Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 4294967292, Instr.i32_binop IBinOp.and, Instr.local_tee 11, Instr.local_get 10, Instr.i32_binop IBinOp.sub, Instr.local_tee 12, Instr.local_get 11, Instr.i32_relop IRelOp.gt_u, Instr.br_if 0, Instr.local_get 8, Instr.br_if 1, Instr.local_get 3, Instr.local_get 0, Instr.local_get 4, Instr.load NumType.i32 none { align := 2, offset := 16 }, Instr.call_indirect 13 0, Instr.call 572, Instr.local_set 13, Instr.local_get 9, Instr.i32_const 8, Instr.i32_binop IBinOp.add, Instr.local_tee 10, Instr.local_get 9, Instr.i32_relop IRelOp.lt_u, Instr.br_if 2, Instr.local_get 10, Instr.local_get 13, Instr.i32_binop IBinOp.add, Instr.local_tee 13, Instr.local_get 10, Instr.i32_relop IRelOp.lt_u, Instr.br_if 3, Instr.local_get 13, Instr.local_get 12, Instr.local_get 6, Instr.i32_binop IBinOp.and, Instr.local_tee 10, Instr.i32_relop IRelOp.gt_u, Instr.br_if 8, Instr.local_get 10, Instr.i32_const 4294967288, Instr.i32_binop IBinOp.add, Instr.local_tee 9, Instr.local_get 10, Instr.i32_relop IRelOp.gt_u, Instr.br_if 4, Instr.local_get 11, Instr.local_get 9, Instr.i32_binop IBinOp.sub, Instr.local_tee 2, Instr.local_get 11, Instr.i32_relop IRelOp.gt_u, Instr.br_if 5, Instr.local_get 2, Instr.call 574, Instr.local_get 9, Instr.i32_const 0, Instr.store NumType.i32 none { align := 2, offset := 8 }, Instr.local_get 9, Instr.i64_const 0, Instr.store NumType.i64 none { align := 2, offset := 0 }, Instr.local_get 9, Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 4294967292, Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.block BlockType.empty [Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.local_tee 2, Instr.i32_const 4294967292, Instr.i32_binop IBinOp.and, Instr.local_tee 10, Instr.i32_eqz, Instr.br_if 0, Instr.i32_const 0, Instr.local_get 10, Instr.local_get 2, Instr.i32_const 2, Instr.i32_binop IBinOp.and, Instr.select none, Instr.local_tee 2, Instr.i32_eqz, Instr.br_if 0, Instr.local_get 2, Instr.local_get 2, Instr.load NumType.i32 none { align := 2, offset := 4 }, Instr.i32_const 3, Instr.i32_binop IBinOp.and, Instr.local_get 9, Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 4 }], Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 4 }, Instr.i32_const 3, Instr.i32_binop IBinOp.and, Instr.local_get 1, Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 4 }, Instr.local_get 1, Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 8 }, Instr.i32_const 4294967294, Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 8 }, Instr.local_get 1, Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 3, Instr.i32_binop IBinOp.and, Instr.local_get 9, Instr.i32_binop IBinOp.or, Instr.local_tee 2, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.local_get 2, Instr.i32_const 2, Instr.i32_binop IBinOp.and, Instr.i32_eqz, Instr.br_if 12, Instr.local_get 1, Instr.local_get 2, Instr.i32_const 4294967293, Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 2, Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.br 12], Instr.i32_const 1057152, Instr.i32_const 33, Instr.i32_const 1057384, Instr.call 853, Instr.unreachable], Instr.i32_const 1057152, Instr.i32_const 33, Instr.i32_const 1057400, Instr.call 853, Instr.unreachable], Instr.i32_const 1057104, Instr.i32_const 28, Instr.i32_const 1057416, Instr.call 853, Instr.unreachable], Instr.i32_const 1057104, Instr.i32_const 28, Instr.i32_const 1057416, Instr.call 853, Instr.unreachable], Instr.i32_const 1057152, Instr.i32_const 33, Instr.i32_const 1057432, Instr.call 853, Instr.unreachable], Instr.i32_const 1057152, Instr.i32_const 33, Instr.i32_const 1057448, Instr.call 853, Instr.unreachable], Instr.local_get 1, Instr.local_get 9, Instr.i32_const 4294967294, Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 8 }, Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 4 }, Instr.i32_const 4294967292, Instr.i32_binop IBinOp.and, Instr.local_tee 9, Instr.br_if 0, Instr.i32_const 0, Instr.local_set 9, Instr.br 1], Instr.i32_const 0, Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 (some { bits := 8, signed := false }) { align := 0, offset := 0 }, Instr.i32_const 1, Instr.i32_binop IBinOp.and, Instr.select none, Instr.local_set 9], Instr.local_get 1, Instr.call 575, Instr.block BlockType.empty [Instr.local_get 1, Instr.load NumType.i32 (some { bits := 8, signed := false }) { align := 0, offset := 0 }, Instr.i32_const 2, Instr.i32_binop IBinOp.and, Instr.i32_eqz, Instr.br_if 0, Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 2, Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 0 }], Instr.local_get 2, Instr.local_get 9, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.local_get 9, Instr.call 576, Instr.drop, Instr.local_get 9, Instr.local_set 1, Instr.br 0]

/-- The body of 580's outer loop (`@3`). -/
abbrev l3Body : List Instr :=
  [Instr.local_get 1, Instr.i32_eqz, Instr.br_if 2, Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.block BlockType.empty [Instr.loop BlockType.empty l7Body], Instr.local_get 7, Instr.local_get 9, Instr.i32_binop IBinOp.and, Instr.i32_eqz, Instr.br_if 1], Instr.local_get 2, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.local_tee 1, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.br 1]]

instance (w c nx : UInt32) : Decidable (fits w c nx) := by unfold fits; infer_instance

theorem v_and2 (v : UInt32) (h : v &&& 3 = 0) : v &&& 4294967294 = v := by
  apply u32_ext; intro i hi
  have h4 := toNat_mod4 v h
  simp only [UInt32.toNat_and, UInt32.reduceToNat, Nat.testBit_and]
  rcases (show i = 0 ∨ 1 ≤ i by omega) with rfl | hi1
  · rw [tb_low _ 0 h4 (by omega)]; try simp
  · have : (4294967294 : Nat).testBit i = true := by
      have := tb_mid 4294967292 i (by omega)
      interval_cases i <;> decide
    rw [this]; simp

theorem v_and1 (v : UInt32) (h : v &&& 3 = 0) : v &&& 1 = 0 := by
  apply u32_ext; intro i hi
  have h4 := toNat_mod4 v h
  simp only [UInt32.toNat_and, UInt32.reduceToNat, Nat.testBit_and]
  rcases (show i = 0 ∨ 1 ≤ i by omega) with rfl | hi1
  · rw [tb_low _ 0 h4 (by omega)]; try simp
  · have : (1 : Nat).testBit i = false := by
      rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp; omega
    rw [this]; simp

theorem v_and3m (v : UInt32) (h : v &&& 3 = 0) : v &&& 4294967292 = v := by
  apply u32_ext; intro i hi
  have h4 := toNat_mod4 v h
  simp only [UInt32.toNat_and, UInt32.reduceToNat, Nat.testBit_and]
  rcases (show i < 2 ∨ 2 ≤ i by omega) with h1 | h1
  · rw [tb_low _ i h4 h1]; try simp
  · rw [tb_mid 4294967292 i (by omega) h1 hi]; simp

section SplitSpec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `AllocFirstFit.splitRes` with the cell's `next_free` `v`. -/
def splitResV (n : Nat) (c nx npv A v : UInt32) (lst : Bool) (bs : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ c.toNat ] (UInt32.ofNat (A.toNat - 8)) ∗ n ↦[i32][ c.toNat + 8 ] v ∗
    (∃ b0 : List UInt8, ⌜b0 = bs.take ((UInt32.ofNat (A.toNat - 8)).toNat - c.toNat - 12)⌝ ∗ n ↦[wms][ c.toNat + 12 ] b0) ∗
    n ↦[i32][ (UInt32.ofNat (A.toNat - 8)).toNat ] w0 nx lst ∗ n ↦[i32][ (UInt32.ofNat (A.toNat - 8)).toNat + 4 ] c ∗
    (∃ bs' : List UInt8, ⌜bs'.length = nx.toNat - A.toNat⌝ ∗ n ↦[wms][ A.toNat ] bs') ∗
    nextW n nx (npv &&& 3 ||| (UInt32.ofNat (A.toNat - 8))) lst)

set_option maxHeartbeats 4000000 in
theorem split_spec_v (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (inst : Nat) (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (a574 : Nat)
    (h574 : mi.funcAddrs[574]? = some a574) (ty574 : FuncType)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv c nx npv A v : UInt32) (hv3 : v &&& 3 = 0) (lst : Bool) (bs : List UInt8)
    (hw1 : 1 ≤ w.toNat) (hc0 : 1 ≤ c.toNat) (hnx4 : nx &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32)
    (hbs : bs.length + 12 + c.toNat = nx.toNat)
    (hA4 : A.toNat % 4 = 0) (hA80 : c.toNat + 80 ≤ A.toNat) (hAw : A.toNat + 4 * w.toNat ≤ nx.toNat) :
    a574 ↪[wf] FuncInst.wasm ty574 inst f574 ∗ inst ↪[inst] mi ∗
      credits Cg (100 * cfg.regularOpCost + R) ∗
      n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] v ∗ n ↦[wms][ c.toNat + 12 ] bs ∗
      nextW n nx npv lst ∗
      (∀ l2 : UInt32, credits Cg R -∗ splitResV n c nx npv A v lst bs -∗
        Φ.br 12 [] ⟨#[.i32 w, .i32 c, .i32 l2, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
          .i32 (al + 4294967295), .i32 0, .i32 (UInt32.ofNat (A.toNat - 8)), .i32 nx, .i32 nx, .i32 (nx - w <<< 2),
          .i32 (c + 8 + 8 + 64)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
          .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 A, .i32 nx, .i32 (nx - w <<< 2),
          .i32 (c + 8 + 8 + 64)], inst, mi⟩ [] splitCode Φ := by
  iintro ⟨#H574, #Hi, Hc, H0, H8, Hd, Hn, HΦ⟩
  have hm : Hold (w0 nx lst &&& 4294967292 = nx) := ⟨w0_mask nx lst hnx4⟩
  have eN : (UInt32.ofNat (A.toNat - 8)).toNat = A.toNat - 8 := by
    have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hsub : Hold (A + 4294967288 = UInt32.ofNat (A.toNat - 8)) := ⟨by
    apply UInt32.toNat_inj.mp; rw [eN, UInt32.toNat_add]; simp; omega⟩
  have hb4 := Hold.mk (gt_false (UInt32.ofNat (A.toNat - 8)) A (by omega))
  have eS : (nx - (UInt32.ofNat (A.toNat - 8))).toNat = nx.toNat - (A.toNat - 8) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega), eN]
  have hb5 := Hold.mk (gt_false (nx - (UInt32.ofNat (A.toNat - 8))) nx (by omega))
  have hN3 : Hold ((UInt32.ofNat (A.toNat - 8)) &&& 3 = 0) := ⟨and3_of_mod4 _ (by omega)⟩
  have h574' : 8 ≤ (nx - (UInt32.ofNat (A.toNat - 8))).toNat := by omega
  have hs1 : c.toNat + 12 ≤ (UInt32.ofNat (A.toNat - 8)).toNat := by omega
  have hs2 : (UInt32.ofNat (A.toNat - 8)).toNat + 12 ≤ c.toNat + 12 + bs.length := by omega
  have hNA : (UInt32.ofNat (A.toNat - 8)).toNat + 8 = A.toNat := by omega
  have hnx0 : Hold (nx ≠ 0) := ⟨by intro h; subst h; simp at hcnx⟩
  have hF : Hold ((UInt32.ofNat (A.toNat - 8)).toNat + 8 = A.toNat ∧ (UInt32.ofNat (A.toNat - 8)).toNat + 12 ≤ nx.toNat) := ⟨⟨hNA, by omega⟩⟩
  clear eN eS hNA hA4 hA80 hAw
  icases split_data n c.toNat (UInt32.ofNat (A.toNat - 8)).toNat bs hs1 hs2 $$ Hd with
    ⟨%b0, %b8, %b4, %br, %⟨hb0, hb8, hb4', hbr⟩, Hd, HN8, HN4, HNr⟩
  ihave Hd : (∃ b0 : List UInt8, ⌜b0 = bs.take ((UInt32.ofNat (A.toNat - 8)).toNat - c.toNat - 12)⌝ ∗
      n ↦[wms][ c.toNat + 12 ] b0) $$ [Hd]
  · iexists b0; iframe Hd; ipureintro; exact hb0
  clear hb0
  have hH : Hold (br.length + (UInt32.ofNat (A.toNat - 8)).toNat + 12 = c.toNat + 12 + bs.length ∧ 8 ≤ (nx - (UInt32.ofNat (A.toNat - 8))).toNat) := ⟨⟨hbr, h574'⟩⟩
  clear hs1 hs2 hbr h574'
  simp only [splitCode]
  mstep; mstep; mstep
  rw [show A + 4294967288 = UInt32.ofNat (A.toNat - 8) from hsub.get]
  mstep; mstep; mstep
  mnot_taken hb4.get
  mstep; mstep; mstep; mstep; mstep; mstep
  mnot_taken hb5.get
  clear hb4 hb5
  mstep
  mcall (f574_spec cfg lim (d + 1) ty574 hr574 inst mi Cg (nx - (UInt32.ofNat (A.toNat - 8))) hH.get.2)
    with (simp [activationGas, entryLocals, f574, hp574]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs

  mstep; mstep; mstep [HN4]
  mstep; mstep; mstep [HN8]
  icases WNear.Binary.U128From.memBytes_split n (UInt32.ofNat (A.toNat - 8)).toNat 4 _ (by decide) $$ HN8 with ⟨HNa, HNb⟩
  rw [i64_zero_lo, i64_zero_hi]
  mstep; mstep; mstep [H0]; mstep; mstep
  rw [show w0 nx lst &&& 4294967292 = nx from hm.get]
  mstep [HNa]
  mstep; mstep; mstep [H0]; mstep; mstep; mstep
  rw [show w0 nx lst &&& 4294967292 = nx from hm.get]
  mstep; mstep
  mstep_not_taken with (exact eqz_false nx hnx0.get)
  mstep; mstep; mstep; mstep; mstep
  rw [w0_and2 nx lst hnx4]
  iapply mwpi_cons
  iapply WNear.Binary.AllocNewCell.mwpi_select_ite
  isplitl [Hc]; · iexact Hc
  isplitr; · ipureintro; exact ⟨rfl, by omega⟩
  inext; iintro Hc
  ihave HN4r : (∃ bs' : List UInt8, ⌜bs'.length = nx.toNat - A.toNat⌝ ∗ n ↦[wms][ A.toNat ] bs') $$ [HN4 HNr]
  · iexists bytes32 0 ++ br
    obtain ⟨h1, h2⟩ := hF.get
    obtain ⟨h3, h4⟩ := hH.get
    isplitr
    · ipureintro; simp [bytes32]; omega
    iapply WNear.Binary.AllocNewCell.memBytes_addr (show (UInt32.ofNat (A.toNat - 8)).toNat + 8 = A.toNat by omega)
    iapply WNear.Binary.U128From.memBytes_join n ((UInt32.ofNat (A.toNat - 8)).toNat + 8) 4 _ _ (by simp [bytes32])
    rw [show (UInt32.ofNat (A.toNat - 8)).toNat + 8 + 4 = (UInt32.ofNat (A.toNat - 8)).toNat + 12 by omega]
    iframe HN4 HNr
  clear hF hH hb8 hb4'
  cases lst
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    mctrl_norm
    rw [nextW_false]
    mstep; mstep
    mstep_not_taken with (exact eqz_false nx hnx0.get)
    mstep; mstep; mstep [Hn]; mstep; mstep; mstep; mstep; mstep [Hn]
    mstep; mstep; mstep [HNb]; mstep; mstep; mstep; mstep
    rw [zero_and_or]
    mstep [HNb]
    mstep; mstep; mstep [H8]; mstep; mstep
    rw [v_and2 v hv3]
    mstep [H8]
    rw [show w0 nx false = nx from rfl]
    mstep; mstep; mstep [H0]; mstep; mstep; mstep; mstep; mstep
    rw [v_false nx (UInt32.ofNat (A.toNat - 8)) hnx4]
    mstep [H0]
    mstep; mstep; mstep
    rw [and2_zero (UInt32.ofNat (A.toNat - 8)) (show (UInt32.ofNat (A.toNat - 8)) &&& 3 = 0 from hN3.get)]
    mstep
    iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, eqz_true 0 rfl⟩
    simp only [List.reverse_nil, Post.mseq_br]
    mcredits R
    iapply HΦ $$ %_ Hc
    iunfold splitResV
    rw [nextW_false, show w0 nx false = nx from rfl]
    iframe H0 H8 Hd HNa HNb HN4r Hn
  · simp only [ite_true, show (2 : UInt32) ≠ 0 by decide, ite_false]
    mctrl_norm
    mstep; mstep
    mstep_taken with (exact eqz_true _ rfl)
    mstep; mstep; mstep [HNb]; mstep; mstep; mstep; mstep
    rw [zero_and_or]
    mstep [HNb]
    mstep; mstep; mstep [H8]; mstep; mstep
    rw [v_and2 v hv3]
    mstep [H8]
    rw [show w0 nx true = nx ||| 2 from rfl]
    mstep; mstep; mstep [H0]; mstep; mstep; mstep; mstep; mstep
    rw [v_true nx (UInt32.ofNat (A.toNat - 8)) hnx4 (show (UInt32.ofNat (A.toNat - 8)) &&& 3 = 0 from hN3.get)]
    mstep [H0]
    mstep; mstep; mstep
    rw [or2_and2]
    mstep
    mstep_not_taken with (exact eqz_false 2 (by decide))
    mstep; mstep; mstep; mstep
    rw [or2_clear (UInt32.ofNat (A.toNat - 8)) (show (UInt32.ofNat (A.toNat - 8)) &&& 3 = 0 from hN3.get)]
    mstep [H0]
    mstep; mstep; mstep [HNa]; mstep; mstep; mstep [HNa]
    iapply mwpi_br
    mcredits R
    iapply HΦ $$ %_ Hc
    iunfold splitResV
    rw [nextW_true, nextW_true, show w0 nx true = nx ||| 2 from rfl]
    iframe H0 H8 Hd HNa HNb HN4r

end SplitSpec

section Body7

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The free cell `c`'s walk resources, `next_free = v`: header word 0, `next_free`, data, the
next neighbour's `prev` word, the policy's vtable slot and table entry. -/
def cellW (n : Nat) (c nx npv v : UInt32) (lst : Bool) (bs : List UInt8) (pv idx : UInt32) (ta a578 : Nat) :
    IProp GF :=
  iprop(n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] v ∗ n ↦[wms][ c.toNat + 12 ] bs ∗
    nextW n nx npv lst ∗ n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578)

/-- The code `body7` calls (persistent). -/
def code7 (inst : Nat) (mi : ModuleInst) (a572 a576 a574 a578 : Nat) (ty572 ty576 ty574 : FuncType) : IProp GF :=
  iprop(a572 ↪[wf] FuncInst.wasm ty572 inst f572 ∗ a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗
    a574 ↪[wf] FuncInst.wasm ty574 inst f574 ∗ a578 ↪[wf] FuncInst.wasm mi.types[13]! inst f578 ∗
    inst ↪[inst] mi)

instance (inst : Nat) (mi : ModuleInst) (a572 a576 a574 a578 : Nat) (ty572 ty576 ty574 : FuncType) :
    Persistent (code7 (GF := GF) inst mi a572 a576 a574 a578 ty572 ty576 ty574) := by
  unfold code7; infer_instance

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- One iteration of the merge loop (`@7`) on the free cell `c`, without `CAN_MERGE`
(`v &&& 3 = 0`), the locals `l9 … l13` anything: too small → `br` out of `@7` to the unlink
(`Φ.br 1`); not splittable → `Φ.br 0` (the alignment test); split → `Φ.br 4` (the end of the
walk, the new cell's header written but not its `ALLOCATED` bit). -/
theorem body7 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (I : List Value → Frame → IProp GF) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv idx c nx npv v l9 l10 l11 l12 l13 : UInt32) (lst : Bool) (bs : List UInt8) (k : Nat)
    (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (hc0 : 1 ≤ c.toNat) (hnx4 : nx &&& 3 = 0) (hv3 : v &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32)
    (hbs : bs.length + 12 + c.toNat = nx.toNat) (K7 : Nat)
    (hK7 : (if fits w c nx then 279 else 80) * cfg.regularOpCost ≤ K7) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574 ∗
      credits Cg (K7 + R) ∗ cellW n c nx npv v lst bs pv idx ta a578 ∗
      ((⌜¬ fits w c nx⌝ -∗ credits Cg R -∗ cellW n c nx npv v lst bs pv idx ta a578 -∗
          Φ.br 1 [] ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 (w <<< 2), .i32 l11, .i32 l12, .i32 l13], inst, mi⟩) ∧
       (⌜fits w c nx ∧ ¬ canSplit w al c nx⌝ -∗ credits Cg (120 * cfg.regularOpCost + R) -∗
          cellW n c nx npv v lst bs pv idx ta a578 -∗
          Φ.br 0 [] ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 (nx - w <<< 2 &&& 0 - al), .i32 nx,
            .i32 (nx - w <<< 2), .i32 (c + 8 + 8 + 64)], inst, mi⟩) ∧
       (∀ A : UInt32, ∀ l2 : UInt32, ⌜A.toNat = aN nx w al ∧ fits w c nx ∧ canSplit w al c nx⌝ -∗
          credits Cg (40 * cfg.regularOpCost + R) -∗ splitResV n c nx npv A v lst bs -∗
          n ↦[i32][ pv.toNat + 16 ] idx -∗ ta ↦[wt][ idx.toNat ] Ref.func a578 -∗
          Φ.br 4 [] ⟨#[.i32 w, .i32 c, .i32 l2, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (UInt32.ofNat (A.toNat - 8)), .i32 nx, .i32 nx,
            .i32 (nx - w <<< 2), .i32 (c + 8 + 8 + 64)], inst, mi⟩))
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l7Body
          (Post.mloop cfg Cg 0 [] I Φ) := by
  iintro ⟨#Hk, Hc, HR, HO⟩
  iunfold code7 at Hk
  icases Hk with ⟨#H572, #H576, #H574, #H578, #Hi⟩
  iunfold cellW at HR
  icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
  by_cases hfit : fits w c nx
  swap
  · rw [if_neg hfit] at hK7
    mcredits (80 * cfg.regularOpCost + R)
    mstep; mstep; mstep [H8]; mstep; mstep; mstep
    mstep_not_taken with (exact v_and1 v hv3)
    mstep; mstep; mstep; mstep; mstep
    mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg w (by omega))
      with (simp [activationGas, entryLocals, f572, hp572]; omega)
    · ipureintro; trivial
    icases HQ with %hrs
    subst hrs
    mstep; mstep
    have hm := w0_mask nx lst hnx4
    mcall (f576_spec cfg lim (d + 1) ty576 hr576 inst mi n hn Cg c (w0 nx lst) (by omega)
        (by rw [hm]; omega)) using [H0]
      with (simp [activationGas, entryLocals, f576, hp576]; omega)
    · iframe H0
    icases HQ with ⟨%hrs, H0⟩
    subst hrs
    rw [hm]
    mstep
    mstep
    have e1 := sub8_toNat nx c (by omega)
    have e2 := WNear.Binary.AllocNewCell.shl2_toNat w (by omega)
    · iapply mwpi_cons
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, lt_true _ _ (by unfold fits szN at hfit; rw [e1, e2]; omega)⟩
      simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, List.nil_append]
      clear e1 e2
      icases HO with ⟨HU, -⟩
      mcredits R
      iapply HU $$ %hfit Hc
      iunfold cellW
      iframe H0 H8 Hd Hn Hv Ht
  rw [if_pos hfit] at hK7
  mcredits (279 * cfg.regularOpCost + R)
  mstep; mstep; mstep [H8]; mstep; mstep; mstep
  mstep_not_taken with (exact v_and1 v hv3)
  mstep; mstep; mstep; mstep; mstep
  mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg w (by omega))
    with (simp [activationGas, entryLocals, f572, hp572]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep; mstep
  have hm := w0_mask nx lst hnx4
  mcall (f576_spec cfg lim (d + 1) ty576 hr576 inst mi n hn Cg c (w0 nx lst) (by omega)
      (by rw [hm]; omega)) using [H0]
    with (simp [activationGas, entryLocals, f576, hp576]; omega)
  · iframe H0
  icases HQ with ⟨%hrs, H0⟩
  subst hrs
  rw [hm]
  mstep
  mstep
  have e1 := sub8_toNat nx c (by omega)
  have e2 := WNear.Binary.AllocNewCell.shl2_toNat w (by omega)
  have hnf := lt_false (nx - c + 4294967288) (w <<< 2) (by unfold fits szN at hfit; rw [e1, e2]; omega)
  have hfit' : 4 * w.toNat ≤ nx.toNat - c.toNat - 8 := hfit
  have e3 : (nx - w <<< 2).toNat = nx.toNat - 4 * w.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, e2]; omega), e2]; omega
  have hgt := gt_false (nx - w <<< 2) nx (by rw [e3]; omega)
  clear e1 e2 hfit'
  mstep_not_taken with (exact hnf)
  clear hnf
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep [H0]; mstep; mstep
  rw [hm]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (exact hgt)
  clear hgt
  mstep
  mstep_not_taken
  mstep; mstep; mstep; mstep [Hv]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 13) (t := 0) (ta := ta) (idx := idx) (a := a578)
    (type := mi.types[13]!) (inst := inst) (mi := mi) (code := f578) [.i32 pd, .i32 w])
  isplitr
  · iapply (f578_spec cfg lim (d + 1) mi.types[13]! hrt578 inst mi Cg pd w)
  isplitr; · iexact H578
  isplitr; · iexact Hi
  isplitl [Ht]; · iexact Ht
  isplitr; · ipureintro; exact ⟨rfl, hta, rfl, by simp [hty578], hd⟩
  isplitl [Hc]; · iexact Hc
  isplitr; · ipureintro; mstep_norm_full; omega
  isplitr; · ipureintro; rfl
  inext
  iintro %rs Ht Hc %hrs
  subst hrs
  mctrl_norm
  mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg 16 (by decide))
    with (simp [activationGas, entryLocals, f572, hp572]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  rw [show (16 : UInt32) <<< 2 = 64 by decide]
  have e16 : (c + 8 + 8).toNat = c.toNat + 16 := by
    rw [UInt32.toNat_add, UInt32.toNat_add]; simp; omega
  have e80 : (c + 8 + 8 + 64).toNat = c.toNat + 80 := by
    rw [UInt32.toNat_add, e16]; simp; omega
  have e8 : (c + 8).toNat = c.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have hb1 := lt_false (c + 8 + 8) (c + 8) (by omega)
  have hb2 := lt_false (c + 8 + 8 + 64) (c + 8 + 8) (by omega)
  have eA : (nx - w <<< 2 &&& 0 - al).toNat = aN nx w al := by
    rw [and_neg_toNat (nx - w <<< 2) al k hal hk, e3]; rfl
  clear e16 e3
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (exact hb1)
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (exact hb2)
  clear hb1 hb2
  mstep; mstep; mstep; mstep; mstep; mstep
  by_cases hsplit : canSplit w al c nx
  swap
  · have hb := gt_true (c + 8 + 8 + 64) (nx - w <<< 2 &&& 0 - al) (by
      unfold canSplit at hsplit; rw [e80, eA]; omega)
    clear eA e80 e8
    iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hb⟩
    clear hb
    simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, List.nil_append]
    icases HO with ⟨-, HO⟩
    icases HO with ⟨HN, -⟩
    mcredits (120 * cfg.regularOpCost + R)
    iapply HN $$ %⟨hfit, hsplit⟩ Hc
    iunfold cellW
    iframe H0 H8 Hd Hn Hv Ht
  have hb := gt_false (c + 8 + 8 + 64) (nx - w <<< 2 &&& 0 - al) (by
    have h := hsplit; unfold canSplit at h; rw [e80, eA]; omega)
  have hAm4 := aN_mod4 nx w al k hal (toNat_mod4 nx hnx4)
  have hfit' : 4 * w.toNat ≤ nx.toNat - c.toNat - 8 := hfit
  have hsplit' : c.toNat + 80 ≤ aN nx w al := hsplit
  have hAle : aN nx w al + 4 * w.toNat ≤ nx.toNat := by
    unfold aN; have := Nat.mod_le (nx.toNat - 4 * w.toNat) al.toNat; omega
  generalize hAd : (nx - w <<< 2 &&& 0 - al) = A at *
  clear e80 hAd e8
  mstep_not_taken with (exact hb)
  clear hb
  have hF : Hold (A.toNat = aN nx w al ∧ A.toNat % 4 = 0 ∧ c.toNat + 80 ≤ A.toNat ∧
      A.toNat + 4 * w.toNat ≤ nx.toNat) := ⟨⟨eA, by omega, by omega, by omega⟩⟩
  clear eA hAm4 hfit' hsplit' hAle
  iapply split_spec_v cfg lim d _ inst mi n hn a574 h574 ty574 hp574 hr574 hd Cg
    (40 * cfg.regularOpCost + R) w al slot pd pv c nx npv A v hv3 lst bs hw1 hc0 hnx4 hcnx hnx hbs
    hF.get.2.1 hF.get.2.2.1 hF.get.2.2.2
  isplitr; · iexact H574
  isplitr; · iexact Hi
  isplitl [Hc]; · mcredits (100 * cfg.regularOpCost + (40 * cfg.regularOpCost + R)); iexact Hc
  iframe H0 H8 Hd Hn
  iintro %l2 Hc HS
  simp only [Post.mblock_br_succ, Post.mseq_br, Post.mloop_br_succ, List.nil_append]
  icases HO with ⟨-, -, HS'⟩
  iapply HS' $$ %A %l2 %⟨hF.get.1, hfit, hsplit⟩ Hc HS Hv Ht

end Body7

section Body3

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What the caller of `body3` gives for each outcome (see `body3`). -/
def obl3 (cfg : WasmConfig) (Cg R : Nat) (Φ : Post NearState GF) (I : List Value → Frame → IProp GF)
    (inst : Nat) (mi : ModuleInst) (n : Nat) (w al slot pd pv idx c nx npv v s : UInt32) (lst : Bool)
    (bs : List UInt8) (ta a578 : Nat) : IProp GF :=
  iprop(
       (∀ m10 : UInt32, ∀ m11 : UInt32, ∀ m12 : UInt32, ∀ m13 : UInt32, ⌜¬ fits w c nx ∨ (¬ canSplit w al c nx ∧ ¬ aligned al c)⌝ -∗
          credits Cg R -∗ n ↦[i32][ slot.toNat ] v -∗
          cellW n c nx npv v lst bs pv idx ta a578 -∗
          I [] ⟨#[.i32 w, .i32 v, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 m10, .i32 m11, .i32 m12, .i32 m13], inst, mi⟩) ∧
       (⌜fits w c nx ∧ ¬ canSplit w al c nx ∧ aligned al c⌝ -∗ credits Cg (100 * cfg.regularOpCost + R) -∗
          n ↦[i32][ slot.toNat ] s -∗ cellW n c nx npv v lst bs pv idx ta a578 -∗
          Φ.normal [] ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 (nx - w <<< 2 &&& 0 - al), .i32 nx,
            .i32 (nx - w <<< 2), .i32 (c + 8 + 8 + 64)], inst, mi⟩) ∧
       (∀ A : UInt32, ∀ l2 : UInt32, ⌜A.toNat = aN nx w al ∧ fits w c nx ∧ canSplit w al c nx⌝ -∗
          credits Cg (40 * cfg.regularOpCost + R) -∗ n ↦[i32][ slot.toNat ] s -∗
          splitResV n c nx npv A v lst bs -∗
          n ↦[i32][ pv.toNat + 16 ] idx -∗ ta ↦[wt][ idx.toNat ] Ref.func a578 -∗
          Φ.br 0 [] ⟨#[.i32 w, .i32 c, .i32 l2, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (UInt32.ofNat (A.toNat - 8)), .i32 nx, .i32 nx,
            .i32 (nx - w <<< 2), .i32 (c + 8 + 8 + 64)], inst, mi⟩)
  )

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- One iteration of the walk (`@3`) at the free cell `c ≠ 0` without `CAN_MERGE`, its
`next_free` `v`: unlinked (the slot gets `v`, the walk goes on at `v`), taken whole (the loop
ends, `Φ.normal`), or split (`Φ.br 0`, the end of the walk). -/
theorem body3 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (I : List Value → Frame → IProp GF) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv idx c nx npv v s l9 l10 l11 l12 l13 : UInt32) (lst : Bool) (bs : List UInt8) (k : Nat)
    (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (hc0 : 1 ≤ c.toNat) (hnx4 : nx &&& 3 = 0) (hv3 : v &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32)
    (hbs : bs.length + 12 + c.toNat = nx.toNat) (K3 : Nat)
    (hK3 : (if fits w c nx then 291 else 92) * cfg.regularOpCost ≤ K3) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574 ∗
      credits Cg (K3 + R) ∗ n ↦[i32][ slot.toNat ] s ∗
      cellW n c nx npv v lst bs pv idx ta a578 ∗
      obl3 cfg Cg R Φ I inst mi n w al slot pd pv idx c nx npv v s lst bs ta a578
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l3Body
          (Post.mloop cfg Cg 0 [] I Φ) := by
  iintro ⟨#Hk, Hc, Hs, HR, HO⟩
  have hcne : c ≠ 0 := by intro h; subst h; simp at hc0
  have hK3a : 92 * cfg.regularOpCost ≤ K3 := le_trans (by split <;> omega) hK3
  have hK7 : (if fits w c nx then 279 else 80) * cfg.regularOpCost ≤ K3 - 12 * cfg.regularOpCost := by
    split at hK3 <;> split <;> simp_all <;> omega
  mstep; mstep
  mstep_not_taken with (exact eqz_false c hcne)
  mstep; mstep; mstep
  mcredits (cfg.regularOpCost + ((K3 - 12 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R)))
  iapply mwpi_loop_pin (Cg := Cg) (R := (K3 - 12 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R)) .empty _
    iprop(credits Cg ((K3 - 12 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R)) ∗ cellW n c nx npv v lst bs pv idx ta a578 ∗
      n ↦[i32][ slot.toNat ] s ∗ obl3 cfg Cg R Φ I inst mi n w al slot pd pv idx c nx npv v s lst bs ta a578) rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc; iframe Hc HR Hs HO
  imodintro
  iintro ⟨Hc, HR, Hs, HO⟩
  iunfold obl3 at HO
  iapply (body7 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
    hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (8 * cfg.regularOpCost + R) w al slot pd pv idx c nx npv v
    l9 l10 l11 l12 l13 lst bs k hal hk hw1 hw2 hc0 hnx4 hv3 hcnx hnx hbs _ hK7)
  iframe Hk Hc HR
  have e8 : (c + 8).toNat = c.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  isplit
  · -- too small: the unlink
    iintro %hfit Hc HR
    simp only [Post.mblock_br_succ, Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
    mctrl_norm
    mpay
    iunfold cellW at HR
    icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
    mstep; mstep; mstep [H8]; mstep; mstep [Hs]
    iapply mwpi_br
    simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
    iapply pure_pay_intro'
    isplitl [Hc]; · iexact Hc
    isplitr; · ipureintro; exact ⟨by simp, by omega⟩
    inext; iintro Hc
    simp only [List.length_nil, List.drop_nil]
    icases HO with ⟨HU, -⟩
    mcredits R
    iapply HU $$ %(w <<< 2) %l11 %l12 %l13 %(Or.inl hfit) Hc Hs
    iunfold cellW
    iframe H0 H8 Hd Hn Hv Ht
  isplit
  · -- not splittable: the alignment
    iintro %⟨hfit, hsplit⟩ Hc HR
    simp only [Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
    mctrl_norm
    mpay
    mstep; mstep; mstep; mstep
    by_cases hali : aligned al c
    · have hb := eqz_and_true (c + 8) al k hal hk (by rw [e8]; exact hali)
      iapply mwpi_cons
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, hb⟩
      clear hb
      simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero,
        List.nil_append]
      mpay
      simp only [Post.mloop_normal, List.nil_append]
      mpay
      icases HO with ⟨-, HO⟩
      icases HO with ⟨HW, -⟩
      mcredits (100 * cfg.regularOpCost + R)
      iapply HW $$ %⟨hfit, hsplit, hali⟩ Hc Hs HR
    · have hb := eqz_and_false (c + 8) al k hal hk (by rw [e8]; exact hali)
      mstep_not_taken with (exact hb)
      clear hb
      iunfold cellW at HR
      icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
      mstep; mstep; mstep [H8]; mstep; mstep [Hs]
      iapply mwpi_br
      simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
      iapply pure_pay_intro'
      isplitl [Hc]; · iexact Hc
      isplitr; · ipureintro; exact ⟨by simp, by omega⟩
      inext; iintro Hc
      simp only [List.length_nil, List.drop_nil]
      icases HO with ⟨HU, -⟩
      mcredits R
      iapply HU $$ %_ %_ %_ %_ %(Or.inr ⟨hsplit, hali⟩) Hc Hs
      iunfold cellW
      iframe H0 H8 Hd Hn Hv Ht
  · -- split
    iintro %A %l2 %hS Hc HS Hv Ht
    simp only [Post.mblock_br_succ, Post.mseq_br, Post.mloop_br_succ, List.nil_append]
    icases HO with ⟨-, -, HS'⟩
    mcredits (40 * cfg.regularOpCost + R)
    iapply HS' $$ %A %l2 %hS Hc Hs HS Hv Ht

end Body3

section Merge7

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem or1_and1 (b : UInt32) : (b ||| 1) &&& 1 ≠ 0 := by
  intro h
  have := congrArg UInt32.toNat h
  rw [WNear.Binary.AllocRemove.u32_and_1, UInt32.toNat_or] at this
  have e : (b.toNat ||| 1) % 2 = 1 := by
    rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.or_mod_two_pow]; have := Nat.mod_lt b.toNat (show 2 ^ 1 > 0 by decide)
    rcases (show b.toNat % 2 ^ 1 = 0 ∨ b.toNat % 2 ^ 1 = 1 by omega) with h | h <;> rw [h] <;> rfl
  simp at this; omega

theorem or1_clear (b : UInt32) (h : b &&& 3 = 0) : (b ||| 1) &&& 4294967294 = b := by
  apply u32_ext; intro i hi
  have h4 := toNat_mod4 b h
  simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or]
  rcases (show i = 0 ∨ 1 ≤ i by omega) with rfl | hi1
  · rw [tb_low _ 0 h4 (by omega)]; decide
  · have h1 : (1 : Nat).testBit i = false := by
      rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp; omega
    have h2 : (4294967294 : Nat).testBit i = true := by
      have := tb_mid 4294967292 i (by omega)
      interval_cases i <;> decide
    rw [h1, h2]; simp

theorem byte_and1_u (a : UInt32) (h : a &&& 3 = 0) : UInt32.ofNat (a.toNat % 256) &&& 1 = 0 := by
  have h4 := toNat_mod4 a h
  apply UInt32.toNat_inj.mp
  rw [WNear.Binary.AllocRemove.u32_and_1]; simp only [UInt32.toNat_ofNat']; simp; omega

theorem nextOf_w0 (nx : UInt32) (lst : Bool) (h : nx &&& 3 = 0) :
    WNear.Binary.AllocRemove.nextOf (w0 nx lst) = if lst then 0 else nx := by
  unfold WNear.Binary.AllocRemove.nextOf
  rw [w0_and2 nx lst h, w0_mask nx lst h]
  cases lst <;> simp

theorem w0_and3 (nx : UInt32) (lst : Bool) (h : nx &&& 3 = 0) : w0 nx lst &&& 3 = if lst then 2 else 0 := by
  cases lst
  · exact h
  · simp only [w0, ite_true]
    apply u32_ext; intro i hi
    have h4 := toNat_mod4 nx h
    simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or]
    rcases (show i < 2 ∨ 2 ≤ i by omega) with h1 | h1
    · rw [tb_low _ i h4 h1]; interval_cases i <;> decide
    · rw [tb_small 3 i (by omega) h1, tb_small 2 i (by omega) h1]; simp

theorem and3_or_u (x y : UInt32) (h : x &&& 3 = 0) : x &&& 3 ||| y = y := by
  rw [h]; apply UInt32.toNat_inj.mp; rw [UInt32.toNat_or]; simp

/-- The code `merge7` calls (persistent). -/
def code575 (inst : Nat) (mi : ModuleInst) (a575 a576 : Nat) (ty575 ty576 : FuncType) : IProp GF :=
  iprop(a575 ↪[wf] FuncInst.wasm ty575 inst f575 ∗ a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗
    inst ↪[inst] mi)

instance (inst : Nat) (mi : ModuleInst) (a575 a576 : Nat) (ty575 ty576 : FuncType) :
    Persistent (code575 (GF := GF) inst mi a575 a576 ty575 ty576) := by
  unfold code575; infer_instance

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- The merge iteration of `@7`: the listed cell `a` has `CAN_MERGE` (`next_free = b | 1`) and
its previous neighbour is the free cell `b` (`b.word0 = a`); `a` is removed from its chunk
(575), `b` gets `a`'s end (and `NEXT_CELL_IS_INVALID` if `a` was last), the slot gets `b`, and
the loop goes on at `b`. -/
theorem merge7 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (I : List Value → Frame → IProp GF) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a575 a576 : Nat)
    (h575 : mi.funcAddrs[575]? = some a575) (h576 : mi.funcAddrs[576]? = some a576)
    (ty575 ty576 : FuncType)
    (hp575 : ty575.params.length = 1) (hr575 : ty575.results.length = 0)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv a b anx l9 l10 l11 l12 l13 : UInt32) (alst : Bool)
    (ha3 : a &&& 3 = 0) (hb3 : b &&& 3 = 0) (hnx3 : anx &&& 3 = 0)
    (hb0 : 1 ≤ b.toNat) (hba : b.toNat + 12 ≤ a.toNat) (han : a.toNat + 12 ≤ anx.toNat)
    (hnx : anx.toNat + 65536 ≤ 2 ^ 32) :
    code575 inst mi a575 a576 ty575 ty576 ∗ credits Cg (170 * cfg.regularOpCost + R) ∗
      n ↦[i32][ slot.toNat ] a ∗ n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 4 ] b ∗
      n ↦[i32][ a.toNat + 8 ] (b ||| 1) ∗ n ↦[i32][ b.toNat ] a ∗ nextW n anx a alst ∗
      (credits Cg R -∗ n ↦[i32][ slot.toNat ] b -∗ n ↦[i32][ a.toNat ] (w0 anx alst &&& 3) -∗
        n ↦[i32][ a.toNat + 4 ] 0 -∗ n ↦[i32][ a.toNat + 8 ] b -∗ n ↦[i32][ b.toNat ] w0 anx alst -∗
        nextW n anx b alst -∗
        I [] ⟨#[.i32 w, .i32 b, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
          .i32 (al + 4294967295), .i32 0, .i32 b, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l7Body
          (Post.mloop cfg Cg 0 [] I Φ) := by
  iintro ⟨#Hk, Hc, Hs, Ha0, Ha4, Ha8, Hb0, Hn, HO⟩
  iunfold code575 at Hk
  icases Hk with ⟨#H575, #H576, #Hi⟩
  have hbne : b ≠ 0 := by intro h; subst h; simp at hb0
  have ham := v_and3m b hb3
  mstep; mstep; mstep [Ha8]; mstep; mstep; mstep
  mstep_taken with (exact or1_and1 b)
  mstep; mstep; mstep; mstep
  rw [or1_clear b hb3]
  mstep [Ha8]
  mstep; mstep; mstep; mstep [Ha4]; mstep; mstep
  rw [ham]
  mstep
  mstep_taken with (exact hbne)
  mstep; mstep; mstep
  iapply mwpi_cons; iapply WNear.Binary.AllocDealloc.mwpi_load8u_w (addr := b.toNat) (w := a)
  iframe Hc; isplitr
  · ipureintro; exact ⟨rfl, rfl, by omega, hn⟩
  iframe Hb0; inext; iintro Hc Hb0; mctrl_norm
  mstep; mstep
  rw [byte_and1_u a ha3]
  iapply mwpi_cons
  iapply WNear.Binary.AllocNewCell.mwpi_select_ite
  isplitl [Hc]; · iexact Hc
  isplitr; · ipureintro; exact ⟨rfl, by omega⟩
  inext; iintro Hc
  simp only [↓reduceIte]
  mctrl_norm
  mstep; mstep
  have s575 := WNear.Binary.AllocRemove.f575_spec (GF := GF) cfg lim (d + 1) ty575 hr575 inst mi n hn Cg
    a (w0 anx alst) b a a
  rw [nextOf_w0 anx alst hnx3, ham] at s575
  have hw0m := w0_mask anx alst hnx3
  have hw03 := w0_and3 anx alst hnx3
  cases alst
  · simp only [Bool.false_eq_true, ↓reduceIte] at s575 hw03
    have hnx0 : anx ≠ 0 := by intro h; subst h; simp at han
    simp only [WNear.Binary.AllocRemove.ptsIf, ne_eq, hnx0, hbne, not_false_eq_true, ↓reduceIte] at s575
    simp only [nextW_false]
    mcall s575 using [Ha0 Ha4 Hn Hb0] with (simp [activationGas, entryLocals, f575, hp575]; omega)
    · iframe Ha0 Ha4 Hn Hb0
    icases HQ with ⟨%hrs, Ha0, Ha4, Hn, Hb0⟩
    subst hrs
    clear s575
    rw [hw03, and3_or_u a b ha3, and3_or_u a _ ha3, hw0m, show (b &&& 3) = 0 from hb3]
    mstep; mstep
    iapply mwpi_cons; iapply WNear.Binary.AllocDealloc.mwpi_load8u_w (addr := a.toNat) (w := 0)
    iframe Hc; isplitr
    · ipureintro; exact ⟨rfl, rfl, by omega, hn⟩
    iframe Ha0; inext; iintro Hc Ha0; mctrl_norm
    mstep; mstep; mstep
    mstep_taken with decide
    mstep; mstep; mstep [Hs]
    mstep
    have s576 := f576_spec (GF := GF) cfg lim (d + 1) ty576 hr576 inst mi n hn Cg b anx (by omega)
      (by rw [v_and3m anx hnx3]; omega)
    mcall s576 using [Hb0] with (simp [activationGas, entryLocals, f576, hp576]; omega)
    · iframe Hb0
    icases HQ with ⟨%hrs, Hb0⟩
    subst hrs
    clear s576
    mstep; mstep; mstep
    iapply mwpi_br
    simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
    iapply pure_pay_intro'
    isplitl [Hc]; · iexact Hc
    isplitr; · ipureintro; exact ⟨by simp, by omega⟩
    inext; iintro Hc
    simp only [List.length_nil, List.drop_nil]
    mcredits R
    simp only [w0, ↓reduceIte, Bool.false_eq_true]
    iapply HO $$ Hc Hs Ha0 Ha4 Ha8 Hb0 Hn
  · simp only [↓reduceIte] at s575 hw03
    simp only [WNear.Binary.AllocRemove.ptsIf, ne_eq, not_true_eq_false, hbne, not_false_eq_true,
      ↓reduceIte] at s575
    simp only [nextW_true]
    mcall s575 using [Ha0 Ha4 Hb0] with (simp [activationGas, entryLocals, f575, hp575]; omega)
    · iframe Ha0 Ha4 Hb0
    icases HQ with ⟨%hrs, Ha0, Ha4, -, Hb0⟩
    subst hrs
    clear s575
    rw [hw03, and3_or_u a _ ha3, hw0m, show (b &&& 3) = 0 from hb3]
    mstep; mstep
    iapply mwpi_cons; iapply WNear.Binary.AllocDealloc.mwpi_load8u_w (addr := a.toNat) (w := 2)
    iframe Hc; isplitr
    · ipureintro; exact ⟨rfl, rfl, by omega, hn⟩
    iframe Ha0; inext; iintro Hc Ha0; mctrl_norm
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep [Hb0]; mstep; mstep; mstep [Hb0]
    mstep; mstep; mstep [Hs]
    mstep
    have s576 := f576_spec (GF := GF) cfg lim (d + 1) ty576 hr576 inst mi n hn Cg b (anx ||| 2) (by omega)
      (by rw [show (anx ||| 2) = w0 anx true from rfl, hw0m]; omega)
    mcall s576 using [Hb0] with (simp [activationGas, entryLocals, f576, hp576]; omega)
    · iframe Hb0
    icases HQ with ⟨%hrs, Hb0⟩
    subst hrs
    clear s576
    mstep; mstep; mstep
    iapply mwpi_br
    simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
    iapply pure_pay_intro'
    isplitl [Hc]; · iexact Hc
    isplitr; · ipureintro; exact ⟨by simp, by omega⟩
    inext; iintro Hc
    simp only [List.length_nil, List.drop_nil]
    mcredits R
    simp only [w0, ↓reduceIte, Bool.false_eq_true]
    iapply HO $$ Hc Hs Ha0 Ha4 Ha8 Hb0
    iempintro

end Merge7

section Merge3

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem merge_data (n b a : Nat) (bsb bsa : List UInt8) (x y z : UInt32) (h : b + 12 + bsb.length = a) :
    n ↦[wms][ b + 12 ] bsb ∗ n ↦[i32][ a ] x ∗ n ↦[i32][ a + 4 ] y ∗ n ↦[i32][ a + 8 ] z ∗
      n ↦[wms][ a + 12 ] bsa ⊢
    (n ↦[wms][ b + 12 ] (bsb ++ bytes32 x ++ bytes32 y ++ bytes32 z ++ bsa) : IProp GF) := by
  iintro ⟨H1, H2, H3, H4, H5⟩
  have l4 : ∀ v : UInt32, (bytes32 v).length = 4 := fun v => by simp [bytes32]
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  iapply WNear.Binary.U128From.memBytes_join n (b + 12) bsb.length _ _ rfl
  iframe H1
  rw [h]
  iapply WNear.Binary.U128From.memBytes_join n a 4 _ _ (l4 x)
  iframe H2
  iapply WNear.Binary.U128From.memBytes_join n (a + 4) 4 _ _ (l4 y)
  iframe H3
  rw [show a + 4 + 4 = a + 8 by omega]
  iapply WNear.Binary.U128From.memBytes_join n (a + 8) 4 _ _ (l4 z)
  iframe H4
  rw [show a + 8 + 4 = a + 12 by omega]
  iexact H5

/-- The data of the cell `b` once the next cell `a` (header `x`, `y`, `next_free` `z`, data
`bsa`) is merged into it. -/
def mergedBs (bsb bsa : List UInt8) (x y z : UInt32) : List UInt8 := bsb ++ bytes32 x ++ bytes32 y ++ bytes32 z ++ bsa

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- One iteration of the walk (`@3`) at a listed cell `a` with `CAN_MERGE`, whose previous
neighbour `b` (free, `next_free = 0`) is the next listed cell: `a` is merged into `b`
(`merge7`), then `b`, grown to `a`'s end, is walked as in `body3` (its outcomes `obl3`). -/
theorem merge3 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (I : List Value → Frame → IProp GF) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a575 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h575 : mi.funcAddrs[575]? = some a575)
    (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty575 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp575 : ty575.params.length = 1) (hr575 : ty575.results.length = 0)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv idx a b anx l9 l10 l11 l12 l13 : UInt32) (alst : Bool) (bsa bsb : List UInt8) (k : Nat)
    (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (ha3 : a &&& 3 = 0) (hb3 : b &&& 3 = 0) (hnx3 : anx &&& 3 = 0)
    (hb0 : 1 ≤ b.toNat) (hba : b.toNat + 12 ≤ a.toNat) (han : a.toNat + 12 ≤ anx.toNat)
    (hnx : anx.toNat + 65536 ≤ 2 ^ 32)
    (hbsb : bsb.length + 12 + b.toNat = a.toNat) (hbsa : bsa.length + 12 + a.toNat = anx.toNat)
    (K : Nat) (hK : (if fits w b anx then 462 else 262) * cfg.regularOpCost ≤ K) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574 ∗ code575 inst mi a575 a576 ty575 ty576 ∗
      credits Cg (K + R) ∗ n ↦[i32][ slot.toNat ] a ∗
      n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 4 ] b ∗ n ↦[i32][ a.toNat + 8 ] (b ||| 1) ∗
      n ↦[wms][ a.toNat + 12 ] bsa ∗ n ↦[i32][ b.toNat ] a ∗ n ↦[i32][ b.toNat + 8 ] 0 ∗
      n ↦[wms][ b.toNat + 12 ] bsb ∗ nextW n anx a alst ∗
      n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578 ∗
      obl3 cfg Cg R Φ I inst mi n w al slot pd pv idx b anx b 0 b alst
        (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) ta a578
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l3Body
          (Post.mloop cfg Cg 0 [] I Φ) := by
  iintro ⟨#Hk, #Hk5, Hc, Hs, Ha0, Ha4, Ha8, Hda, Hb0, Hb8, Hdb, Hn, Hv, Ht, HO⟩
  have hane : a ≠ 0 := by intro h; subst h; simp at hba
  have hKa : 262 * cfg.regularOpCost ≤ K := le_trans (by split <;> omega) hK
  have hK7 : (if fits w b anx then 279 else 80) * cfg.regularOpCost ≤ K - 182 * cfg.regularOpCost := by
    split at hK <;> split <;> simp_all <;> omega
  have hbs' : (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b).length + 12 + b.toNat = anx.toNat := by
    simp [mergedBs, bytes32]; omega
  mstep; mstep
  mstep_not_taken with (exact eqz_false a hane)
  mstep; mstep; mstep
  mcredits (cfg.regularOpCost + (170 * cfg.regularOpCost + ((K - 182 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R))))
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg)
    (R := 170 * cfg.regularOpCost + ((K - 182 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R))) .empty _
    (fun X g => iprop(⌜X = []⌝ ∗
      ((⌜g = ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩⌝ ∗
          credits Cg (170 * cfg.regularOpCost + ((K - 182 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R))) ∗
          n ↦[i32][ slot.toNat ] a ∗
          n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 4 ] b ∗ n ↦[i32][ a.toNat + 8 ] (b ||| 1) ∗
          n ↦[wms][ a.toNat + 12 ] bsa ∗ n ↦[i32][ b.toNat ] a ∗ n ↦[i32][ b.toNat + 8 ] 0 ∗
          n ↦[wms][ b.toNat + 12 ] bsb ∗ nextW n anx a alst ∗
          n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578 ∗
          obl3 cfg Cg R Φ I inst mi n w al slot pd pv idx b anx b 0 b alst
            (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) ta a578) ∨
       (⌜g = ⟨#[.i32 w, .i32 b, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 b, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩⌝ ∗
          credits Cg ((K - 182 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R)) ∗ n ↦[i32][ slot.toNat ] b ∗
          cellW n b anx b 0 alst (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) pv idx ta a578 ∗
          obl3 cfg Cg R Φ I inst mi n w al slot pd pv idx b anx b 0 b alst
            (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) ta a578))))
    rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc
    isplitr; · ipureintro; rfl
    ileft
    iframe Hc Hs Ha0 Ha4 Ha8 Hda Hb0 Hb8 Hdb Hn Hv Ht HO
    ipureintro; rfl
  imodintro
  iintro %X %l ⟨%hX, HI⟩
  subst hX
  icases HI with (⟨%hg, Hc, Hs, Ha0, Ha4, Ha8, Hda, Hb0, Hb8, Hdb, Hn, Hv, Ht, HO⟩ | ⟨%hg, Hc, Hs, HR, HO⟩)
  · rw [hg]
    iapply (merge7 cfg lim d _ _ inst mi n hn a575 a576 h575 h576 ty575 ty576 hp575 hr575 hp576 hr576 hd Cg
      ((K - 182 * cfg.regularOpCost) + (8 * cfg.regularOpCost + R)) w al slot pd pv a b anx l9 l10 l11 l12 l13 alst ha3 hb3 hnx3 hb0 hba han hnx)
    iframe Hk5 Hs Ha0 Ha4 Ha8 Hb0 Hn
    isplitl [Hc]; · iexact Hc
    iintro Hc Hs Ha0 Ha4 Ha8 Hb0 Hn
    isplitr; · ipureintro; rfl
    iright
    isplitr; · ipureintro; rfl
    iframe Hc Hs HO
    iunfold cellW
    iframe Hb0 Hb8 Hn Hv Ht
    unfold mergedBs
    iapply merge_data n b.toNat a.toNat bsb bsa _ _ _ (by omega)
    iframe Hdb Ha0 Ha4 Ha8 Hda
  rw [hg]
  iapply (body7 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
    hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (8 * cfg.regularOpCost + R) w al slot pd pv idx b anx b 0
    b l10 l11 l12 l13 alst (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) k hal hk hw1 hw2 hb0 hnx3 (by decide) (by omega)
    hnx hbs' _ hK7)
  iframe Hk Hc HR
  iunfold obl3 at HO
  have e8 : (b + 8).toNat = b.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  isplit
  · -- too small: the unlink
    iintro %hfit Hc HR
    simp only [Post.mblock_br_succ, Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
    mctrl_norm
    mpay
    iunfold cellW at HR
    icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
    mstep; mstep; mstep [H8]; mstep; mstep [Hs]
    iapply mwpi_br
    simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
    iapply pure_pay_intro'
    isplitl [Hc]; · iexact Hc
    isplitr; · ipureintro; exact ⟨by simp, by omega⟩
    inext; iintro Hc
    simp only [List.length_nil, List.drop_nil]
    icases HO with ⟨HU, -⟩
    mcredits R
    iapply HU $$ %(w <<< 2) %l11 %l12 %l13 %(Or.inl hfit) Hc Hs
    iunfold cellW
    iframe H0 H8 Hd Hn Hv Ht
  isplit
  · -- not splittable: the alignment
    iintro %⟨hfit, hsplit⟩ Hc HR
    simp only [Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
    mctrl_norm
    mpay
    mstep; mstep; mstep; mstep
    by_cases hali : aligned al b
    · have hb := eqz_and_true (b + 8) al k hal hk (by rw [e8]; exact hali)
      iapply mwpi_cons
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, hb⟩
      clear hb
      simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero,
        List.nil_append]
      mpay
      simp only [Post.mloop_normal, List.nil_append]
      mpay
      icases HO with ⟨-, HO⟩
      icases HO with ⟨HW, -⟩
      mcredits (100 * cfg.regularOpCost + R)
      iapply HW $$ %⟨hfit, hsplit, hali⟩ Hc Hs HR
    · have hb := eqz_and_false (b + 8) al k hal hk (by rw [e8]; exact hali)
      mstep_not_taken with (exact hb)
      clear hb
      iunfold cellW at HR
      icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
      mstep; mstep; mstep [H8]; mstep; mstep [Hs]
      iapply mwpi_br
      simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
      iapply pure_pay_intro'
      isplitl [Hc]; · iexact Hc
      isplitr; · ipureintro; exact ⟨by simp, by omega⟩
      inext; iintro Hc
      simp only [List.length_nil, List.drop_nil]
      icases HO with ⟨HU, -⟩
      mcredits R
      iapply HU $$ %_ %_ %_ %_ %(Or.inr ⟨hsplit, hali⟩) Hc Hs
      iunfold cellW
      iframe H0 H8 Hd Hn Hv Ht
  · -- split
    iintro %A %l2 %hS Hc HS Hv Ht
    simp only [Post.mblock_br_succ, Post.mseq_br, Post.mloop_br_succ, List.nil_append]
    icases HO with ⟨-, -, HS'⟩
    mcredits (40 * cfg.regularOpCost + R)
    iapply HS' $$ %A %l2 %hS Hc Hs HS Hv Ht

end Merge3

section Exits

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code after the walk's loop in its block (the whole cell's unlink), and after that
block (the `ALLOCATED` bit, the result). -/
abbrev yRest : List Instr :=
  [Instr.local_get 2, Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 8 },
    Instr.i32_const 4294967292, Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 0 },
    Instr.local_get 1, Instr.local_set 9]

abbrev xRest : List Instr :=
  [Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 0 },
    Instr.i32_const 1, Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 0 },
    Instr.local_get 9, Instr.i32_const 8, Instr.i32_binop IBinOp.add, Instr.local_set 5]

/-- The walk loop's continuation, the function's own `Φf` after it. -/
abbrev postY (cfg : WasmConfig) (lim : ExecLimits) (d Cg : Nat) (Φf : Post NearState GF) : Post NearState GF :=
  Post.mseq cfg lim d yRest (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d xRest
    (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d [Instr.local_get 5] Φf))))

set_option maxHeartbeats 4000000 in
/-- The loop ended on taking the cell `c` whole: the slot gets `c`'s `next_free`, `c` is
marked allocated, the result is `c + 8`. -/
theorem exitW (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φf : Post NearState GF) (inst : Nat)
    (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat)
    (w al slot pd pv c v s x l5 l10 l11 l12 l13 : UInt32) (hc : c.toNat + 12 < 2 ^ 32) :
    credits Cg (30 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] s ∗ n ↦[i32][ c.toNat ] x ∗
      n ↦[i32][ c.toNat + 8 ] v ∗
      (∀ g, credits Cg R -∗ n ↦[i32][ slot.toNat ] (v &&& 4294967292) -∗ n ↦[i32][ c.toNat ] (x ||| 1) -∗
        n ↦[i32][ c.toNat + 8 ] v -∗ Φf.normal [.i32 (c + 8)] g)
      ⊢ (postY cfg lim d Cg Φf).normal [] ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 l5, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ := by
  iintro ⟨Hc, Hs, H0, H8, HK⟩
  unfold postY
  simp only [Post.mseq_normal, List.nil_append]
  mstep; mstep; mstep [H8]; mstep; mstep; mstep [Hs]
  mstep; mstep
  mstep; mstep; mstep [H0]; mstep; mstep; mstep [H0]
  mstep; mstep; mstep; mstep
  mstep
  mcredits R
  iapply HK $$ %_ Hc Hs H0 H8

set_option maxHeartbeats 4000000 in
/-- The loop ended on a split, the new cell `N`: `N` is marked allocated, the result `N + 8`. -/
theorem exitS (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φf : Post NearState GF) (inst : Nat)
    (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat)
    (w al c l2 pd pv N l5 nx l12 l13 x : UInt32) :
    credits Cg (30 * cfg.regularOpCost + R) ∗ n ↦[i32][ N.toNat ] x ∗
      (∀ g, credits Cg R -∗ n ↦[i32][ N.toNat ] (x ||| 1) -∗ Φf.normal [.i32 (N + 8)] g)
      ⊢ (postY cfg lim d Cg Φf).br 0 [] ⟨#[.i32 w, .i32 c, .i32 l2, .i32 pd, .i32 pv, .i32 l5, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 N, .i32 nx, .i32 nx, .i32 l12, .i32 l13], inst, mi⟩ := by
  iintro ⟨Hc, H0, HK⟩
  unfold postY
  simp only [Post.mseq_br, Post.mblock_br_zero, List.nil_append]
  mctrl_norm
  mpay
  mstep; mstep; mstep [H0]; mstep; mstep; mstep [H0]
  mstep; mstep; mstep; mstep
  mstep
  mcredits R
  iapply HK $$ %_ Hc H0

set_option maxHeartbeats 4000000 in
/-- The walk found nothing (`l1 = 0` at the loop's head): the result is `l5 = 0`. -/
theorem exit0 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φf : Post NearState GF) (inst : Nat)
    (mi : ModuleInst) (Cg R : Nat) (w al slot pd pv l9 l10 l11 l12 l13 : UInt32) (I : List Value → Frame → IProp GF) :
    credits Cg (10 * cfg.regularOpCost + R) ∗
      (∀ g, credits Cg R -∗ Φf.normal [.i32 0] g)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 0, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l3Body
          (Post.mloop cfg Cg 0 [] I (postY cfg lim d Cg Φf)) := by
  iintro ⟨Hc, HK⟩
  mstep; mstep
  mstep_taken
  unfold postY
  mloop_norm
  mstep
  mcredits R
  iapply HK $$ %_ Hc

end Exits

section Two

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A free cell's walk resources but the vtable's (`cellW` without `vt`). -/
def cellR (n : Nat) (c nx npv v : UInt32) (lst : Bool) (bs : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] v ∗ n ↦[wms][ c.toNat + 12 ] bs ∗
    nextW n nx npv lst)

/-- 580's result on the list `[a, b]` without `CAN_MERGE`: `a` too small, unlinked and kept as it
is, and `post1` on `b`; or `a` taken whole (the slot gets `b`) or split (the slot keeps `a`),
`b` untouched. -/
def post2 (n : Nat) (w al slot a anx anpv b bnx bnpv : UInt32) (alst blst : Bool) (bsa bsb : List UInt8)
    (pv idx : UInt32) (ta a578 : Nat) (args rs : List Value) : IProp GF :=
  iprop((⌜¬ fits w a anx⌝ ∗ cellR n a anx anpv b alst bsa ∗
      post1 n w al slot b bnx bnpv blst bsb pv idx ta a578 args rs) ∨
    (∃ r : UInt32, ⌜rs = [.i32 r]⌝ ∗ vt n pv idx ta a578 ∗ cellR n b bnx bnpv 0 blst bsb ∗
      ((⌜r = a + 8 ∧ fits w a anx ∧ ¬ canSplit w al a anx⌝ ∗
          n ↦[i32][ slot.toNat ] b ∗ n ↦[i32][ a.toNat ] (w0 anx alst ||| 1) ∗ n ↦[i32][ a.toNat + 8 ] b ∗
          n ↦[wms][ a.toNat + 12 ] bsa ∗ nextW n anx anpv alst) ∨
       (⌜r.toNat = aN anx w al ∧ fits w a anx ∧ canSplit w al a anx⌝ ∗
          n ↦[i32][ slot.toNat ] a ∗ n ↦[i32][ a.toNat ] (r - 8) ∗ n ↦[i32][ a.toNat + 8 ] b ∗
          n ↦[wms][ a.toNat + 12 ] bsa.take (r.toNat - 8 - a.toNat - 12) ∗
          n ↦[i32][ r.toNat - 8 ] (w0 anx alst ||| 1) ∗ n ↦[i32][ r.toNat - 4 ] a ∗
          (∃ bs' : List UInt8, ⌜bs'.length = anx.toNat - r.toNat⌝ ∗ n ↦[wms][ r.toNat ] bs') ∗
          nextW n anx (anpv &&& 3 ||| (r - 8)) alst))))

theorem aligned_one (al c : UInt32) (h : al.toNat = 1) : aligned al c := by
  unfold aligned; rw [h]; exact Nat.mod_one _

/-- The split's resources, as `post1`/`post2` state them. -/
theorem split_post (n : Nat) (c nx npv A v : UInt32) (lst : Bool) (bs : List UInt8)
    (hA80 : c.toNat + 80 ≤ A.toNat) :
    splitResV (GF := GF) n c nx npv A v lst bs ⊢
      n ↦[i32][ c.toNat ] (A - 8) ∗ n ↦[i32][ c.toNat + 8 ] v ∗
        n ↦[wms][ c.toNat + 12 ] bs.take (A.toNat - 8 - c.toNat - 12) ∗
        n ↦[i32][ (A - 8).toNat ] w0 nx lst ∗ n ↦[i32][ A.toNat - 4 ] c ∗
        (∃ bs' : List UInt8, ⌜bs'.length = nx.toNat - A.toNat⌝ ∗ n ↦[wms][ A.toNat ] bs') ∗
        nextW n nx (npv &&& 3 ||| (A - 8)) lst := by
  have eNN : (UInt32.ofNat (A.toNat - 8)).toNat = A.toNat - 8 := by
    have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hAm8 : A - 8 = UInt32.ofNat (A.toNat - 8) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega), eNN]; simp
  iintro H
  iunfold splitResV at H
  icases H with ⟨H0, H8, ⟨%b0, %hb0, Hd⟩, HNa, HNb, HN4r, Hn⟩
  rw [hAm8]
  rw [eNN] at hb0 ⊢
  ihave HNb := WNear.Binary.AllocNewCell.memBytes_addr (show A.toNat - 8 + 4 = A.toNat - 4 by omega) $$ HNb
  ihave Hd := WNear.Binary.AllocNewCell.memBytes_eq (show b0 = bs.take (A.toNat - 8 - c.toNat - 12) by
    rw [hb0]) $$ Hd
  iframe H0 H8 Hd HNa HNb HN4r Hn

end Two

section Skip

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- `body7` on a cell too small for the request: only its word 0 and `next_free` are read. -/
theorem body7U (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (I : List Value → Frame → IProp GF) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (ty572 ty576 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv c nx v l9 l10 l11 l12 l13 : UInt32) (lst : Bool)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (hc0 : 1 ≤ c.toNat) (hnx4 : nx &&& 3 = 0) (hv3 : v &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32) (hfit : ¬ fits w c nx) :
    a572 ↪[wf] FuncInst.wasm ty572 inst f572 ∗ a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗ inst ↪[inst] mi ∗
      credits Cg (80 * cfg.regularOpCost + R) ∗ n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] v ∗
      (credits Cg R -∗ n ↦[i32][ c.toNat ] w0 nx lst -∗ n ↦[i32][ c.toNat + 8 ] v -∗
          Φ.br 1 [] ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 (w <<< 2), .i32 l11, .i32 l12, .i32 l13], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l7Body
          (Post.mloop cfg Cg 0 [] I Φ) := by
  iintro ⟨#H572, #H576, #Hi, Hc, H0, H8, HU⟩
  mstep; mstep; mstep [H8]; mstep; mstep; mstep
  mstep_not_taken with (exact v_and1 v hv3)
  mstep; mstep; mstep; mstep; mstep
  mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg w (by omega))
    with (simp [activationGas, entryLocals, f572, hp572]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep; mstep
  have hm := w0_mask nx lst hnx4
  mcall (f576_spec cfg lim (d + 1) ty576 hr576 inst mi n hn Cg c (w0 nx lst) (by omega)
      (by rw [hm]; omega)) using [H0]
    with (simp [activationGas, entryLocals, f576, hp576]; omega)
  · iframe H0
  icases HQ with ⟨%hrs, H0⟩
  subst hrs
  rw [hm]
  mstep
  mstep
  have e1 := sub8_toNat nx c (by omega)
  have e2 := WNear.Binary.AllocNewCell.shl2_toNat w (by omega)
  iapply mwpi_cons
  iapply mwpi_br_if_taken'
  isplitr
  · ipureintro; exact ⟨rfl, lt_true _ _ (by unfold fits szN at hfit; rw [e1, e2]; omega)⟩
  simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, List.nil_append]
  clear e1 e2
  mcredits R
  iapply HU $$ Hc H0 H8

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- `body3` on a cell too small for the request: unlinked, the walk goes on at its
`next_free`; only its word 0 and `next_free` are read. -/
theorem body3U (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (I : List Value → Frame → IProp GF) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (ty572 ty576 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv c nx v s l9 l10 l11 l12 l13 : UInt32) (lst : Bool)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (hc0 : 1 ≤ c.toNat) (hnx4 : nx &&& 3 = 0) (hv3 : v &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32) (hfit : ¬ fits w c nx) :
    a572 ↪[wf] FuncInst.wasm ty572 inst f572 ∗ a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗ inst ↪[inst] mi ∗
      credits Cg (92 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] s ∗
      n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] v ∗
      (credits Cg R -∗ n ↦[i32][ slot.toNat ] v -∗ n ↦[i32][ c.toNat ] w0 nx lst -∗ n ↦[i32][ c.toNat + 8 ] v -∗
          I [] ⟨#[.i32 w, .i32 v, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 (w <<< 2), .i32 l11, .i32 l12, .i32 l13], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] l3Body
          (Post.mloop cfg Cg 0 [] I Φ) := by
  iintro ⟨#H572, #H576, #Hi, Hc, Hs, H0, H8, HU⟩
  have hcne : c ≠ 0 := by intro h; subst h; simp at hc0
  mstep; mstep
  mstep_not_taken with (exact eqz_false c hcne)
  mstep; mstep; mstep
  mcredits (cfg.regularOpCost + (80 * cfg.regularOpCost + (8 * cfg.regularOpCost + R)))
  iapply mwpi_loop_pin (Cg := Cg) (R := 80 * cfg.regularOpCost + (8 * cfg.regularOpCost + R)) .empty _
    iprop(credits Cg (80 * cfg.regularOpCost + (8 * cfg.regularOpCost + R)) ∗ n ↦[i32][ c.toNat ] w0 nx lst ∗
      n ↦[i32][ c.toNat + 8 ] v ∗ n ↦[i32][ slot.toNat ] s ∗
      (credits Cg R -∗ n ↦[i32][ slot.toNat ] v -∗ n ↦[i32][ c.toNat ] w0 nx lst -∗ n ↦[i32][ c.toNat + 8 ] v -∗
          I [] ⟨#[.i32 w, .i32 v, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 (w <<< 2), .i32 l11, .i32 l12, .i32 l13], inst, mi⟩))
    rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc; iframe Hc H0 H8 Hs HU
  imodintro
  iintro ⟨Hc, H0, H8, Hs, HU⟩
  iapply (body7U cfg lim d _ _ inst mi n hn a572 a576 h572 h576 ty572 ty576 hp572 hr572 hp576 hr576 hd Cg
    (8 * cfg.regularOpCost + R) w al slot pd pv c nx v l9 l10 l11 l12 l13 lst hw1 hw2 hc0 hnx4 hv3 hcnx hnx hfit)
  iframe H572 H576 Hi Hc H0 H8
  iintro Hc H0 H8
  simp only [Post.mblock_br_succ, Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
  mctrl_norm
  mpay
  mstep; mstep; mstep [H8]; mstep; mstep [Hs]
  iapply mwpi_br
  simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
  iapply pure_pay_intro'
  isplitl [Hc]; · iexact Hc
  isplitr; · ipureintro; exact ⟨by simp, by omega⟩
  inext; iintro Hc
  simp only [List.length_nil, List.drop_nil]
  mcredits R
  iapply HU $$ Hc Hs H0 H8

end Skip

end WNear.Binary.AllocTwoWalk
