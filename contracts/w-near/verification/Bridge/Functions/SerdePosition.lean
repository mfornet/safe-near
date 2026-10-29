import Bridge.Functions.ParseStr

/-!
# serde_json's error position (M6): `position_of_index` (645) and `peek_position` (638)

Every syntax error serde_json builds (`peek_error`, `error`, 647, 657) first computes the line and
column of the reader's index, by scanning the input up to it:

```wat
;; 609 <RangeTo as SliceIndex>::index(out, ptr, len, idx, loc)   583(0, idx): out := (ptr, idx)
;; 645 position_of_index(out, rd, idx)
(start, end) := (ptr, ptr + idx)                    ;; 609 on the slice of the reader
line := 1
loop                                                ;; once per line
  k := 0
  loop                                              ;; the bytes of the line
    k = end - start → out := (line, k); return
    [start + k] = '\n' → line += 1; start += k + 1; next line
    k += 1
;; 638 position(out, rd)  645(out, rd, rd.index)
```

The overflow checks (`line + 1`, `k + 1`) never fail: both stay below `idx + 1`.

The error paths need only some finite cost (`Refines` asks a rejected call to roll back, and
running out of gas is a rollback too), so the specification here is loose: the result is some
pair `(line, column)`, and the cost is at most `cost645 idx = 200 + 50 · idx`.

* `f609_spec` (70, a 16-byte frame).
* `f645_spec`: some `(line, column)`, at most `cost645 idx`, a 32-byte stack. The line loop's
  invariant (`invO`) holds the start `ptr + j` of the current line and its number `L ≤ j + 1`; the
  byte loop's (`invI`) the offset `k ≤ idx - j`; both hold `50` per byte left.
* `f638_spec`: the same at the reader's index (`rd n de ptr bs i`), at most
  `cost638 i = 40 + cost645 i`, a 48-byte stack.

The input length is below `2^32 - 1` (`hlen`), so the line counter cannot wrap.
-/

namespace WNear.Binary.SerdePosition

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word)

set_option hygiene false in
/-- A `br_if` taken (the condition `h`), out of the enclosing blocks. -/
local macro "brt " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, $h⟩
  mctrl_norm; repeat mpay))

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

section L609

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<RangeTo<usize> as SliceIndex<[u8]>>::index(out, ptr, len, idx, loc)`** (609, 70), `idx ≤ len`:
the prefix `(ptr, idx)`, through 583 in a 16-byte frame. -/
theorem f609_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr len idx loc : UInt32) (ob : List UInt8) (hob : ob.length = 8)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hil : idx.toNat ≤ len.toNat) (hsp : 16 ≤ sp.toNat) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f609 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 len, .i32 idx, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 70 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 16) 16 ∗
          n ↦[i32][ out.toNat ] ptr ∗ n ↦[i32][ out.toNat + 4 ] idx)) := by
  iintro ⟨#F583, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 16) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  simp only [f609]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  have t36 : types[36]!.params.length = 6 := by rfl
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 16 + 8 = (sp - 16 + 8).toNat by
    rw [UInt32.toNat_add, h16]; simp; omega) $$ S8'
  mcall (ParseStr.f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 16 + 8) 0 idx ptr len loc
    s8 hs8 (by rw [UInt32.toNat_add, h16]; simp; omega) (by simp) hil) using [S8']
  · iframe S8'
  icases HQ with ⟨%hrs, P0, P4⟩
  subst hrs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  mstep; mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep [O0]
  mstep; mstep; mstep [P4] with (simp [UInt32.toNat_add]; omega)
  mstep [O4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hg
  rw [show ptr + 0 = ptr by simp, show idx - 0 = idx by simp]
  iframe O0 O4
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P8 := VecFromElem.stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 16 + 8 by
    rw [UInt32.toNat_add, h16]; simp; omega) $$ P8
  iapply stk_join n (sp.toNat - 16) 8 8
  iframe S8 P8

end L609

theorem add_ofNat_sub (ptr : UInt32) (j idx : Nat) (hj : j ≤ idx) (hidx : idx < 2 ^ 32) :
    (ptr + UInt32.ofNat idx) - (ptr + UInt32.ofNat j) = UInt32.ofNat (idx - j) := by
  apply UInt32.toNat_inj.mp
  have := ptr.toNat_lt
  simp [UInt32.toNat_sub, UInt32.toNat_add]
  omega

theorem add_ofNat_step (ptr : UInt32) (j k : Nat) :
    ptr + UInt32.ofNat j + UInt32.ofNat k + 1 = ptr + UInt32.ofNat (j + k + 1) := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_add]
  omega

set_option maxRecDepth 100000 in
theorem eq10 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq x.toUInt32 10) = if x.toNat = 10 then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

/-- `position_of_index`'s cost bound on an index `idx`, activation excluded. -/
def cost645 (idx : Nat) : Nat := 200 + 50 * idx

section L645

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 645's frame: `(out, k, a, sp, start, end, line, seg)`. -/
def fr645 (inst : Nat) (mi : ModuleInst) (out l1 l2 l3 l4 l5 l6 l7 : UInt32) : Frame :=
  ⟨#[.i32 out, .i32 l1, .i32 l2, .i32 l3, .i32 l4, .i32 l5, .i32 l6, .i32 l7], inst, mi⟩

/-- The line loop: at `start = ptr + j`, the line number `L ≤ j + 1`, `50` per byte left. -/
def invO (inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (out sp ptr : UInt32) (idx : Nat) (P : IProp GF) :
    List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (j L : Nat) (l1 l2 l7 : UInt32), ⌜X = [] ∧
      g = fr645 inst mi out l1 l2 sp (ptr + UInt32.ofNat j) (ptr + UInt32.ofNat idx) (UInt32.ofNat L) l7 ∧
      j ≤ idx ∧ L ≤ j + 1⌝ ∗
    credits Cg (50 * (idx - j) * c₀ + E * c₀ + R) ∗ P)

/-- The byte loop of the line at `j`: at `k ≤ idx - j`. -/
def invI (inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (out sp ptr : UInt32) (idx j L : Nat) (P : IProp GF) :
    List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l2 : UInt32), ⌜X = [] ∧
      g = fr645 inst mi out (UInt32.ofNat k) l2 sp (ptr + UInt32.ofNat j) (ptr + UInt32.ofNat idx)
        (UInt32.ofNat L) (UInt32.ofNat (idx - j)) ∧ k ≤ idx - j⌝ ∗
    credits Cg (50 * (idx - j - k) * c₀ + E * c₀ + R) ∗ P)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`position_of_index(out, rd, idx)`** (645), `idx ≤ len`: some `(line, column)` at `out`, at most
`cost645 idx`. The stack: 16 bytes, and 609's 16 below. -/
theorem f645_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 a609 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (ha609 : mi.funcAddrs[609]? = some a609)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr : UInt32) (ob bs : List UInt8) (idx : Nat) (hob : ob.length = 8)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hde : de.toNat + 8 ≤ 2 ^ 32) (hidx : idx ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 32 ≤ sp.toNat) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ a609 ↪[wf] FuncInst.wasm types[39]! inst f609 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f645 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 (UInt32.ofNat idx)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ de.toNat ] ptr ∗
          n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗ n ↦[wms][ ptr.toNat ] bs))
        (fun _ => cost645 idx * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 32) 32 ∗
          (∃ line col : UInt32, n ↦[i32][ out.toNat ] line ∗ n ↦[i32][ out.toNat + 4 ] col) ∗
          n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
          n ↦[wms][ ptr.toNat ] bs)) := by
  iintro ⟨#F583, #F609, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, D0, D4, Hb⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 32) 16 16 $$ Hs with ⟨S16, Hs⟩
  icases stk_split n (sp.toNat - 32 + 16) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  simp only [f645, cost645]
  rw [show (200 + 50 * idx) * cfg.regularOpCost + R =
    140 * cfg.regularOpCost + (50 * (idx - 0) * cfg.regularOpCost + 60 * cfg.regularOpCost + R) by
      simp only [Nat.add_mul, Nat.sub_zero]; omega]
  generalize hW : 50 * (idx - 0) * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mstep; mstep [D0]; mstep; mstep [D4]; mstep; mstep
  have t39 : types[39]!.params.length = 5 := by rfl
  ihave S16 := VecFromElem.stk_addr (show sp.toNat - 32 = (sp - 16).toNat - 16 by omega) $$ S16
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 32 + 16 + 8 = (sp - 16 + 8).toNat by
    rw [UInt32.toNat_add, h16]; simp; omega) $$ S8'
  mcall (f609_spec cfg (lim := lim) (d + 1) types[39]! (by rfl) inst mi n g hn hg a583 ha583 (by omega) Cg gt
    (sp - 16) (sp - 16 + 8) ptr (UInt32.ofNat bs.length) (UInt32.ofNat idx) 1062152 s8 hs8
    (by rw [UInt32.toNat_add, h16]; simp; omega) (by simp; omega) (by omega)) using [Hg S16 S8']
  · iframe Hg S16 S8'
  icases HQ with ⟨%hrs, Hg, S16, P0, P4⟩
  subst hrs
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [P4] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := W + 60 * cfg.regularOpCost + R)
    (I := invO inst mi Cg cfg.regularOpCost 60 R out (sp - 16) ptr idx
      iprop(n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗ stk n (sp.toNat - 32 + 16) 8 ∗
        n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
        g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n ((sp - 16).toNat - 16) 16 ∗
        n ↦[i32][ (sp - 16 + 8).toNat ] ptr ∗ n ↦[i32][ (sp - 16 + 8).toNat + 4 ] UInt32.ofNat idx)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold invO at HI
    icases HI with ⟨%j, %L, %l1, %l2, %l7, %⟨hX, hfr, hj, hL⟩, Hc, HP⟩
    subst hX
    rw [hfr]
    simp only [fr645]
    clear hfr
    generalize hZ : 50 * (idx - j) * cfg.regularOpCost = Z
    rw [show Z + 60 * cfg.regularOpCost + R = 60 * cfg.regularOpCost + (Z + R) by omega]
    mstep; mstep; mstep
    rw [add_ofNat_sub ptr j idx hj (by omega)]
    mstep; mstep; mstep; mstep
    iapply mwpi_cons
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := Z + 40 * cfg.regularOpCost + R)
      (I := invI inst mi Cg cfg.regularOpCost 40 R out (sp - 16) ptr idx j L
        iprop(n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗ stk n (sp.toNat - 32 + 16) 8 ∗
          n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
          g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n ((sp - 16).toNat - 16) 16 ∗
          n ↦[i32][ (sp - 16 + 8).toNat ] ptr ∗ n ↦[i32][ (sp - 16 + 8).toNat + 4 ] UInt32.ofNat idx)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold invI at HI
      icases HI with ⟨%k, %l2', %⟨hX, hfr, hk⟩, Hc, HP⟩
      subst hX
      rw [hfr]
      simp only [fr645]
      clear hfr
      by_cases hke : k = idx - j
      · subst hke
        rw [show 50 * (idx - j - (idx - j)) * cfg.regularOpCost + 40 * cfg.regularOpCost + R =
          40 * cfg.regularOpCost + R by simp]
        mstep; mstep; mstep
        brt (by simp [Numeric.bool, Numeric.irelop32])
        (try simp only [Post.mloop]); mctrl_norm; (repeat mpay)
        icases HP with ⟨Ho, Hb, S8, D0, D4, Hg, S16, P0, P4⟩
        icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
        mstep; mstep; mstep [O4]
        mstep; mstep; mstep [O0]
        mstep; mstep; mstep; mstep [Hg]
        rw [show sp - 16 + 16 = sp by simp]
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        isplitr
        · ipureintro; trivial
        iframe Hg D0 D4 Hb
        isplitl [S8 S16 P0 P4]
        · ihave P0 := stk_word n _ _ $$ P0
          ihave P4 := stk_word n _ _ $$ P4
          ihave P8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [P0 P4]
          · iframe P0 P4
          ihave P8 := VecFromElem.stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 32 + 16 + 8 by
            rw [h8, h16]; omega) $$ P8
          ihave S16' := stk_join n (sp.toNat - 32 + 16) 8 8 $$ [S8 P8]
          · iframe S8 P8
          ihave S16 := VecFromElem.stk_addr (show (sp - 16).toNat - 16 = sp.toNat - 32 by omega) $$ S16
          iapply stk_join n (sp.toNat - 32) 16 16
          iframe S16 S16'
        iexists _, _
        iframe O0 O4
      · have hkl : k < idx - j := by omega
        have hc : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat (idx - j)) (UInt32.ofNat k)) = 0 := by
          have hu : (UInt32.ofNat k).toNat = k := by simp; omega
          have hv : (UInt32.ofNat (idx - j)).toNat = idx - j := by simp; omega
          generalize UInt32.ofNat k = u at hu ⊢
          generalize UInt32.ofNat (idx - j) = v at hv ⊢
          have : v ≠ u := fun e => by subst e; omega
          simp [Numeric.bool, Numeric.irelop32, this]
        rw [show 50 * (idx - j - k) * cfg.regularOpCost + 40 * cfg.regularOpCost + R =
          90 * cfg.regularOpCost + (50 * (idx - j - (k + 1)) * cfg.regularOpCost + R) by
            rw [show idx - j - k = (idx - j - (k + 1)) + 1 by omega]; simp only [Nat.mul_add, Nat.add_mul]; omega]
        generalize hZ' : 50 * (idx - j - (k + 1)) * cfg.regularOpCost = Z'
        mstep; mstep; mstep
        brn hc
        clear hc
        icases HP with ⟨Ho, Hb, HR⟩
        ihave Hb := MemCpy.memBytes_pick n ptr.toNat (j + k) bs (by omega) $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        obtain ⟨x, hxk⟩ : ∃ x, bs[j + k]'(by omega) = x := ⟨_, rfl⟩
        rw [hxk]
        mstep; mstep; mstep; mstep; mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.load8]
        ihave Hb := MemCpy.memBytes_unpick n ptr.toNat (j + k) (bs.take (j + k)) x (bs.drop (j + k + 1)) (by simp; omega) $$ [B1 Bk B2]
        · iframe B1 Bk B2
        rw [show List.take (j + k) bs ++ x :: List.drop (j + k + 1) bs = bs by rw [← hxk]; simp]
        mstep; mstep
        rw [eq10]
        by_cases hx : x.toNat = 10
        · rw [if_pos hx]
          brt (by decide)
          (try simp only [Post.mloop]); mctrl_norm; (repeat mpay)
          mstep; mstep; mstep
          rw [SerdeRead.ofNat_succ L (by omega)]
          mstep; mstep; mstep
          rw [FromUtf8.ltu_ofNat _ _ (by omega), if_neg (by simp; omega)]
          brn rfl
          mstep; mstep; mstep
          rw [add_ofNat_step]
          mstep; mstep; mstep; mstep
          iunfold invO
          iexists j + k + 1, L + 1, UInt32.ofNat (L + 1), ptr + UInt32.ofNat j + UInt32.ofNat k, UInt32.ofNat (idx - j)
          isplitr
          · ipureintro; exact ⟨rfl, rfl, by omega, by omega⟩
          rw [show idx - (j + k + 1) = idx - j - (k + 1) by omega, hZ']
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iframe Ho Hb HR
        · rw [if_neg hx]
          brn rfl
          mstep; mstep; mstep
          rw [SerdeRead.ofNat_succ k (by omega)]
          mstep; mstep; mstep
          rw [FromUtf8.ltu_ofNat _ _ (by omega), if_neg (by simp; omega)]
          brn rfl
          mstep; mstep; mstep
          simp only [Post.mloop]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          simp only [List.length_nil, Nat.sub_zero, List.drop_nil]
          iunfold invI
          iexists k + 1, UInt32.ofNat (k + 1)
          isplitr
          · ipureintro; exact ⟨rfl, rfl, by omega⟩
          rw [hZ']
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iframe Ho Hb HR
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    inext
    iintro Hc
    iunfold invI
    iexists 0, l2
    isplitr
    · ipureintro; exact ⟨rfl, rfl, by omega⟩
    rw [Nat.sub_zero, hZ]
    iframe Hc HP
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iunfold invO
  iexists 0, 1, de, UInt32.ofNat idx, 0
  isplitr
  · ipureintro; exact ⟨rfl, by simp [fr645], Nat.zero_le _, by omega⟩
  rw [hW]
  iframe Hc Ho Hb S8 D0 D4 Hg S16 P0 P4

end L645

end WNear.Binary.SerdePosition

namespace WNear.Binary.SerdePosition

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)

/-- `position`'s cost bound at the index `i`. -/
def cost638 (i : Nat) : Nat := 40 + cost645 i

section L638

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::position(out, rd)`** (638): `position_of_index` at the reader's index `i`, some
`(line, column)` at `out`, at most `cost638 i`. The stack: 48 bytes. -/
theorem f638_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 a609 a645 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (ha609 : mi.funcAddrs[609]? = some a609)
    (ha645 : mi.funcAddrs[645]? = some a645) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr : UInt32) (ob bs : List UInt8) (i : Nat) (hob : ob.length = 8)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 48 ≤ sp.toNat) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ a609 ↪[wf] FuncInst.wasm types[39]! inst f609 ∗
      a645 ↪[wf] FuncInst.wasm types[31]! inst f645 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f638 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i))
        (fun _ => cost638 i * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 48) 48 ∗
          (∃ line col : UInt32, n ↦[i32][ out.toNat ] line ∗ n ↦[i32][ out.toNat + 4 ] col) ∗
          rd n de ptr bs i)) := by
  iintro ⟨#F583, #F609, #F645, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hrd⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  icases stk_split n (sp.toNat - 48) 32 16 $$ Hs with ⟨S32, Hs⟩
  icases stk_split n (sp.toNat - 48 + 32) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  simp only [f638, cost638]
  rw [show (40 + cost645 i) * cfg.regularOpCost + R = 40 * cfg.regularOpCost + (cost645 i * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep [D8] with (simp [UInt32.toNat_add]; omega)
  have t31 : types[31]!.params.length = 3 := by rfl
  ihave S32 := VecFromElem.stk_addr (show sp.toNat - 48 = (sp - 16).toNat - 32 by omega) $$ S32
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 48 + 32 + 8 = (sp - 16 + 8).toNat by omega) $$ S8'
  have hK2 : (12 + cost645 (UInt32.ofNat i).toNat) * cfg.regularOpCost = 12 * cfg.regularOpCost + cost645 i * cfg.regularOpCost := by
    rw [show (UInt32.ofNat i).toNat = i by simp; omega, Nat.add_mul]
  have hK3 : (13 + cost645 i) * cfg.regularOpCost = 13 * cfg.regularOpCost + cost645 i * cfg.regularOpCost := Nat.add_mul _ _ _
  mcall (f645_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n g hn hg a583 a609 ha583 ha609 (by omega)
    Cg gt (sp - 16) (sp - 16 + 8) de ptr s8 bs i hs8 (by omega) (by omega) hi hlen hptr (by omega))
    using [Hg S32 S8' D0 D4 Hb]
  · iframe Hg S32 S8' D0 D4 Hb
  rw [hK3, show 29 * cfg.regularOpCost + (cost645 i * cfg.regularOpCost + R) -
    (13 * cfg.regularOpCost + cost645 i * cfg.regularOpCost) = 16 * cfg.regularOpCost + R by omega]
  icases HQ with ⟨%hrs, Hg, S32, ⟨%line, %col, L0, L4⟩, D0, D4, Hb⟩
  subst hrs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  mstep; mstep; mstep [L0] with (simp [UInt32.toNat_add]; omega)
  mstep [O0]
  mstep; mstep; mstep [L4] with (simp [UInt32.toNat_add]; omega)
  mstep [O4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hg
  isplitl [S32 S8 L0 L4]
  · ihave L0 := stk_word n _ _ $$ L0
    ihave L4 := stk_word n _ _ $$ L4
    ihave L8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave L8 := VecFromElem.stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 48 + 32 + 8 by omega) $$ L8
    ihave S16 := stk_join n (sp.toNat - 48 + 32) 8 8 $$ [S8 L8]
    · iframe S8 L8
    ihave S32 := VecFromElem.stk_addr (show (sp - 16).toNat - 32 = sp.toNat - 48 by omega) $$ S32
    iapply stk_join n (sp.toNat - 48) 32 16
    iframe S32 S16
  isplitl [O0 O4]
  · iexists _, _
    iframe O0 O4
  iunfold rd, sliceRead
  iframe D0 D4 D8 Hb

end L638

end WNear.Binary.SerdePosition
