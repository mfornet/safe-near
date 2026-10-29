import Bridge.Functions.SerdePosition
import Bridge.Functions.SerdeErrRet

/-!
# Source positions have a nonzero line

The original position contracts hide the line's positivity. Error propagation
needs it: `fix_position` returns an already-positioned error unchanged. These
stronger contracts retain that fact with the original cost and footprint.
-/

namespace WNear.Binary.SerdePositionPositive

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.SerdePosition WNear.Binary.SerdeErrBox
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)

set_option hygiene false in
local macro "brt " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, $h⟩
  mctrl_norm; repeat mpay))

set_option hygiene false in
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def invO (inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (out sp ptr : UInt32) (idx : Nat) (P : IProp GF) :
    List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (j L : Nat) (l1 l2 l7 : UInt32), ⌜X = [] ∧
      g = fr645 inst mi out l1 l2 sp (ptr + UInt32.ofNat j) (ptr + UInt32.ofNat idx) (UInt32.ofNat L) l7 ∧
      j ≤ idx ∧ L ≤ j + 1 ∧ 0 < L⌝ ∗
    credits Cg (50 * (idx - j) * c₀ + E * c₀ + R) ∗ P)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`position_of_index(out, rd, idx)`** (645), `idx ≤ len`: some `(line, column)` at `out`, at most
`cost645 idx`. The stack: 16 bytes, and 609's 16 below. -/
theorem f645_pos (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
          (∃ line col : UInt32, ⌜line ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] line ∗ n ↦[i32][ out.toNat + 4 ] col) ∗
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
    icases HI with ⟨%j, %L, %l1, %l2, %l7, %⟨hX, hfr, hj, hL, hLpos⟩, Hc, HP⟩
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
        ipureintro
        intro he
        have he' := congrArg UInt32.toNat he
        have hbound : L < 2 ^ 32 := by omega
        simp only [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt hbound] at he'
        omega
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
          · ipureintro; exact ⟨rfl, rfl, by omega, by omega, by omega⟩
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
  · ipureintro; exact ⟨rfl, by simp [fr645], Nat.zero_le _, by omega, by omega⟩
  rw [hW]
  iframe Hc Ho Hb S8 D0 D4 Hg S16 P0 P4


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem f638_pos (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
          (∃ line col : UInt32, ⌜line ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] line ∗ n ↦[i32][ out.toNat + 4 ] col) ∗
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
  mcall (f645_pos cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n g hn hg a583 a609 ha583 ha609 (by omega)
    Cg gt (sp - 16) (sp - 16 + 8) de ptr s8 bs i hs8 (by omega) (by omega) hi hlen hptr (by omega))
    using [Hg S32 S8' D0 D4 Hb]
  · iframe Hg S32 S8' D0 D4 Hb
  rw [hK3, show 29 * cfg.regularOpCost + (cost645 i * cfg.regularOpCost + R) -
    (13 * cfg.regularOpCost + cost645 i * cfg.regularOpCost) = 16 * cfg.regularOpCost + R by omega]
  icases HQ with ⟨%hrs, Hg, S32, ⟨%line, %col, %hline, L0, L4⟩, D0, D4, Hb⟩
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
    ipureintro; exact hline
  iunfold rd, sliceRead
  iframe D0 D4 D8 Hb


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem f640_pos (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 a609 a645 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (ha609 : mi.funcAddrs[609]? = some a609)
    (ha645 : mi.funcAddrs[645]? = some a645) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr : UInt32) (ob bs : List UInt8) (i : Nat) (hob : ob.length = 8)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 48 ≤ sp.toNat) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ a609 ↪[wf] FuncInst.wasm types[39]! inst f609 ∗
      a645 ↪[wf] FuncInst.wasm types[31]! inst f645 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f640 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i))
        (fun _ => (20 + cost638 (i + 1)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 48) 48 ∗
          (∃ line col : UInt32, ⌜line ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] line ∗ n ↦[i32][ out.toNat + 4 ] col) ∗
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
  have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat (i + 1))) = 0
      then Value.i32 (UInt32.ofNat bs.length) else Value.i32 (UInt32.ofNat (i + 1))) =
      Value.i32 (UInt32.ofNat (min (i + 1) bs.length)) := by
    by_cases hib : i + 1 < bs.length
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat (i + 1))) ≠ 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      rw [if_neg this, Nat.min_eq_left (by omega)]
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat (i + 1))) = 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      rw [if_pos this, Nat.min_eq_right (by omega)]
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (i + 1)) (UInt32.ofNat i)) = 0 := by
    rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
  generalize hj : min (i + 1) bs.length = j at hsel
  have hjl : j ≤ bs.length := by omega
  have hle := Nat.mul_le_mul_right cfg.regularOpCost
    (show cost645 j ≤ cost645 (i + 1) by unfold cost645; omega)
  simp only [f640, cost638]
  rw [show (20 + (40 + cost645 (i + 1))) * cfg.regularOpCost + R =
    60 * cfg.regularOpCost + (cost645 j * cfg.regularOpCost + ((cost645 (i + 1) * cfg.regularOpCost - cost645 j * cfg.regularOpCost) + R)) by
    simp only [Nat.add_mul]; omega]
  generalize hR' : cost645 (i + 1) * cfg.regularOpCost - cost645 j * cfg.regularOpCost + R = R'
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [D8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep
  rw [SerdeRead.ofNat_succ i (by omega)]
  mstep; mstep; mstep
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro
  exact ⟨rfl, by omega, hov⟩
  inext; iintro Hc; mctrl_norm
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [D4] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply mwpi_select2
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; omega
  inext
  iintro Hc
  rw [hsel]
  clear hsel
  mctrl_norm
  have t31 : types[31]!.params.length = 3 := by rfl
  ihave S32 := VecFromElem.stk_addr (show sp.toNat - 48 = (sp - 16).toNat - 32 by omega) $$ S32
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 48 + 32 + 8 = (sp - 16 + 8).toNat by omega) $$ S8'
  have hK2 : (12 + cost645 (UInt32.ofNat j).toNat) * cfg.regularOpCost = 12 * cfg.regularOpCost + cost645 j * cfg.regularOpCost := by
    rw [show (UInt32.ofNat j).toNat = j by simp; omega, Nat.add_mul]
  have hK3 : (13 + cost645 j) * cfg.regularOpCost = 13 * cfg.regularOpCost + cost645 j * cfg.regularOpCost := Nat.add_mul _ _ _
  mcall (f645_pos cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n g hn hg a583 a609 ha583 ha609 (by omega)
    Cg gt (sp - 16) (sp - 16 + 8) de ptr s8 bs j hs8 (by omega) (by omega) hjl hlen hptr (by omega))
    using [Hg S32 S8' D0 D4 Hb]
  · iframe Hg S32 S8' D0 D4 Hb
  try rw [hK3]
  try rw [hK2]
  generalize cost645 j * cfg.regularOpCost = K1
  mcredits (16 * cfg.regularOpCost + R')
  icases HQ with ⟨%hrs, Hg, S32, ⟨%line, %col, %hline, L0, L4⟩, D0, D4, Hb⟩
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
    ipureintro; exact hline
  iunfold rd, sliceRead
  iframe D0 D4 D8 Hb

end Proof

end WNear.Binary.SerdePositionPositive
