import Bridge.Functions.AllocTwoWalk

/-!
# `alloc_first_fit` (580) on a two-cell free list (milestone M4)

`f580_two`: the list `[a, b]` without `CAN_MERGE` (`a.next_free = b`, `b.next_free = 0`), the
alignment 1: `post2` (`a` taken whole or split, or `a` unlinked and `b` walked as by
`AllocFirstFit.f580_one`). `f580_merge`: the list `[a, b]` where `a` has `CAN_MERGE` and `b` is
its previous neighbour: `a` merged into `b`, then `b` walked (`post1` on the grown `b`).

Costs: a parameter `Kt` with the bounds the paths need (in `regular_op_cost`s): 308 when the
first cell fits, 400 when the second does, 211 always (`f580_two`); 497 when the merged cell
fits, 283 always (`f580_merge`).
-/

namespace WNear.Binary.AllocTwoWalk

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocLeaves WNear.Binary.AllocFirstFit
set_option maxRecDepth 20000

section F580Two

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- `alloc_first_fit` (580) on the free list `[a, b]` without `CAN_MERGE`, alignment 1. -/
theorem f580_two (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (w al slot pd pv idx a anx anpv b bnx bnpv : UInt32) (alst blst : Bool) (bsa bsb : List UInt8)
    (hal : al.toNat = 1) (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (ha0 : 1 ≤ a.toNat) (hanx4 : anx &&& 3 = 0) (hacnx : a.toNat + 12 ≤ anx.toNat)
    (hanx : anx.toNat + 65536 ≤ 2 ^ 32) (hbsa : bsa.length + 12 + a.toNat = anx.toNat)
    (hb0 : 1 ≤ b.toNat) (hb3 : b &&& 3 = 0) (hbnx4 : bnx &&& 3 = 0) (hbcnx : b.toNat + 12 ≤ bnx.toNat)
    (hbnx : bnx.toNat + 65536 ≤ 2 ^ 32) (hbsb : bsb.length + 12 + b.toNat = bnx.toNat)
    (Kt : Nat) (hK1 : fits w a anx → 308 * cfg.regularOpCost ≤ Kt)
    (hK2 : fits w b bnx → 400 * cfg.regularOpCost ≤ Kt) (hK3 : 211 * cfg.regularOpCost ≤ Kt) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 w, .i32 al, .i32 slot, .i32 pd, .i32 pv]⌝ ∗
          n ↦[i32][ slot.toNat ] a ∗ cellW n a anx anpv b alst bsa pv idx ta a578 ∗
          cellR n b bnx bnpv 0 blst bsb))
        (fun _ => Kt)
        (post2 n w al slot a anx anpv b bnx bnpv alst blst bsa bsb pv idx ta a578) := by
  iintro #Hk
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hs, HA, HB⟩ Hc
  subst hargs
  have hal0 : al ≠ 0 := by intro h; subst h; simp at hal
  have hal' : al.toNat = 2 ^ 0 := hal
  have hane : a ≠ 0 := by intro h; subst h; simp at ha0
  have hbne : b ≠ 0 := by intro h; subst h; simp at hb0
  simp only [f580]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep [Hs]
  mstep
  mstep
  mstep
  rw [flag_zero al hal0]
  iapply mwpi_cons
  mcredits (cfg.regularOpCost + ((Kt - 17 * cfg.regularOpCost) + R))
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg) (R := (Kt - 17 * cfg.regularOpCost) + R) .empty _
    (fun X g => iprop(⌜X = []⌝ ∗
      ((⌜g = ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], inst, mi⟩⌝ ∗
          credits Cg ((Kt - 17 * cfg.regularOpCost) + R) ∗ n ↦[i32][ slot.toNat ] a ∗
          cellW n a anx anpv b alst bsa pv idx ta a578 ∗ cellR n b bnx bnpv 0 blst bsb) ∨
       (∃ m10 m11 m12 m13 : UInt32, ⌜g = ⟨#[.i32 w, .i32 b, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (a + 8), .i32 m10, .i32 m11, .i32 m12, .i32 m13], inst, mi⟩ ∧
            ¬ fits w a anx⌝ ∗
          credits Cg ((Kt - 109 * cfg.regularOpCost) + R) ∗ n ↦[i32][ slot.toNat ] b ∗
          cellW n b bnx bnpv 0 blst bsb pv idx ta a578 ∗ cellR n a anx anpv b alst bsa) ∨
       (∃ m10 m11 m12 m13 : UInt32, ⌜g = ⟨#[.i32 w, .i32 0, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (b + 8), .i32 m10, .i32 m11, .i32 m12, .i32 m13], inst, mi⟩ ∧
            ¬ fits w a anx ∧ ¬ fits w b bnx⌝ ∗
          credits Cg (10 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] 0 ∗
          cellR n a anx anpv b alst bsa ∗ cellR n b bnx bnpv 0 blst bsb ∗
          n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578))))
    rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc
    isplitr; · ipureintro; rfl
    ileft
    iframe Hc Hs HA HB
    ipureintro; rfl
  imodintro
  iintro %X %l ⟨%hX, HI⟩
  subst hX
  icases HI with (⟨%hg, Hc, Hs, HA, HB⟩ | ⟨%m10, %m11, %m12, %m13, %⟨hg, hfa⟩, Hc, Hs, HBw, HAr⟩ |
    ⟨%m10, %m11, %m12, %m13, %⟨hg, hfa, hfb⟩, Hc, Hs, HAr, HBr, Hv, Ht⟩)
  · ---------------------------------------------------------------- at `a`
    rw [hg]
    by_cases hfa : fits w a anx
    · have hK := hK1 hfa
      iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
        hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 308 * cfg.regularOpCost + R)
        w al slot pd pv idx a anx anpv b a 0 0 0 0 0 alst bsa 0 hal' (by omega) hw1 hw2 ha0 hanx4 hb3 hacnx hanx hbsa
        (291 * cfg.regularOpCost) (by rw [if_pos hfa]))
      iframe Hk Hs HA
      isplitl [Hc]; · mcredits (291 * cfg.regularOpCost + (Kt - 308 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %_ %_ %_ %_ %hu
        exfalso
        rcases hu with h | ⟨-, h⟩
        · exact h hfa
        · exact h (aligned_one al a hal)
      isplit
      · iintro %⟨-, hsp, -⟩ Hc Hs HA
        iunfold cellW at HA
        icases HA with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        iapply (exitW cfg lim d _ inst mi n hn Cg R w al slot pd pv a b a (w0 anx alst) 0 _ _ _ _ (by omega))
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe Hs H0 H8
        iintro %g Hc Hs H0 H8
        rw [v_and3m b hb3]
        mstep_post
        rw [htype]
        iframe Hc
        iunfold post2
        iright
        iexists a + 8
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht HB
        ileft
        iframe Hs H0 H8 Hd Hn
        ipureintro; exact ⟨rfl, hfa, hsp⟩
      · iintro %A %l2 %⟨hA1, -, hsp⟩ Hc Hs HS Hv Ht
        have hA80 : a.toNat + 80 ≤ A.toNat := by unfold canSplit at hsp; omega
        ihave HS := split_post n a anx anpv A b alst bsa hA80 $$ HS
        icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
        have eNN : (A - 8).toNat = A.toNat - 8 := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
        have hA8 : UInt32.ofNat (A.toNat - 8) = A - 8 := by
          apply UInt32.toNat_inj.mp; rw [eNN]; have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
        rw [hA8]
        iapply (exitS cfg lim d _ inst mi n hn Cg R w al a l2 pd pv (A - 8) 0 anx _ _ _)
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe HNa
        iintro %g Hc HNa
        rw [show A - 8 + 8 = A by simp]
        mstep_post
        rw [htype]
        iframe Hc
        iunfold post2
        iright
        iexists A
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht HB
        iright
        rw [eNN]
        rw [show A.toNat - (8 + a.toNat + 12) = A.toNat - 8 - a.toNat - 12 by omega]
        iframe Hs H0 H8 Hd HNa HNb HN4r Hn
        ipureintro; exact ⟨hA1, hfa, hsp⟩
    · iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
        hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 109 * cfg.regularOpCost + R)
        w al slot pd pv idx a anx anpv b a 0 0 0 0 0 alst bsa 0 hal' (by omega) hw1 hw2 ha0 hanx4 hb3 hacnx hanx hbsa
        (92 * cfg.regularOpCost) (by rw [if_neg hfa]))
      iframe Hk Hs HA
      isplitl [Hc]; · mcredits (92 * cfg.regularOpCost + (Kt - 109 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %m10 %m11 %m12 %m13 %_ Hc Hs HA
        isplitr; · ipureintro; rfl
        iright; ileft
        iexists m10, m11, m12, m13
        isplitr; · ipureintro; exact ⟨rfl, hfa⟩
        iunfold cellW at HA
        icases HA with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        iunfold cellR at HB
        icases HB with ⟨HB0, HB8, HBd, HBn⟩
        iunfold cellW
        iunfold cellR
        iframe Hc Hs HB0 HB8 HBd HBn Hv Ht H0 H8 Hd Hn
      isplit
      · iintro %⟨h, -⟩; exact absurd h hfa
      · iintro %_ %_ %⟨-, h, -⟩; exact absurd h hfa
  · ---------------------------------------------------------------- at `b`, `a` unlinked
    rw [hg]
    by_cases hfb : fits w b bnx
    · have hK := hK2 hfb
      iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
        hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 400 * cfg.regularOpCost + R)
        w al slot pd pv idx b bnx bnpv 0 b (a + 8) m10 m11 m12 m13 blst bsb 0 hal' (by omega) hw1 hw2 hb0 hbnx4
        (by decide) hbcnx hbnx hbsb (291 * cfg.regularOpCost) (by rw [if_pos hfb]))
      iframe Hk Hs HBw
      isplitl [Hc]; · mcredits (291 * cfg.regularOpCost + (Kt - 400 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %_ %_ %_ %_ %hu
        exfalso
        rcases hu with h | ⟨-, h⟩
        · exact h hfb
        · exact h (aligned_one al b hal)
      isplit
      · iintro %⟨-, hsp, -⟩ Hc Hs HB
        iunfold cellW at HB
        icases HB with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        iapply (exitW cfg lim d _ inst mi n hn Cg R w al slot pd pv b 0 b (w0 bnx blst) 0 _ _ _ _ (by omega))
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe Hs H0 H8
        iintro %g Hc Hs H0 H8
        rw [show (0 : UInt32) &&& 4294967292 = 0 by decide]
        mstep_post
        rw [htype]
        iframe Hc
        iunfold post2
        ileft
        isplitr; · ipureintro; exact hfa
        iframe HAr
        iunfold post1
        iexists b + 8
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht
        iright; ileft
        iframe Hs H0 H8 Hd Hn
        ipureintro; exact ⟨rfl, hfb, hsp, aligned_one al b hal⟩
      · iintro %A %l2 %⟨hA1, -, hsp⟩ Hc Hs HS Hv Ht
        have hA80 : b.toNat + 80 ≤ A.toNat := by unfold canSplit at hsp; omega
        ihave HS := split_post n b bnx bnpv A 0 blst bsb hA80 $$ HS
        icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
        have eNN : (A - 8).toNat = A.toNat - 8 := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
        have hA8 : UInt32.ofNat (A.toNat - 8) = A - 8 := by
          apply UInt32.toNat_inj.mp; rw [eNN]; have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
        rw [hA8]
        iapply (exitS cfg lim d _ inst mi n hn Cg R w al b l2 pd pv (A - 8) 0 bnx _ _ _)
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe HNa
        iintro %g Hc HNa
        rw [show A - 8 + 8 = A by simp]
        mstep_post
        rw [htype]
        iframe Hc
        iunfold post2
        ileft
        isplitr; · ipureintro; exact hfa
        iframe HAr
        iunfold post1
        iexists A
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht
        iright; iright
        rw [eNN]
        rw [show A.toNat - (8 + b.toNat + 12) = A.toNat - 8 - b.toNat - 12 by omega]
        iframe Hs H0 H8 Hd HNa HNb HN4r Hn
        ipureintro; exact ⟨hA1, hfb, hsp⟩
    · iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
        hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 201 * cfg.regularOpCost + R)
        w al slot pd pv idx b bnx bnpv 0 b (a + 8) m10 m11 m12 m13 blst bsb 0 hal' (by omega) hw1 hw2 hb0 hbnx4
        (by decide) hbcnx hbnx hbsb (92 * cfg.regularOpCost) (by rw [if_neg hfb]))
      iframe Hk Hs HBw
      isplitl [Hc]; · mcredits (92 * cfg.regularOpCost + (Kt - 201 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %m10 %m11 %m12 %m13 %_ Hc Hs HB
        isplitr; · ipureintro; rfl
        iright; iright
        iexists m10, m11, m12, m13
        isplitr; · ipureintro; exact ⟨rfl, hfa, hfb⟩
        iunfold cellW at HB
        icases HB with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        mcredits (10 * cfg.regularOpCost + R)
        iframe Hc Hs HAr Hv Ht
        iunfold cellR
        iframe H0 H8 Hd Hn
      isplit
      · iintro %⟨h, -⟩; exact absurd h hfb
      · iintro %_ %_ %⟨-, h, -⟩; exact absurd h hfb
  · ---------------------------------------------------------------- the list exhausted
    rw [hg]
    iapply (exit0 cfg lim d _ inst mi Cg R w al slot pd pv (b + 8) m10 m11 m12 m13)
    iframe Hc
    iintro %g Hc
    mstep_post
    rw [htype]
    iframe Hc
    iunfold post2
    ileft
    isplitr; · ipureintro; exact hfa
    iframe HAr
    iunfold post1
    iexists 0
    isplitr; · ipureintro; rfl
    iunfold vt
    iframe Hv Ht
    ileft
    iunfold cellR at HBr
    icases HBr with ⟨H0, H8, Hd, Hn⟩
    iframe Hs H0 H8 Hd Hn
    ipureintro; exact ⟨rfl, Or.inl hfb⟩

end F580Two

section F580Merge

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The list `[a, b]` with `CAN_MERGE` on `a`, `b` its previous neighbour: `a`'s header words,
`next_free` and data, `b`'s word 0 (`a`, `b` not last), `next_free` (0) and data, `a`'s next
neighbour's `prev` word. -/
def mergeRes (n : Nat) (a anx b : UInt32) (alst : Bool) (bsa bsb : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 4 ] b ∗ n ↦[i32][ a.toNat + 8 ] (b ||| 1) ∗
    n ↦[wms][ a.toNat + 12 ] bsa ∗ n ↦[i32][ b.toNat ] a ∗ n ↦[i32][ b.toNat + 8 ] 0 ∗
    n ↦[wms][ b.toNat + 12 ] bsb ∗ nextW n anx a alst)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- `alloc_first_fit` (580) on the free list `[a, b]` where `a` has `CAN_MERGE` and `b` is its
previous neighbour, alignment 1: `a` is merged into `b`, then `post1` on the grown `b`. -/
theorem f580_merge (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
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
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (w al slot pd pv idx a b anx : UInt32) (alst : Bool) (bsa bsb : List UInt8)
    (hal : al.toNat = 1) (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (ha3 : a &&& 3 = 0) (hb3 : b &&& 3 = 0) (hnx3 : anx &&& 3 = 0)
    (hb0 : 1 ≤ b.toNat) (hba : b.toNat + 12 ≤ a.toNat) (han : a.toNat + 12 ≤ anx.toNat)
    (hnx : anx.toNat + 65536 ≤ 2 ^ 32)
    (hbsb : bsb.length + 12 + b.toNat = a.toNat) (hbsa : bsa.length + 12 + a.toNat = anx.toNat)
    (Kt : Nat) (hK1 : fits w b anx → 480 * cfg.regularOpCost ≤ Kt) (hK2 : 289 * cfg.regularOpCost ≤ Kt) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574 ∗ code575 inst mi a575 a576 ty575 ty576
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 w, .i32 al, .i32 slot, .i32 pd, .i32 pv]⌝ ∗
          n ↦[i32][ slot.toNat ] a ∗ mergeRes n a anx b alst bsa bsb ∗
          n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578))
        (fun _ => Kt)
        (post1 n w al slot b anx b alst (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) pv idx ta a578) := by
  iintro ⟨#Hk, #Hk5⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hs, HM, Hv, Ht⟩ Hc
  subst hargs
  have hal0 : al ≠ 0 := by intro h; subst h; simp at hal
  have hal' : al.toNat = 2 ^ 0 := hal
  have hane : a ≠ 0 := by intro h; subst h; simp at hba
  have hbs' : (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b).length + 12 + b.toNat = anx.toNat := by
    simp [mergedBs, bytes32]; omega
  simp only [f580]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep [Hs]
  mstep
  mstep
  mstep
  rw [flag_zero al hal0]
  iapply mwpi_cons
  mcredits (cfg.regularOpCost + ((Kt - 17 * cfg.regularOpCost) + R))
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg) (R := (Kt - 17 * cfg.regularOpCost) + R) .empty _
    (fun X g => iprop(⌜X = []⌝ ∗
      ((⌜g = ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], inst, mi⟩⌝ ∗
          credits Cg ((Kt - 17 * cfg.regularOpCost) + R) ∗ n ↦[i32][ slot.toNat ] a ∗
          mergeRes n a anx b alst bsa bsb ∗ n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578) ∨
       (∃ m10 m11 m12 m13 : UInt32, ⌜g = ⟨#[.i32 w, .i32 0, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (b + 8), .i32 m10, .i32 m11, .i32 m12, .i32 m13], inst, mi⟩ ∧
            ¬ fits w b anx⌝ ∗
          credits Cg (10 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] 0 ∗
          cellW n b anx b 0 alst (mergedBs bsb bsa (w0 anx alst &&& 3) 0 b) pv idx ta a578))))
    rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc
    isplitr; · ipureintro; rfl
    ileft
    iframe Hc Hs HM Hv Ht
    ipureintro; rfl
  imodintro
  iintro %X %l ⟨%hX, HI⟩
  subst hX
  icases HI with (⟨%hg, Hc, Hs, HM, Hv, Ht⟩ | ⟨%m10, %m11, %m12, %m13, %⟨hg, hfb⟩, Hc, Hs, HB⟩)
  · rw [hg]
    iunfold mergeRes at HM
    icases HM with ⟨Ha0, Ha4, Ha8, Hda, Hb0, Hb8, Hdb, Hn⟩
    by_cases hfb : fits w b anx
    · have hK := hK1 hfb
      iapply (merge3 cfg lim d _ _ inst mi n hn a572 a575 a576 a574 a578 ta h572 h575 h576 h574 hta
        ty572 ty575 ty576 ty574 hp572 hr572 hp575 hr575 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg
        (Kt - 479 * cfg.regularOpCost + R) w al slot pd pv idx a b anx 0 0 0 0 0 alst bsa bsb 0 hal' (by omega)
        hw1 hw2 ha3 hb3 hnx3 hb0 hba han hnx hbsb hbsa (462 * cfg.regularOpCost) (by rw [if_pos hfb]))
      iframe Hk Hk5 Hs Ha0 Ha4 Ha8 Hda Hb0 Hb8 Hdb Hn Hv Ht
      isplitl [Hc]; · mcredits (462 * cfg.regularOpCost + (Kt - 479 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %_ %_ %_ %_ %hu
        exfalso
        rcases hu with h | ⟨-, h⟩
        · exact h hfb
        · exact h (aligned_one al b hal)
      isplit
      · iintro %⟨-, hsp, -⟩ Hc Hs HB
        iunfold cellW at HB
        icases HB with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        iapply (exitW cfg lim d _ inst mi n hn Cg R w al slot pd pv b 0 b (w0 anx alst) 0 _ _ _ _ (by omega))
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe Hs H0 H8
        iintro %g Hc Hs H0 H8
        rw [show (0 : UInt32) &&& 4294967292 = 0 by decide]
        mstep_post
        rw [htype]
        iframe Hc
        iunfold post1
        iexists b + 8
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht
        iright; ileft
        iframe Hs H0 H8 Hd Hn
        ipureintro; exact ⟨rfl, hfb, hsp, aligned_one al b hal⟩
      · iintro %A %l2 %⟨hA1, -, hsp⟩ Hc Hs HS Hv Ht
        have hA80 : b.toNat + 80 ≤ A.toNat := by unfold canSplit at hsp; omega
        ihave HS := split_post n b anx b A 0 alst _ hA80 $$ HS
        icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
        have eNN : (A - 8).toNat = A.toNat - 8 := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
        have hA8 : UInt32.ofNat (A.toNat - 8) = A - 8 := by
          apply UInt32.toNat_inj.mp; rw [eNN]; have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
        rw [hA8]
        iapply (exitS cfg lim d _ inst mi n hn Cg R w al b l2 pd pv (A - 8) 0 anx _ _ _)
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe HNa
        iintro %g Hc HNa
        rw [show A - 8 + 8 = A by simp]
        mstep_post
        rw [htype]
        iframe Hc
        iunfold post1
        iexists A
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht
        iright; iright
        rw [eNN]
        rw [show A.toNat - (8 + b.toNat + 12) = A.toNat - 8 - b.toNat - 12 by omega]
        iframe Hs H0 H8 Hd HNa HNb HN4r Hn
        ipureintro; exact ⟨hA1, hfb, hsp⟩
    · iapply (merge3 cfg lim d _ _ inst mi n hn a572 a575 a576 a574 a578 ta h572 h575 h576 h574 hta
        ty572 ty575 ty576 ty574 hp572 hr572 hp575 hr575 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg
        (Kt - 279 * cfg.regularOpCost + R) w al slot pd pv idx a b anx 0 0 0 0 0 alst bsa bsb 0 hal' (by omega)
        hw1 hw2 ha3 hb3 hnx3 hb0 hba han hnx hbsb hbsa (262 * cfg.regularOpCost) (by rw [if_neg hfb]))
      iframe Hk Hk5 Hs Ha0 Ha4 Ha8 Hda Hb0 Hb8 Hdb Hn Hv Ht
      isplitl [Hc]; · mcredits (262 * cfg.regularOpCost + (Kt - 279 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %m10 %m11 %m12 %m13 %_ Hc Hs HB
        isplitr; · ipureintro; rfl
        iright
        iexists m10, m11, m12, m13
        isplitr; · ipureintro; exact ⟨rfl, hfb⟩
        mcredits (10 * cfg.regularOpCost + R)
        iframe Hc Hs HB
      isplit
      · iintro %⟨h, -⟩; exact absurd h hfb
      · iintro %_ %_ %⟨-, h, -⟩; exact absurd h hfb
  · rw [hg]
    iapply (exit0 cfg lim d _ inst mi Cg R w al slot pd pv (b + 8) m10 m11 m12 m13)
    iframe Hc
    iintro %g Hc
    mstep_post
    rw [htype]
    iframe Hc
    iunfold post1
    iexists 0
    isplitr; · ipureintro; rfl
    iunfold cellW at HB
    icases HB with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
    iunfold vt
    iframe Hv Ht
    ileft
    iframe Hs H0 H8 Hd Hn
    ipureintro; exact ⟨rfl, Or.inl hfb⟩

end F580Merge

section F580Skip

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- `alloc_first_fit` (580) on the free list `[a, b]` (no `CAN_MERGE`) when `a` is too small:
`a` (only its word 0 and `next_free` read) is skipped, then `post1` on `b`. -/
theorem f580_skip (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (w al slot pd pv idx a anx b bnx bnpv : UInt32) (alst blst : Bool) (bsb : List UInt8)
    (hal : al.toNat = 1) (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (ha0 : 1 ≤ a.toNat) (hanx4 : anx &&& 3 = 0) (hacnx : a.toNat + 12 ≤ anx.toNat)
    (hanx : anx.toNat + 65536 ≤ 2 ^ 32) (hfa : ¬ fits w a anx)
    (hb0 : 1 ≤ b.toNat) (hb3 : b &&& 3 = 0) (hbnx4 : bnx &&& 3 = 0) (hbcnx : b.toNat + 12 ≤ bnx.toNat)
    (hbnx : bnx.toNat + 65536 ≤ 2 ^ 32) (hbsb : bsb.length + 12 + b.toNat = bnx.toNat)
    (Kt : Nat) (hK2 : fits w b bnx → 400 * cfg.regularOpCost ≤ Kt) (hK3 : 211 * cfg.regularOpCost ≤ Kt) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 w, .i32 al, .i32 slot, .i32 pd, .i32 pv]⌝ ∗
          n ↦[i32][ slot.toNat ] a ∗ n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 8 ] b ∗
          cellW n b bnx bnpv 0 blst bsb pv idx ta a578))
        (fun _ => Kt)
        (fun args rs => iprop(n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 8 ] b ∗
          post1 n w al slot b bnx bnpv blst bsb pv idx ta a578 args rs)) := by
  iintro #Hk
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hs, Ha0, Ha8, HBw⟩ Hc
  subst hargs
  have hal0 : al ≠ 0 := by intro h; subst h; simp at hal
  have hal' : al.toNat = 2 ^ 0 := hal
  have hane : a ≠ 0 := by intro h; subst h; simp at ha0
  have hbne : b ≠ 0 := by intro h; subst h; simp at hb0
  simp only [f580]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep [Hs]
  mstep
  mstep
  mstep
  rw [flag_zero al hal0]
  iapply mwpi_cons
  mcredits (cfg.regularOpCost + ((Kt - 17 * cfg.regularOpCost) + R))
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg) (R := (Kt - 17 * cfg.regularOpCost) + R) .empty _
    (fun X g => iprop(⌜X = []⌝ ∗
      ((⌜g = ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], inst, mi⟩⌝ ∗
          credits Cg ((Kt - 17 * cfg.regularOpCost) + R) ∗ n ↦[i32][ slot.toNat ] a ∗
          n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 8 ] b ∗ cellW n b bnx bnpv 0 blst bsb pv idx ta a578) ∨
       (⌜g = ⟨#[.i32 w, .i32 b, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (a + 8), .i32 (w <<< 2), .i32 0, .i32 0, .i32 0], inst, mi⟩⌝ ∗
          credits Cg ((Kt - 109 * cfg.regularOpCost) + R) ∗ n ↦[i32][ slot.toNat ] b ∗
          cellW n b bnx bnpv 0 blst bsb pv idx ta a578 ∗ n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 8 ] b) ∨
       (∃ m10 m11 m12 m13 : UInt32, ⌜g = ⟨#[.i32 w, .i32 0, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (b + 8), .i32 m10, .i32 m11, .i32 m12, .i32 m13], inst, mi⟩ ∧
            ¬ fits w b bnx⌝ ∗
          credits Cg (10 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] 0 ∗
          n ↦[i32][ a.toNat ] w0 anx alst ∗ n ↦[i32][ a.toNat + 8 ] b ∗ cellR n b bnx bnpv 0 blst bsb ∗
          n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578))))
    rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc
    isplitr; · ipureintro; rfl
    ileft
    iframe Hc Hs Ha0 Ha8 HBw
    ipureintro; rfl
  imodintro
  iintro %X %l ⟨%hX, HI⟩
  subst hX
  icases HI with (⟨%hg, Hc, Hs, Ha0, Ha8, HBw⟩ | ⟨%hg, Hc, Hs, HBw, Ha0, Ha8⟩ |
    ⟨%m10, %m11, %m12, %m13, %⟨hg, hfb⟩, Hc, Hs, Ha0, Ha8, HBr, Hv, Ht⟩)
  · ---------------------------------------------------------------- at `a`
    rw [hg]
    iunfold code7 at Hk
    icases Hk with ⟨#H572, #H576, -, -, #Hi⟩
    iapply (body3U cfg lim d _ _ inst mi n hn a572 a576 h572 h576 ty572 ty576 hp572 hr572 hp576 hr576 hd Cg
      (Kt - 109 * cfg.regularOpCost + R) w al slot pd pv a anx b a 0 0 0 0 0 alst hw1 hw2 ha0 hanx4 hb3 hacnx hanx hfa)
    iframe H572 H576 Hi Hs Ha0 Ha8
    isplitl [Hc]; · mcredits (92 * cfg.regularOpCost + (Kt - 109 * cfg.regularOpCost + R)); iexact Hc
    iintro Hc Hs Ha0 Ha8
    isplitr; · ipureintro; rfl
    iright; ileft
    isplitr; · ipureintro; rfl
    iframe Hc Hs HBw Ha0 Ha8
  · ---------------------------------------------------------------- at `b`, `a` unlinked
    rw [hg]
    by_cases hfb : fits w b bnx
    · have hK := hK2 hfb
      iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
        hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 400 * cfg.regularOpCost + R)
        w al slot pd pv idx b bnx bnpv 0 b (a + 8) (w <<< 2) 0 0 0 blst bsb 0 hal' (by omega) hw1 hw2 hb0 hbnx4
        (by decide) hbcnx hbnx hbsb (291 * cfg.regularOpCost) (by rw [if_pos hfb]))
      iframe Hk Hs HBw
      isplitl [Hc]; · mcredits (291 * cfg.regularOpCost + (Kt - 400 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %_ %_ %_ %_ %hu
        exfalso
        rcases hu with h | ⟨-, h⟩
        · exact h hfb
        · exact h (aligned_one al b hal)
      isplit
      · iintro %⟨-, hsp, -⟩ Hc Hs HB
        iunfold cellW at HB
        icases HB with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        iapply (exitW cfg lim d _ inst mi n hn Cg R w al slot pd pv b 0 b (w0 bnx blst) 0 _ _ _ _ (by omega))
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe Hs H0 H8
        iintro %g Hc Hs H0 H8
        rw [show (0 : UInt32) &&& 4294967292 = 0 by decide]
        mstep_post
        rw [htype]
        iframe Hc
        iframe Ha0 Ha8
        iunfold post1
        iexists b + 8
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht
        iright; ileft
        iframe Hs H0 H8 Hd Hn
        ipureintro; exact ⟨rfl, hfb, hsp, aligned_one al b hal⟩
      · iintro %A %l2 %⟨hA1, -, hsp⟩ Hc Hs HS Hv Ht
        have hA80 : b.toNat + 80 ≤ A.toNat := by unfold canSplit at hsp; omega
        ihave HS := split_post n b bnx bnpv A 0 blst bsb hA80 $$ HS
        icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
        have eNN : (A - 8).toNat = A.toNat - 8 := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
        have hA8 : UInt32.ofNat (A.toNat - 8) = A - 8 := by
          apply UInt32.toNat_inj.mp; rw [eNN]; have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
        rw [hA8]
        iapply (exitS cfg lim d _ inst mi n hn Cg R w al b l2 pd pv (A - 8) 0 bnx _ _ _)
        isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
        iframe HNa
        iintro %g Hc HNa
        rw [show A - 8 + 8 = A by simp]
        mstep_post
        rw [htype]
        iframe Hc
        iframe Ha0 Ha8
        iunfold post1
        iexists A
        isplitr; · ipureintro; rfl
        iunfold vt
        iframe Hv Ht
        iright; iright
        rw [eNN]
        rw [show A.toNat - (8 + b.toNat + 12) = A.toNat - 8 - b.toNat - 12 by omega]
        iframe Hs H0 H8 Hd HNa HNb HN4r Hn
        ipureintro; exact ⟨hA1, hfb, hsp⟩
    · iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
        hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 201 * cfg.regularOpCost + R)
        w al slot pd pv idx b bnx bnpv 0 b (a + 8) (w <<< 2) 0 0 0 blst bsb 0 hal' (by omega) hw1 hw2 hb0 hbnx4
        (by decide) hbcnx hbnx hbsb (92 * cfg.regularOpCost) (by rw [if_neg hfb]))
      iframe Hk Hs HBw
      isplitl [Hc]; · mcredits (92 * cfg.regularOpCost + (Kt - 201 * cfg.regularOpCost + R)); iexact Hc
      iunfold obl3
      isplit
      · iintro %m10 %m11 %m12 %m13 %_ Hc Hs HB
        isplitr; · ipureintro; rfl
        iright; iright
        iexists m10, m11, m12, m13
        isplitr; · ipureintro; exact ⟨rfl, hfb⟩
        iunfold cellW at HB
        icases HB with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
        mcredits (10 * cfg.regularOpCost + R)
        iframe Hc Hs Ha0 Ha8 Hv Ht
        iunfold cellR
        iframe H0 H8 Hd Hn
      isplit
      · iintro %⟨h, -⟩; exact absurd h hfb
      · iintro %_ %_ %⟨-, h, -⟩; exact absurd h hfb
  · ---------------------------------------------------------------- the list exhausted
    rw [hg]
    iapply (exit0 cfg lim d _ inst mi Cg R w al slot pd pv (b + 8) m10 m11 m12 m13)
    iframe Hc
    iintro %g Hc
    mstep_post
    rw [htype]
    iframe Hc Ha0 Ha8
    iunfold post1
    iexists 0
    isplitr; · ipureintro; rfl
    iunfold vt
    iframe Hv Ht
    ileft
    iunfold cellR at HBr
    icases HBr with ⟨H0, H8, Hd, Hn⟩
    iframe Hs H0 H8 Hd Hn
    ipureintro; exact ⟨rfl, Or.inl hfb⟩

end F580Skip

section F580First

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 580's result when the first listed cell `a` (its `next_free` `v`) fits: taken whole (the
slot gets `v`) or split (the slot keeps `a`). -/
def postF (n : Nat) (w al slot a anx anpv v : UInt32) (alst : Bool) (bsa : List UInt8)
    (pv idx : UInt32) (ta a578 : Nat) (_args rs : List Value) : IProp GF :=
  iprop(∃ r : UInt32, ⌜rs = [.i32 r]⌝ ∗ vt n pv idx ta a578 ∗
      ((⌜r = a + 8 ∧ fits w a anx ∧ ¬ canSplit w al a anx⌝ ∗
          n ↦[i32][ slot.toNat ] v ∗ n ↦[i32][ a.toNat ] (w0 anx alst ||| 1) ∗ n ↦[i32][ a.toNat + 8 ] v ∗
          n ↦[wms][ a.toNat + 12 ] bsa ∗ nextW n anx anpv alst) ∨
       (⌜r.toNat = aN anx w al ∧ fits w a anx ∧ canSplit w al a anx⌝ ∗
          n ↦[i32][ slot.toNat ] a ∗ n ↦[i32][ a.toNat ] (r - 8) ∗ n ↦[i32][ a.toNat + 8 ] v ∗
          n ↦[wms][ a.toNat + 12 ] bsa.take (r.toNat - 8 - a.toNat - 12) ∗
          n ↦[i32][ r.toNat - 8 ] (w0 anx alst ||| 1) ∗ n ↦[i32][ r.toNat - 4 ] a ∗
          (∃ bs' : List UInt8, ⌜bs'.length = anx.toNat - r.toNat⌝ ∗ n ↦[wms][ r.toNat ] bs') ∗
          nextW n anx (anpv &&& 3 ||| (r - 8)) alst)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- `alloc_first_fit` (580) when the first listed cell `a` fits (alignment 1): only `a` is
walked, whatever follows it in the list (its `next_free` `v`). -/
theorem f580_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (w al slot pd pv idx a anx anpv b : UInt32) (alst : Bool) (bsa : List UInt8)
    (hal : al.toNat = 1) (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (ha0 : 1 ≤ a.toNat) (hanx4 : anx &&& 3 = 0) (hacnx : a.toNat + 12 ≤ anx.toNat)
    (hanx : anx.toNat + 65536 ≤ 2 ^ 32) (hbsa : bsa.length + 12 + a.toNat = anx.toNat)
    (hb3 : b &&& 3 = 0) (hfa : fits w a anx)
    (Kt : Nat) (hK1 : 308 * cfg.regularOpCost ≤ Kt) :
    code7 inst mi a572 a576 a574 a578 ty572 ty576 ty574
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 w, .i32 al, .i32 slot, .i32 pd, .i32 pv]⌝ ∗
          n ↦[i32][ slot.toNat ] a ∗ cellW n a anx anpv b alst bsa pv idx ta a578))
        (fun _ => Kt)
        (postF n w al slot a anx anpv b alst bsa pv idx ta a578) := by
  iintro #Hk
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hs, HA⟩ Hc
  subst hargs
  have hal0 : al ≠ 0 := by intro h; subst h; simp at hal
  have hal' : al.toNat = 2 ^ 0 := hal
  have hane : a ≠ 0 := by intro h; subst h; simp at ha0
  simp only [f580]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep [Hs]
  mstep
  mstep
  mstep
  rw [flag_zero al hal0]
  iapply mwpi_cons
  mcredits (cfg.regularOpCost + ((Kt - 17 * cfg.regularOpCost) + R))
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg) (R := (Kt - 17 * cfg.regularOpCost) + R) .empty _
    (fun X g => iprop(⌜X = [] ∧ g = ⟨#[.i32 w, .i32 a, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], inst, mi⟩⌝ ∗
          credits Cg ((Kt - 17 * cfg.regularOpCost) + R) ∗ n ↦[i32][ slot.toNat ] a ∗
          cellW n a anx anpv b alst bsa pv idx ta a578))
    rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc
    iframe Hc Hs HA
    ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iintro %X %l ⟨%⟨hX, hg⟩, Hc, Hs, HA⟩
  subst hX
  rw [hg]
  have hK := hK1
  iapply (body3 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
    hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg (Kt - 308 * cfg.regularOpCost + R)
    w al slot pd pv idx a anx anpv b a 0 0 0 0 0 alst bsa 0 hal' (by omega) hw1 hw2 ha0 hanx4 hb3 hacnx hanx hbsa
    (291 * cfg.regularOpCost) (by rw [if_pos hfa]))
  iframe Hk Hs HA
  isplitl [Hc]; · mcredits (291 * cfg.regularOpCost + (Kt - 308 * cfg.regularOpCost + R)); iexact Hc
  iunfold obl3
  isplit
  · iintro %_ %_ %_ %_ %hu
    exfalso
    rcases hu with h | ⟨-, h⟩
    · exact h hfa
    · exact h (aligned_one al a hal)
  isplit
  · iintro %⟨-, hsp, -⟩ Hc Hs HA
    iunfold cellW at HA
    icases HA with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
    iapply (exitW cfg lim d _ inst mi n hn Cg R w al slot pd pv a b a (w0 anx alst) 0 _ _ _ _ (by omega))
    isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
    iframe Hs H0 H8
    iintro %g Hc Hs H0 H8
    rw [v_and3m b hb3]
    mstep_post
    rw [htype]
    iframe Hc
    iunfold postF
    iexists a + 8
    isplitr; · ipureintro; rfl
    iunfold vt
    iframe Hv Ht
    ileft
    iframe Hs H0 H8 Hd Hn
    ipureintro; exact ⟨rfl, hfa, hsp⟩
  · iintro %A %l2 %⟨hA1, -, hsp⟩ Hc Hs HS Hv Ht
    have hA80 : a.toNat + 80 ≤ A.toNat := by unfold canSplit at hsp; omega
    ihave HS := split_post n a anx anpv A b alst bsa hA80 $$ HS
    icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
    have eNN : (A - 8).toNat = A.toNat - 8 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
    have hA8 : UInt32.ofNat (A.toNat - 8) = A - 8 := by
      apply UInt32.toNat_inj.mp; rw [eNN]; have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
    rw [hA8]
    iapply (exitS cfg lim d _ inst mi n hn Cg R w al a l2 pd pv (A - 8) 0 anx _ _ _)
    isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
    iframe HNa
    iintro %g Hc HNa
    rw [show A - 8 + 8 = A by simp]
    mstep_post
    rw [htype]
    iframe Hc
    iunfold postF
    iexists A
    isplitr; · ipureintro; rfl
    iunfold vt
    iframe Hv Ht
    iright
    rw [eNN]
    rw [show A.toNat - (8 + a.toNat + 12) = A.toNat - 8 - a.toNat - 12 by omega]
    iframe Hs H0 H8 Hd HNa HNb HN4r Hn
    ipureintro; exact ⟨hA1, hfa, hsp⟩

end F580First

end WNear.Binary.AllocTwoWalk
