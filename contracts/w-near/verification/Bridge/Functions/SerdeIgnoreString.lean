import Bridge.Functions.SerdeIgnoreEscape
import Bridge.Functions.SerdeIgnStr
import Bridge.Functions.SerdeKeyNoEsc
import Bridge.Functions.StrSuccessCostBound

/-! # Successful ignored strings, including escapes and invalid raw UTF-8 -/

namespace WNear.Binary.SerdeIgnoreString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (plain escTable esc_at escTable_length strRun)
open WNear.Binary.SerdeIgnStr (fr650 inv650 inv650_intro)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.ParseEscape (escDecode)

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

/-- A syntactically valid ignored string supplies decoded bytes even when UTF-8 decoding fails. -/
theorem strRun_of_stringBody (l : List UInt8) (s : Option String) (rest : List UInt8)
    (hs : NearInterface.Json.stringBody l [] = some (s, rest)) :
    ∃ bytes, strRun l [] = .ok bytes rest := by
  have hm := ParseStr.strRun_model l []
  simp only [List.reverse_nil] at hm
  rw [hs] at hm
  cases hr : strRun l [] with
  | eof | ctrl | badEsc => simp [hr] at hm
  | ok bytes r =>
    simp only [hr, Option.some.injEq, Prod.mk.injEq] at hm
    exact ⟨bytes, by simpa only [hm.2] using hr⟩

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The outer escape loop retains the modeled remaining string, not its UTF-8 validity. -/
def outer (n inst : Nat) (mi : ModuleInst) (Cg c R : Nat) (gt : GlobalType) (g : Nat)
    (sp de ptr : UInt32) (bs bytes rest : List UInt8) (i : Nat) : List Value → Frame → IProp GF :=
  fun X fr => iprop(∃ (j : Nat) (acc : List UInt8) (a2 a3 a4 a5 : UInt32),
    ⌜X = [] ∧ fr = fr650 inst mi de (sp - 16) a2 a3 a4 a5 ∧ i ≤ j ∧ j ≤ bs.length ∧
      strRun (bs.drop j) acc = .ok bytes rest⌝ ∗
    credits Cg ((100 + 300 * (bs.length - rest.length - j)) * c + R) ∗
    n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
    n ↦[i32][ de.toNat + 8 ] UInt32.ofNat j ∗ n ↦[wms][ ptr.toNat ] bs ∗
    g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n (sp.toNat - 128) 128)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The actual string skip returns at the accepted quote without allocating or validating UTF-8. -/
theorem f650_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs bytes rest : List UInt8) (i : Nat)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hsp : 128 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hok : strRun (bs.drop i) [] = .ok bytes rest) :
    SerdeIgnoreEscape.code inst mi A ∗ A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f650 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 128) 128 ∗
          rd n de ptr bs i ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (120 + 300 * (bs.length - rest.length - i)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 128) 128 ∗
          rd n de ptr bs (bs.length - rest.length) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable)) := by
  iintro ⟨#HC, #F652⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold SerdeIgnoreEscape.code at HC
    icases HC with ⟨#Hi, -⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha652 := hm.funcs 652 (by decide)
  have t32 : types[32]!.params.length = 1 := rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hg, H128, Hrd, He, Hhex⟩
  subst ha
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  simp only [f650, Nat.add_mul, Nat.sub_sub]
  generalize hW : 300 * (bs.length - (rest.length + i)) * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mcredits (cfg.regularOpCost + (100 * cfg.regularOpCost + W + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg)
    (R := 100 * cfg.regularOpCost + W + R)
    (I := outer n inst mi Cg cfg.regularOpCost R gt g sp de ptr bs bytes rest i) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold outer at HI
    icases HI with ⟨%j, %acc, %a2, %a3, %a4, %a5, %⟨hX, hfr, hij, hj, hrun⟩, Hc, He, Hhex, D0, D4, D8, Hb, Hg, H128⟩
    subst hX
    rw [hfr]
    simp only [fr650]
    clear hfr
    simp only [Nat.add_mul, Nat.sub_sub]
    generalize hV : 300 * (bs.length - (rest.length + j)) * cfg.regularOpCost = V
    have hsuf := (ParseStrSuccess.costRun_linear_work cfg 0 0 acc (bs.drop j) bytes rest bs.length hrun).1
    simp only [List.length_drop] at hsuf
    have hsplit : bs.drop j = (bs.drop j).takeWhile plain ++ (bs.drop j).dropWhile plain := List.takeWhile_append_dropWhile.symm
    cases htail : (bs.drop j).dropWhile plain with
    | nil => rw [ParseStr.strRun_nil _ _ htail] at hrun; cases hrun
    | cons b tail =>
      rw [htail] at hsplit
      generalize hbody : (bs.drop j).takeWhile plain = body at hsplit
      have hplain : ∀ b ∈ body, plain b = true := by rw [← hbody]; exact ParseStr.takeWhile_plain _
      have hbl := congrArg List.length hsplit
      simp only [List.length_drop, List.length_append, List.length_cons] at hbl
      have hil : j + body.length + 1 ≤ bs.length := by omega
      have hstop : plain b = false := SerdeKeyNoEsc.dropWhile_head htail
      generalize hJ : j + body.length = stop
      have hrest : tail = bs.drop (stop + 1) := by
        have heq : List.drop (body.length + 1) (bs.drop j) = tail := by rw [hsplit]; simp
        simpa [List.drop_drop, ← Nat.add_assoc, hJ] using heq.symm
      have hrem : stop < bs.length - rest.length := by
        have hr := hrun
        rw [ParseStr.strRun_cons _ _ b tail htail, hbody] at hr
        by_cases hq : b = 0x22
        · simp only [if_pos hq, ParseStr.StrOut.ok.injEq] at hr
          rw [hr.2] at hbl
          omega
        · simp only [if_neg hq] at hr
          split at hr
          · split at hr
            · rename_i out m he
              have hlenEsc := ParseStr.escDecode_len tail out m he
              have hsmall := (ParseStrSuccess.costRun_linear_work cfg 0 0 (acc ++ body ++ out) (tail.drop m) bytes rest bs.length hr).1
              simp only [List.length_drop] at hsmall
              omega
            · cases hr
          · cases hr
      generalize hRi : (300 * (bs.length - rest.length - stop) + 40) * cfg.regularOpCost + R = Ri
      have hVeq : V = 300 * body.length * cfg.regularOpCost +
          300 * (bs.length - rest.length - stop) * cfg.regularOpCost := by
        rw [← hV]
        have he : bs.length - (rest.length + j) = body.length + (bs.length - rest.length - stop) := by omega
        rw [he, Nat.mul_add, Nat.add_mul]
      have hRiexp : Ri = 300 * (bs.length - rest.length - stop) * cfg.regularOpCost + 40 * cfg.regularOpCost + R := by
        rw [← hRi, Nat.add_mul]
      have hPlain : 21 * body.length * cfg.regularOpCost ≤ 300 * body.length * cfg.regularOpCost :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 21 ≤ 300 by decide))
      mstep; mstep [D8]; mstep; mstep; mstep [D0]; mstep; mstep; mstep [D4]; mstep
      mstep
      mcredits (cfg.regularOpCost + (21 * body.length * cfg.regularOpCost + 38 * cfg.regularOpCost + Ri))
      iapply mwpi_cons
      iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 21 * body.length * cfg.regularOpCost + 38 * cfg.regularOpCost + Ri)
        (I := inv650 n inst mi Cg cfg.regularOpCost 38 Ri de (sp - 16) ptr (UInt32.ofNat bs.length) j body.length
          iprop(n ↦[wms][ 1062392 ] escTable ∗ n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
            n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
            stk n (sp.toNat - 128) 128 ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable)) _ _ rfl
      isplitr
      · imodintro
        iintro %X %l HI
        iunfold inv650 at HI
        icases HI with ⟨%k, %l5, %⟨hX, hfr, hik, hkm⟩, Hc, D8, HP⟩
        subst hX
        rw [hfr]
        simp only [fr650]
        clear hfr
        icases HP with ⟨He, D0, D4, Hb, Hg, H128, Hhex⟩
        have hkl : k < bs.length := by omega
        have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat k) (UInt32.ofNat bs.length)) = 0 := by
          have hu : (UInt32.ofNat k).toNat = k := by simp; omega
          have hv : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
          generalize UInt32.ofNat k = u at hu ⊢
          generalize UInt32.ofNat bs.length = v at hv ⊢
          simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
        have hbk : bs[k]? = (body ++ b :: tail)[k - j]? := by
          rw [← hsplit, List.getElem?_drop]; congr 1; omega
        ihave Hb := MemCpy.memBytes_pick n ptr.toNat k bs hkl $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
        rw [hxk]
        rw [List.getElem?_eq_getElem hkl, hxk] at hbk
        have es : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
        have hx8 : x.toNat < 256 := x.toNat_lt
        by_cases hkm' : k < j + body.length
        · have hxb : plain x = true := by
            rw [List.getElem?_append_left (by omega)] at hbk
            exact hplain x (List.mem_of_getElem? hbk.symm)
          rw [show 21 * (j + body.length - k) * cfg.regularOpCost + 38 * cfg.regularOpCost + Ri =
            21 * cfg.regularOpCost + (21 * (j + body.length - (k + 1)) * cfg.regularOpCost + 38 * cfg.regularOpCost + Ri) by
              rw [show j + body.length - k = (j + body.length - (k + 1)) + 1 by omega]; simp only [Nat.mul_add, Nat.add_mul]; omega]
          generalize hZ : 21 * (j + body.length - (k + 1)) * cfg.regularOpCost = Z
          mstep; mstep; mstep
          brn hge
          clear hge
          mstep; mstep; mstep; mstep
          mstep [Bk] with (simp [UInt32.toNat_add]; omega)
          simp only [SerdeKey.load8]
          ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          mstep; mstep; mstep
          ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
          icases He with ⟨E1, Ek, E2⟩
          mstep [Ek] with (simp [UInt32.toNat_add, UInt8.toNat_toUInt32]; omega)
          rw [SerdeKey.load8, esc_at, if_pos hxb]
          ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
          · iframe E1 Ek E2
          rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
          brn rfl
          mstep; mstep; mstep; mstep; mstep
          mstep [D8]
          rw [SerdeRead.ofNat_succ k (by omega)]
          mstep
          simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iapply inv650_intro n inst mi Cg cfg.regularOpCost 38 Ri de (sp - 16) ptr _ j body.length _ (k + 1) _
            (by omega) (by omega)
          iframe D8 He D0 D4 Hb Hg H128 Hhex
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · have hk : k = j + body.length := by omega
          have hx : x = b := by
            rw [List.getElem?_append_right (by omega), show k - j - body.length = 0 by omega] at hbk
            simpa using hbk
          rw [show 21 * (j + body.length - k) * cfg.regularOpCost = 0 by rw [show j + body.length - k = 0 by omega]; simp,
            Nat.zero_add]
          mstep; mstep; mstep
          brn hge
          clear hge
          mstep; mstep; mstep; mstep
          mstep [Bk] with (simp [UInt32.toNat_add]; omega)
          simp only [SerdeKey.load8]
          ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          mstep; mstep; mstep
          ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
          icases He with ⟨E1, Ek, E2⟩
          mstep [Ek] with (simp [UInt32.toNat_add, UInt8.toNat_toUInt32]; omega)
          rw [SerdeKey.load8, esc_at, if_neg (by rw [hx, hstop]; decide)]
          ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
          · iframe E1 Ek E2
          rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
          iapply mwpi_cons
          iapply mwpi_br_if_taken'
          isplitr
          · ipureintro; exact ⟨rfl, by decide⟩
          mctrl_norm
          simp only [Post.mloop]
          mctrl_norm
          repeat mpay
          rw [hx]
          by_cases hbq : b = 0x22
          · subst hbq
            have hr : tail = rest := by
              have hr := hrun
              rw [ParseStr.strRun_cons _ _ 0x22 tail htail, hbody] at hr
              exact (ParseStr.StrOut.ok.inj hr).2
            have hend : k + 1 = bs.length - rest.length := by rw [hr] at hbl; omega
            mstep; mstep; mstep; mstep
            brn (by decide)
            mstep; mstep; mstep; mstep
            brt (by decide)
            mstep; mstep; mstep; mstep
            mstep [D8]
            rw [SerdeRead.ofNat_succ k (by omega)]
            mstep; mstep; mstep
            (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
            mstep; mstep; mstep; mstep [Hg]
            rw [show sp - 16 + 16 = sp by simp]
            repeat mstep
            rw [← hRi]
            isplitl [Hc]
            · iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
            iframe Hg He Hhex H128
            isplitr
            · ipureintro; simp [htype]
            iunfold rd, sliceRead
            rw [← hend]
            iframe D0 D4 D8 Hb
          · have hbslash : b = 0x5C := by
              have hr := hrun
              rw [ParseStr.strRun_cons _ _ b tail htail, if_neg hbq] at hr
              by_contra he
              simp only [if_neg he] at hr
              cases hr
            subst hbslash
            have hr := hrun
            rw [ParseStr.strRun_cons _ _ 0x5C tail htail, hbody] at hr
            simp only [show (0x5C : UInt8) ≠ 0x22 by decide, ite_false, ite_true] at hr
            cases hesc : escDecode tail with
            | none => rw [hesc] at hr; cases hr
            | some eo =>
              obtain ⟨out, m⟩ := eo
              rw [hesc] at hr
              have hmLen := ParseStr.escDecode_len tail out m hesc
              have hnext : strRun (bs.drop (k + 1 + m)) (acc ++ body ++ out) = .ok bytes rest := by
                rw [hrest] at hr
                simpa [List.drop_drop, hk, hJ, Nat.add_assoc] using hr
              have hnextStrict := (ParseStrSuccess.costRun_linear_work cfg 0 0 _ _ _ _ bs.length hnext).1
              simp only [List.length_drop] at hnextStrict
              have hkl : k < bs.length := by omega
              mstep; mstep; mstep; mstep
              brt (by decide)
              mstep; mstep; mstep; mstep; mstep [D8]
              rw [SerdeRead.ofNat_succ k (by omega)]
              have hesc' : escDecode (bs.drop (k + 1)) = some (out, m) := by simpa only [hrest, show stop = k by omega] using hesc
              have key := SerdeIgnoreEscape.f652_success_linear (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
                (by omega) Cg gt (sp - 16) de ptr bs out (k + 1) m hde hlen hptr (by omega) hesc'
              icases stk_split n (sp.toNat - 128) 112 16 $$ H128 with ⟨Lo, Fr⟩
              rw [show sp.toNat - 128 + 112 = sp.toNat - 16 by omega]
              ihave Lo := stk_addr (show sp.toNat - 128 = (sp - 16).toNat - 112 by omega) $$ Lo
              ihave Hrd : rd n de ptr bs (k + 1) $$ [D0 D4 D8 Hb]
              · iunfold rd, sliceRead
                iframe D0 D4 D8 Hb
              have hremain : bs.length - rest.length - stop =
                  (m + 1) + (bs.length - rest.length - (k + 1 + m)) := by omega
              have hcoeff : 200 * (m + 1) + (110 + 300 * (bs.length - rest.length - (k + 1 + m))) + 30 ≤
                  300 * (bs.length - rest.length - stop) + 51 := by omega
              have hpay := Nat.mul_le_mul_right cfg.regularOpCost hcoeff
              simp only [Nat.add_mul, Nat.sub_sub] at hpay
              generalize hNext : 300 * (bs.length - (rest.length + (k + 1 + m))) * cfg.regularOpCost = Next at hpay ⊢
              rw [← hRi]
              simp only [Nat.add_mul, Nat.sub_sub]
              mcredits ((200 * (m + 1)) * cfg.regularOpCost +
                (110 * cfg.regularOpCost + Next + R) + 30 * cfg.regularOpCost)
              mstep
              mcall key using [Hg Lo Hrd Hhex] with (mstep_norm_full; simp only [Nat.add_mul]; omega)
              · iframe Hg Lo Hrd Hhex
              icases HQ with ⟨%hrs, Hg, Lo, Hrd, Hhex⟩
              subst hrs
              simp only [Nat.add_mul, Nat.one_mul]
              mcredits (110 * cfg.regularOpCost + Next + R)
              ihave Lo := stk_addr (show (sp - 16).toNat - 112 = sp.toNat - 128 by omega) $$ Lo
              ihave H128 := stk_join n (sp.toNat - 128) 112 16 $$ [Lo Fr]
              · rw [show sp.toNat - 128 + 112 = sp.toNat - 16 by omega]
                iframe Lo Fr
              iunfold rd, sliceRead at Hrd
              icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
              mstep; mstep
              brt (by decide)
              iunfold outer
              iexists k + 1 + m, acc ++ body ++ out, 0, ptr, UInt32.ofNat bs.length, 0x5C
              isplitr
              · ipureintro; exact ⟨rfl, rfl, by omega, by omega, hnext⟩
              iframe He Hhex D0 D4 D8 Hb Hg H128
              simp only [Nat.add_mul, Nat.sub_sub]
              rw [hNext]
              iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
      · iframe Hc
        inext
        iintro Hc
        iapply inv650_intro n inst mi Cg cfg.regularOpCost 38 Ri de (sp - 16) ptr _ j body.length _ j _
          (by omega) (by omega)
        iframe D8 He D0 D4 Hb Hg H128 Hhex
        simp only [Nat.add_sub_cancel_left]
        iexact Hc
  · iframe Hc
    inext
    iintro Hc
    iunfold outer
    iexists i, [], 0, 0, 0, 0
    simp only [Nat.add_mul, Nat.sub_sub]
    rw [hW]
    iframe Hc He Hhex D0 D4 D8 Hb Hg H128
    ipureintro; exact ⟨trivial, rfl, le_rfl, hi, hok⟩

/-- Successful ignored strings directly from the model, with no UTF-8 validity restriction. -/
theorem f650_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs rest : List UInt8) (s : Option String) (i : Nat)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hsp : 128 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hok : NearInterface.Json.stringBody (bs.drop i) [] = some (s, rest)) :
    SerdeIgnoreEscape.code inst mi A ∗ A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f650 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 128) 128 ∗
          rd n de ptr bs i ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (120 + 300 * (bs.length - rest.length - i)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 128) 128 ∗
          rd n de ptr bs (bs.length - rest.length) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable)) := by
  obtain ⟨bytes, hrun⟩ := strRun_of_stringBody (bs.drop i) s rest hok
  exact f650_success cfg lim d type htype inst mi A n g ta hm hd Cg gt sp de ptr bs bytes rest i
    hlen hptr hde hsp hi hrun

end Proof
end WNear.Binary.SerdeIgnoreString
