import Bridge.Functions.ParseEscapeSuccess

/-! # Successful surrogate pairs without a whole-input error reserve -/

namespace WNear.Binary.ParseEscapeSurrogateSuccess

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.ParseEscape
open WNear.Binary.EncodeUtf8 (enc605 enc605_eq)
open NearInterface.Json (hex4 unicodeEscape)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeErrBox (errCode roomFor4)
open WNear.Binary.SerdeEsc (eofCode okPack hexTable)
open WNear.Binary.ScratchGrow (sbuf sgCode capAfter fAfter hlAfter roomRes costExt costApp)

/-- A valid high-surrogate escape has the required second Unicode escape and low surrogate. -/
theorem valid_high_tail (l r : List UInt8) (nv : Nat) (hh : hex4 l = some (nv, r))
    (hnv : 0xD800 ≤ nv ∧ nv < 0xDC00) (hv : (unicodeEscape l).isSome = true) :
    ∃ r2 mv r3, r = 0x5C :: 0x75 :: r2 ∧ hex4 r2 = some (mv, r3) ∧
      0xDC00 ≤ mv ∧ mv < 0xE000 := by
  by_cases hs : ∃ r2, r = 0x5C :: 0x75 :: r2
  · obtain ⟨r2, hs⟩ := hs
    have hue := ue_hi l r r2 nv hh hnv hs
    cases hh2 : hex4 r2 with
    | none => simp [hue, hh2] at hv
    | some p =>
      obtain ⟨mv, r3⟩ := p
      by_cases hm : 0xDC00 ≤ mv ∧ mv < 0xE000
      · exact ⟨r2, mv, r3, hs, hh2, hm⟩
      · simp [hue, hh2, hm] at hv
  · have hue := ue_hi_nobs l r nv hh hnv (fun r2 h => hs ⟨r2, h⟩)
    simp [hue] at hv

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- 649 on a successful high-surrogate pair, with no error-construction reserve. -/
theorem f649_u1_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hvalid : (escDecode (bs.drop j)).isSome = true)
    (hu : ∃ rest, bs.drop j = 0x75 :: rest) (hhi' : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => 2000 * cfg.regularOpCost +
          costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold escCode at Hk'
  icases Hk' with ⟨#HG, #HE, #H651, #H605, -⟩
  ihave #HE' := HE
  iunfold eofCode at HE'
  icases HE' with ⟨#HErr, #H637, -, -, #H655, #H653⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #H613, #H614⟩
  ihave #HErr' := HErr
  iunfold errCode at HErr'
  icases HErr' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have ha651 := hm.funcs 651 (by decide)
  have ha614 := hm.funcs 614 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha605 := hm.funcs 605 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hrd, S0, S4, S8, Hsb, Ht⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
  generalize hX : costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))) = X
  icases sbuf_split $$ Hsb with ⟨Hinv, Hw⟩
  generalize hL : (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) = L
  simp only [f649]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  icases stk_split n ((s - 32).toNat - 112) 16 96 $$ Lo with ⟨L16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 112 + 16 = (s - 32).toNat - 96 by omega) $$ Lo
  have hjl : j < bs.length := by
    by_contra h
    have hnone : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    simp [hnone, escDecode] at hvalid
  mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
    hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 32) de ptr bs j hjl (by omega) hptr hde)
    using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  have hb := okPack_bit de bs[j]
  mcredits (1800 * cfg.regularOpCost + (X + R))
  mstep; mstep; mstep; mstep; mstep
  iterate 11 mstep
  iterate 6 mstep
  rw [okPack_byte]
  obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
  have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
  rw [hx]
  mstep; mstep; mstep
  have hx117 : x = 117 := by obtain ⟨r, hr⟩ := hu; rw [hdrop] at hr; simp at hr; exact hr.1
  subst hx117
  have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((117 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 10 := by
    rw [tab1]; decide
  iapply FromUtf8Gen.mwpi_br_table_k hk
  isplitr
  · ipureintro; rfl
  clear hk
  mctrl_norm; repeat mpay
  have hhValid : (hex4 (bs.drop (j + 1))).isSome = true := by
    cases hh : hex4 (bs.drop (j + 1)) with
    | none =>
      have hd : escDecode (bs.drop j) = none := by rw [hdrop]; simp [escDecode, unicodeEscape, hh]
      simpa [hd] using hvalid
    | some pr => rfl
  have key := SerdeEscSuccess.f653_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
    (by omega) Cg gt (s - 32) de ptr idx bs (j + 1) maxP hl L F hde (by omega) (by omega) hptr (by omega) hhValid
  ihave #S653 := key $$ HE
  repeat mstep
  mcall S653 using [Hg Lo Hvt Hinv Hrd Ht]
  · iframe Hg Lo Hvt Hinv Hrd Ht
  icases HQ with ⟨Hg, Lo, Hvt, Ht, HQ⟩
  mcredits (1400 * cfg.regularOpCost + (X + R))
  cases hh : hex4 (bs.drop (j + 1)) with
  | none => exfalso; simpa [hh] using hhValid
  | some pr =>
    obtain ⟨nv, r1⟩ := pr
    simp only [SerdeEsc.res653, hh]
    icases HQ with ⟨%hrs, Hinv, Hrd⟩
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
    obtain ⟨r2, mv, r3, hshape, hh2, hmv1⟩ := valid_high_tail _ _ _ hh hnv1 huv
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
    mcredits (1300 * cfg.regularOpCost + (X + R))
    mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
      hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 32) de ptr bs (j + 1 + 4) hj5
      (by omega) hptr hde) using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mcredits (1150 * cfg.regularOpCost + (X + R))
    rw [hb1]
    have hb := okPack_bit de 92
    repeat mstep
    rw [okPack_ff00, t5c, if_pos rfl]
    repeat mstep
    mcredits (1050 * cfg.regularOpCost + (X + R))
    mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
      hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 32) de ptr bs (j + 1 + 4 + 1) hj6
      (by omega) hptr hde) using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mcredits (900 * cfg.regularOpCost + (X + R))
    rw [hb2]
    have hb := okPack_bit de 117
    repeat mstep
    rw [okPack_ff00, t75, if_pos rfl]
    repeat mstep
    have key2 := SerdeEscSuccess.f653_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
      (by omega) Cg gt (s - 32) de ptr idx bs (j + 1 + 4 + 1 + 1) maxP hl L F hde (by omega)
      (by omega) hptr (by omega) (by simp [hh2])
    ihave #S653b := key2 $$ HE
    mcredits (850 * cfg.regularOpCost + (X + R))
    mcall S653b using [Hg Lo Hvt Hinv Hrd Ht]
    · iframe Hg Lo Hvt Hinv Hrd Ht
    icases HQ with ⟨Hg, Lo, Hvt, Ht, HQ⟩
    mcredits (500 * cfg.regularOpCost + (X + R))
    simp only [SerdeEsc.res653, hh2]
    icases HQ with ⟨%hrs, Hinv, Hrd⟩
    subst hrs
    have hb := hexPack_low mv hmv'
    repeat mstep
    rw [hexPack_val mv hmv']
    repeat mstep
    rw [mask10 mv hmv', eqc _ _ (by omega), if_pos (by rw [hmlo]; rfl)]
    have hue := ue_hi _ _ _ _ hh hnv1 hshape
    have hcp : (nv' - 55296) * 1024 + (mv - 56320) + 65536 < 0x110000 := by omega
    have hd : escDecode (bs.drop j) = some (enc605 ((nv' - 55296) * 1024 + (mv - 56320) + 65536),
        (j + 1 + 4 + 1 + 1 + 4) - j) := by
      rw [hdrop]
      simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
        show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
        show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
        show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
      rw [hue, hh2]
      simp only [Option.bind_some]
      rw [if_pos hmv1]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [show 0x10000 + (nv' - 0xD800) * 0x400 + (mv - 0xDC00) =
          (nv' - 55296) * 1024 + (mv - 56320) + 65536 by omega]
        exact (enc605_eq _ (by simp [Nat.isValidChar]; omega)).symm
      · simp; omega
    have hdH : FromUtf8Gen.Hide (escDecode (bs.drop j) = some (enc605 ((nv' - 55296) * 1024 + (mv - 56320) + 65536),
        (j + 1 + 4 + 1 + 1 + 4) - j)) := hd
    clear hue hh hh2 hacc4 hd hcp
    repeat mstep
    rw [sub_k nv' 0xD800 4294912000 (by omega) hnv' rfl]
    repeat mstep
    rw [ne16 _ (by omega)]
    repeat mstep
    rw [sub_k mv 0xDC00 4294910976 (by omega) hmv' rfl]
    repeat mstep
    rw [ne16 _ (by omega)]
    repeat mstep
    rw [raw_eq _ _ (by omega) (by omega)]
    repeat mstep
    generalize hraw : (nv' - 55296) * 1024 + (mv - 56320) = raw
    have hraw1 : raw < 1048576 := by omega
    have hraw2 : 65536 ≤ raw + 65536 ∧ raw + 65536 < 0x110000 := by omega
    rw [hraw] at hdH
    clear hraw hnv1 hmv1 hhi hmlo
    rw [show UInt32.ofNat raw + 65536 = UInt32.ofNat (raw + 65536) by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp <;> omega]
    rw [mask27 _ (by omega) (by omega)]
    iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
    isplitr; · (ipureintro; exact ⟨rfl, by omega, trivial⟩)
    inext; iintro Hc; mstep_post
    rw [if_pos trivial]
    have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat raw) 1048575) = 0 := by
      have h1 : (UInt32.ofNat raw).toNat = raw := by rw [UInt32.toNat_ofNat']; omega
      have h2 : ¬ ((1048575 : UInt32) < UInt32.ofNat raw) := by
        rw [UInt32.lt_iff_toNat_lt, h1]; show ¬ (1048575 < raw); omega
      simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, h2, decide_false]
      rfl
    mstep
    mstep
    mstep
    rw [hgt]
    iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
    isplitr; · (ipureintro; exact ⟨rfl, by omega, trivial⟩)
    inext; iintro Hc; mstep_post
    rw [if_pos trivial]
    have h1 : (UInt32.ofNat (raw + 65536)).toNat = raw + 65536 := by rw [UInt32.toNat_ofNat']; omega
    generalize hcpv : UInt32.ofNat (raw + 65536) = cpv at h1
    have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne cpv 1114112) = 1 := by
      have : cpv ≠ 1114112 := fun e => by
        rw [e] at h1; have : (1114112 : UInt32).toNat = 1114112 := rfl; omega
      have h' : (cpv != 1114112) = true := by simp [this]
      simp only [Numeric.bool, Numeric.irelop32, h', if_true]
    mstep; mstep; mstep
    mstep
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    rw [← hcpv]
    have hd : escDecode (bs.drop j) = some (enc605 (raw + 65536), (j + 1 + 4 + 1 + 1 + 4) - j) := hdH
    have hcp : raw + 65536 < 0x110000 := hraw2.2
    clear hdH h1 hne hcpv
    clear hvalid hu hhi' huv hshape hshape5 hshape6 hrestLen hhValid
    clear key key2
    iclear S653 S653b Hk HE HErr H637 H655 H653 H651 H614 H310c
    repeat mstep
    have hK1 : escK (bs.drop j) = (enc605 (raw + 65536)).length := by simp [escK, hd]
    rw [hK1] at hX hr
    have hkl := EncodeUtf8.enc605_length (raw + 65536)
    have hk4 : (enc605 (raw + 65536)).length ≤ 4 := by rw [hkl]; split_ifs <;> omega
    icases stk_split n (s.toNat - 144 + 112) 8 24 $$ Fr with ⟨F0, F1⟩
    icases stk_split n (s.toNat - 144 + 112 + 8) 8 16 $$ F1 with ⟨OB, F2⟩
    icases stk_split n (s.toNat - 144 + 112 + 8 + 8) 4 12 $$ F2 with ⟨BF, F4⟩
    iunfold stk at OB BF
    icases OB with ⟨%ob, %hob, OB⟩
    icases BF with ⟨%bf, %hbf, BF⟩
    ihave BF := memBytes_addr (show s.toNat - 144 + 112 + 8 + 8 = (s - 32).toNat + 16 by omega) $$ BF
    have hbfne : bf ≠ [] := List.ne_nil_of_length_pos (by rw [hbf]; omega)
    iapply mwpi_cons
    iapply NearLogic.mwpi_store_at'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; rfl
    isplitl [BF]
    · iexact BF
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨by omega, hn, hbf, hbfne⟩
    inext
    iintro Hc BF
    mctrl_norm
    repeat mpay
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    ihave OB := memBytes_addr (show s.toNat - 144 + 112 + 8 = (s - 32 + 8).toNat by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ OB
    ihave BF := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ BF
    mcall (EncodeUtf8.f605_spec cfg lim (d + 1) types[31]! rfl inst mi n hm.mem Cg (s - 32 + 8) (UInt32.ofNat (raw + 65536))
        (s - 32 + 16) ob (bytes32 0) hob (by simp [bytes32]) (by simp; omega)
        (by rw [UInt32.toNat_add, h32]; simp; omega) (by rw [UInt32.toNat_add, h32]; simp; omega)) using [OB BF] with
      (first | rfl | assumption | omega | (simp only [t31, Nat.sub_self, List.drop_zero]; mstep_norm_full; omega))
    · iframe OB BF
      ipureintro; simp only [t31, Nat.sub_self, List.drop_zero]
    icases HQ with ⟨%hrs, O0, O4, BF⟩
    subst hrs
    simp only [t31, Nat.sub_self, List.drop_zero, actSize_i32, actSize_nil]
    norm_num only [Nat.reduceAdd, Nat.reduceDiv]
    mcredits (300 * cfg.regularOpCost + X + R)
    rw [show (UInt32.ofNat (raw + 65536)).toNat = (raw + 65536) by simp; omega]
    ihave O0 := memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ O0
    ihave O4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 12 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ O4
    mstep with (first | rfl | assumption | omega | mlocals)
    mstep with (first | rfl | assumption | omega | mlocals)
    iapply mwpi_cons
    iapply NearLogic.mwpi_load_at'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; rfl
    isplitl [O0]
    · iexact O0
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨by omega, hn, by rfl, by simp [bytes32]⟩
    inext
    iintro Hc O0
    mctrl_norm
    repeat mpay
    mstep_norm_full
    mstep with (first | rfl | assumption | omega | mlocals)
    iapply mwpi_cons
    iapply NearLogic.mwpi_load_at'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; rfl
    isplitl [O4]
    · iexact O4
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨by omega, hn, by rfl, by simp [bytes32]⟩
    inext
    iintro Hc O4
    mctrl_norm
    repeat mpay
    mstep_norm_full
    icases U128From.memBytes_split n (s - 32 + 16).toNat (enc605 (raw + 65536)).length _ (by simp) $$ BF with ⟨B1, B2⟩
    rw [List.take_left' rfl]
    subst hL
    ihave Hsb := sbuf_join $$ [Hinv Hw]
    · iframe Hinv Hw
    ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
    ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
    · iframe L16 Lo
    have hkn : (UInt32.ofNat (enc605 (raw + 65536)).length).toNat = (enc605 (raw + 65536)).length := by simp; omega
    have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
      (s - 32) sc (s - 32 + 16) (UInt32.ofNat (enc605 (raw + 65536)).length) ptrS capS idx maxP hl live F acc (enc605 (raw + 65536))
      (by omega) (by omega) hcap (by omega) hkn.symm (by rw [UInt32.toNat_add, h32, hkn]; simp; omega) hr
    rw [hX] at key
    ihave #S613 := key $$ HG
    mcredits (100 * cfg.regularOpCost + (0 + X + R))
    rw [show 0 + X + R = X + (0 + R) by omega]
    mcall S613 using [Hg Lo Hvt S0 S4 S8 Hsb B1] with
      (first | rfl | assumption | omega | (simp only [t31, Nat.sub_self, List.drop_zero]; mstep_norm_full; omega))
    · iframe Hg Lo Hvt S0 S4 S8 Hsb B1
      ipureintro; simp only [t31, Nat.sub_self, List.drop_zero]
    icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, S0, S4, S8, Hsb, B1⟩
    subst hrs
    iclear S613 H605 H613 HG Hi
    clear key
    simp only [t31, Nat.sub_self, List.drop_zero, actSize_i32, actSize_nil]
    norm_num only [Nat.reduceAdd, Nat.reduceDiv]
    mcredits (30 * cfg.regularOpCost + (0 + R))
    mctrl_norm
    repeat mpay
    iapply mwpi_cons
    iapply NearLogic.mwpi_local_get' (v := .i32 (s - 32))
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨trivial, by omega, by rfl⟩
    inext
    iintro Hc
    mctrl_norm
    repeat mpay
    iapply mwpi_cons
    iapply NearLogic.mwpi_i32_const'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨trivial, by omega, trivial⟩
    inext
    iintro Hc
    mctrl_norm
    repeat mpay
    iapply mwpi_cons
    iapply NearLogic.mwpi_i32_binop' (r := s - 32 + 32)
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨rfl, by omega, rfl⟩
    inext
    iintro Hc
    mctrl_norm
    repeat mpay
    iapply mwpi_cons
    iapply NearLogic.mwpi_global_set'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; rfl
    isplitl [Hg]
    · iexact Hg
    isplitr
    · ipureintro; exact ⟨by omega, hg⟩
    inext
    iintro Hc Hg
    mctrl_norm
    repeat mpay
    rw [show s - 32 + 32 = s by simp]
    iapply NearLogic.mwpi_local_get' (v := .i32 0)
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨trivial, by omega, by rfl⟩
    inext
    iintro Hc
    iapply NearLogic.mfunc_normal_intro'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; simp [htype]
    iintro Hc
    simp only [htype, List.nil_append, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero]
    mcredits R
    iframe Hc Hg Hvt Ht
    simp only [res649, hd, htype, Nat.sub_self, List.drop_zero]
    rw [show j + ((j + 1 + 4 + 1 + 1 + 4) - j) = (j + 1 + 4 + 1 + 1 + 4) by omega, hkn]
    isplitr [Hrd S0 S4 S8 Hsb]
    · ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
      ihave O0 := BorshFT.stkW (b := s.toNat - 144 + 112 + 8) _ (by omega) $$ O0
      ihave O4 := BorshFT.stkW (b := s.toNat - 144 + 112 + 8 + 4) _ (by omega) $$ O4
      ihave OB := stk_join n (s.toNat - 144 + 112 + 8) 4 4 $$ [O0 O4]
      · iframe O0 O4
      ihave B := U128From.memBytes_join n (s - 32 + 16).toNat (enc605 (raw + 65536)).length _ _ rfl $$ [B1 B2]
      · iframe B1 B2
      ihave B := BorshFT.stkB (b := s.toNat - 144 + 112 + 8 + 8) (k := 4) _ (by rw [UInt32.toNat_add, h32]; simp; omega)
        (by simp [bytes32]; omega) $$ B
      ihave F2 := stk_join n (s.toNat - 144 + 112 + 8 + 8) 4 12 $$ [B F4]
      · iframe B F4
      ihave F1 := stk_join n (s.toNat - 144 + 112 + 8) 8 16 $$ [OB F2]
      · iframe OB F2
      ihave Fr := stk_join n (s.toNat - 144 + 112) 8 24 $$ [F0 F1]
      · iframe F0 F1
      iapply stk_join n (s.toNat - 144) 112 32
      iframe Lo Fr
    iframe Hrd
    iexists p, hl'
    iframe S0 S4 S8 Hsb
    ipureintro; exact hhl


end Proof
end WNear.Binary.ParseEscapeSurrogateSuccess
