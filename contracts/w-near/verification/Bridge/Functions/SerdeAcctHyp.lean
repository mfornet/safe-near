import Bridge.Functions.SerdeAccountId
import Bridge.Functions.SerdeKeyNoEsc

/-!
# `Hyp169` on an input without escapes (M6)

`SerdeStructArr.Hyp169` asks that `ValidAccountId::deserialize` (169) read every account id the
reader `dv` reads, returning the `String` in a block the heap lends (`strRes`). With `dv` the model's
own reader (`valueAs account`) and an input with no `\` byte, the value at the reader is whitespace, a
`"`, the plain bytes of the account id up to the closing `"` (`keyBody`), and the rest
(`acct_noesc`); 380 accepts it (`ok380`) and the bytes are a valid account id, so
`SerdeAccountId.f169_s` gives the `String` (`hyp169_noesc`).

* The heap needs room for the `String`'s page and, after it, for an error box: `roomS`.
* The cost `K169 cfg bs Fb j` is 169's at the free-list bound `Fb` (the allocator walks the free list).
* `lin169_noesc`: `Lin169` with `a169 = 0`, `b169 = 208` per byte read (`96` per whitespace byte,
  `30 + 100` for 646 and `from_utf8`, `60` for `is_valid_account_id`, `18` for `memcpy`), and the
  constant `x169 cfg Fb`, which holds the allocator's walk (`320` per free cell).
-/

namespace WNear.Binary.SerdeAcctHyp

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeErrBox (roomFor4)
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169 roomS)
open WNear.Binary.ParseStr (plain ok646)
open WNear.Binary.SerdeKeyNoEsc (keyBody key_noesc)
open WNear.Binary.SerdeDeStr (ok380 res380 cost380)
open WNear.Binary.SerdeString (heapS)
open NearInterface.Json WNear.JsonFuel
open WNear.SerdeStructModel (valueAs)
open WNear.Binary.AllocNewCell (cellPages cellPages_toNat cellBytes_toNat)
open WNear.Binary.AllocAlloc (wordsOf)

theorem cellPages_one (size : UInt32) (h : size.toNat ≤ 65000) : (cellPages (wordsOf size) 1).toNat = 1 := by
  have hw : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  rw [cellPages_toNat _ _ (by omega) (by decide), cellBytes_toNat _ _ (by omega) (by decide), hw]
  simp only [UInt32.reduceToNat]
  omega

/-- A value the model reads as a string starts with `"` after the whitespace. -/
theorem valueR_str {bs r : List UInt8} {s : String} (h : valueR bs = some (.str s, r)) :
    ∃ rest, skipWhitespace bs = 0x22 :: rest ∧ stringBody rest [] = some (some s, r) := by
  rw [JsonFuel.valueR_eq] at h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · rename_i rest heq
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s', r'⟩, hs, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    cases s' with
    | none => simp at h1
    | some t =>
      simp only [Value.str.injEq] at h1
      subst h1
      exact ⟨rest, heq, hs⟩
  · split at h <;> simp at h
  · split at h <;> simp at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    simp at h

/-- **An account id on an input without `\`**: at `j`, after the whitespace, a `"`, then the plain
bytes `keyBody bs (j + 1)` (the account id's UTF-8 bytes, valid) and a closing `"`, then `r`. -/
theorem acct_noesc {bs : List UInt8} (hnb : (0x5C : UInt8) ∉ bs) {i : Nat}
    {a : WNear.AccountId} {r : List UInt8} (h : valueAs WNear.account (bs.drop i) = some (a, r))
    (j : Nat) (hj : j = i + wsLen (bs.drop i)) :
    j < bs.length ∧ bs[j]? = some 0x22 ∧
      bs.drop (j + 1) = keyBody bs (j + 1) ++ (bs.drop (j + 1)).dropWhile plain ∧
      (∀ b ∈ keyBody bs (j + 1), plain b = true) ∧
      (∀ x rest, (bs.drop (j + 1)).dropWhile plain = x :: rest → plain x = false ∧ x ≠ 0x5C) ∧
      ok646 (keyBody bs (j + 1)) ((bs.drop (j + 1)).dropWhile plain) ∧
      (bs.drop (j + 1)).dropWhile plain = 0x22 :: r ∧
      a.val.toUTF8.toList = keyBody bs (j + 1) ∧ validAccountIdBytes (keyBody bs (j + 1)) = true := by
  unfold valueAs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, a', hacc, rfl, rfl⟩ := h
  unfold WNear.account at hacc
  simp only [Option.map_eq_some_iff] at hacc
  obtain ⟨na, hna, rfl⟩ := hacc
  cases v with
  | str s =>
    simp only [accountId, string, Option.bind_eq_bind, Option.bind_some] at hna
    split at hna
    · rename_i hval
      simp only [Option.some.injEq] at hna
      subst hna
      obtain ⟨rest, hsk, hsb⟩ := valueR_str hv
      obtain ⟨hb, hrest⟩ := SerdeStructLoop.skip_drop_cons hsk
      rw [← hj] at hb hrest
      subst hrest
      have hjl := SerdeNextKey.getElem_lt hb
      obtain ⟨hsplit, hplain, hstop, hok, htl, hkb⟩ := key_noesc hnb hsb
      refine ⟨hjl, hb, hsplit, hplain, hstop, hok, htl, ?_, ?_⟩
      · exact hkb
      · rw [← hkb]; exact hval
    · simp at hna
  | _ => simp [accountId, string] at hna

/-- 169's cost on an escape-free input, at the free-list bound `Fb`: from the reader's index `j`. -/
def K169 (cfg : WasmConfig) (bs : List UInt8) (Fb j : Nat) : Nat :=
  (400 + AccountIdValid.cost554 (keyBody bs (j + wsLen (bs.drop j) + 1)).length) * cfg.regularOpCost +
    cost380 cfg Fb bs (keyBody bs (j + wsLen (bs.drop j) + 1))
      ((bs.drop (j + wsLen (bs.drop j) + 1)).dropWhile plain) (j + wsLen (bs.drop j)) (wsLen (bs.drop j))

/-- The constant of `Lin169`: 169's fixed cost with the allocator's (`Fb` free cells). -/
def x169 (cfg : WasmConfig) (Fb : Nat) : Nat :=
  (2656 + Fb * 320) * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem cost380_mono (cfg : WasmConfig) {F Fb : Nat} (hF : F ≤ Fb) (bs body tail : List UInt8) (j w : Nat)
    (h : ok380 bs body tail j) : cost380 cfg F bs body tail j w ≤ cost380 cfg Fb bs body tail j w := by
  unfold cost380 SerdeString.cost618 SerdeString.costA AllocWalk.cost310W AllocWalk.walkCost
  rw [if_pos h.1, if_pos h.1, if_pos h, if_pos h]
  unfold ParseStr.cost646
  rw [if_pos h.2, if_pos h.2]
  have := AllocWalk.wc_mono cfg hF
  omega

theorem utf8_len (s : String) : s.utf8ByteSize = s.toUTF8.toList.length := by
  rw [String.toUTF8_eq_toByteArray, ToVec.toList_eq]; simp [String.size_toByteArray]

section Hyp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp169` on an input without `\`**, for the model's reader `valueAs account`, at the cost
`K169 cfg bs Fb`, from `SerdeAccountId.f169_s`, for any persistent `Cd` that holds 169's code. -/
theorem hyp169_noesc (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType) (de ptr idx : UInt32)
    (bs : List UInt8) (maxP : Nat) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hnb : (0x5C : UInt8) ∉ bs) (Fb : Nat) (Cd : IProp GF) [Persistent Cd]
    (hCd : Cd ⊢ SerdeAccountId.code169 n maxP inst mi A) :
    Hyp169 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP (valueAs WNear.account) (K169 cfg bs Fb) Fb Cd := by
  intro d sp out ob j a r mlen F live hd hob hout hsp hj hr hF hdv
  obtain ⟨hjl, hq, hsplit, hplain, hstop, hok, htl, hab, hvalid⟩ := acct_noesc hnb hdv _ rfl
  generalize hJ : j + wsLen (bs.drop j) = j' at *
  generalize hB : keyBody bs (j' + 1) = body at *
  generalize hT : (bs.drop (j' + 1)).dropWhile plain = tail at *
  have h380 : ok380 bs body tail j' := ⟨hjl, hok⟩
  have hbl := congrArg List.length hsplit
  rw [htl] at hbl
  simp only [List.length_drop, List.length_append, List.length_cons] at hbl
  have hv2 : 2 ≤ body.length ∧ body.length ≤ 64 := by
    unfold validAccountIdBytes at hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    exact ⟨hvalid.1.1, hvalid.1.2⟩
  have hbody32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
  have hsz : a.val.utf8ByteSize = body.length := by rw [utf8_len, hab]
  have hne : UInt32.ofNat body.length ≠ 0 := by
    intro e
    have h0 : (UInt32.ofNat body.length).toNat = 0 := by rw [e]; rfl
    omega
  have hrs : 0 < body.length → roomFor mlen maxP (UInt32.ofNat body.length) := by
    intro _
    obtain ⟨h1, h2, h3, h4⟩ := hr.1
    have hc : (AllocNewCell.cellPages (AllocAlloc.wordsOf 20) 4).toNat = 1 := by decide
    have hc1 := cellPages_one (UInt32.ofNat body.length) (by rw [hbody32]; omega)
    unfold roomFor
    rw [hc1]
    rw [hc] at h3 h4
    exact ⟨h1, h2, by omega, by omega⟩
  have hpos : bs.length - r.length = j' + 1 + body.length + 1 := by omega
  have hK : (400 + AccountIdValid.cost554 body.length) * cfg.regularOpCost +
      cost380 cfg F bs body tail j' (wsLen (bs.drop j)) ≤ K169 cfg bs Fb j := by
    unfold K169
    rw [hJ, hB, hT]
    have := cost380_mono cfg hF bs body tail j' (wsLen (bs.drop j)) h380
    omega
  iintro #HC
  ihave #H := hCd $$ HC
  iapply (AllocGen.MFunSpec_cost (K := fun _ => (400 + AccountIdValid.cost554 body.length) * cfg.regularOpCost +
      cost380 cfg F bs body tail j' (wsLen (bs.drop j))) (fun _ => hK))
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ sl : UInt32, ⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      stk n (sp.toNat - 256) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
      n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs j ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[i32][ de.toNat + 12 ] 1 ∗ n ↦[i32][ de.toNat + 16 ] 0 ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 256) 256 ∗
      vt n 1057464 idx ta (A 578) ∗ tbl n de ∗
      ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
        n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
        strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - r.length)))
 ?hP0 ?hQ0)
  case hP0 =>
    intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hh, Ho, Hrd, Ht⟩
    iunfold tbl at Ht
    icases Ht with ⟨⟨%sl, Hsl⟩, He, Hw, T12, T16, Hid⟩
    isplitr []
    · iexists sl
      iframe Hg Hs Hvt Hh Ho Hrd Hsl He Hw T12 T16 Hid
      ipureintro; exact ha
    iempintro
  case hQ0 =>
    intro args rs
    iintro ⟨-, HQ⟩
    iexact HQ
  iapply AllocGen.MFunSpec_exists
  imodintro
  iintro %sl
  have s := SerdeAccountId.f169_s (GF := GF) cfg lim d types[14]! (by rfl) inst mi A n g ta hm hd Cg gt sp out de
    ptr idx sl ob bs body tail j j' maxP mlen live F hob hout hlen hptr hde hsp hj hJ.symm (fun _ => hq) hsplit hplain
    hstop hr.1 hrs (fun _ => hvalid)
  ihave #S := s $$ H
  clear s
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(n ↦[i32][ de.toNat + 12 ] 1 ∗ n ↦[i32][ de.toNat + 16 ] 0 ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
    (P := fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      stk n (sp.toNat - 256) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
      n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs j ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 256) 256 ∗
      vt n 1057464 idx ta (A 578) ∗ (∃ sl', n ↦[i32][ de.toNat + 20 ] sl') ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      res380 n maxP mlen live F out de ptr ob bs body tail j')) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hh, Ho, Hrd, Hsl, He, Hw, T12, T16, Hid⟩
    iframe T12 T16 Hid Hg Hs Hvt Hh Ho Hrd Hsl He Hw
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨⟨T12, T16, Hid⟩, %hrs', Hg, Hs, Hvt, Hsl, He, Hw, Hres⟩
    iunfold res380 at Hres
    rw [if_pos h380]
    icases Hres with ⟨%p, Q0, Q4, Q8, Q12, HS, Hp, Hrd⟩
    iunfold heapS at HS
    rw [if_neg hne]
    icases HS with ⟨%⟨hp0, hpb⟩, %len', %hlen', Hh⟩
    isplitr
    · ipureintro; exact hrs'
    iframe Hg Hs Hvt
    isplitl [Hsl He Hw T12 T16 Hid]
    · iunfold tbl
      iframe Hsl He Hw T12 T16 Hid
    iexists p
    iexists UInt32.ofNat body.length
    rw [hsz, hpos]
    iframe Q0 Q4 Q8 Q12 Hrd
    iunfold strRes
    iexists len'
    iexists max F 1
    rw [hsz, hab, hbody32]
    iframe Hp
    isplitr
    · ipureintro
      refine ⟨hp0, by omega, ?_⟩
      rcases hlen' with rfl | rfl
      · exact hr.1
      · have hc1 := cellPages_one (UInt32.ofNat body.length) (by rw [hbody32]; omega)
        unfold VecFromElem.grownLen
        rw [hc1]
        simpa using hr.2
    isplitr [Hh]
    · iunfold block
      iexists []
      isplitr
      · ipureintro; simp
      iapply VecFromElem.memBytes_nil
    iexact Hh
  iexact S

end Hyp

/-- **`Lin169` for `K169`**: at most `208` per byte the account id's value reads, plus `x169 cfg Fb`. -/
theorem lin169_noesc (cfg : WasmConfig) (bs : List UInt8) (hnb : (0x5C : UInt8) ∉ bs) (Fb : Nat) :
    SerdeCost.Lin169 cfg.regularOpCost (K169 cfg bs Fb) (valueAs WNear.account) bs 0 208 (x169 cfg Fb) := by
  intro j a r hj hdv
  obtain ⟨hjl, hq, hsplit, hplain, hstop, hok, htl, hab, hvalid⟩ := acct_noesc hnb hdv _ rfl
  have hbl := congrArg List.length hsplit
  rw [htl] at hbl
  simp only [List.length_drop, List.length_append, List.length_cons] at hbl
  have hv2 : 2 ≤ (keyBody bs (j + wsLen (bs.drop j) + 1)).length ∧
      (keyBody bs (j + wsLen (bs.drop j) + 1)).length ≤ 64 := by
    unfold validAccountIdBytes at hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    exact ⟨hvalid.1.1, hvalid.1.2⟩
  have h380 : ok380 bs (keyBody bs (j + wsLen (bs.drop j) + 1)) ((bs.drop (j + wsLen (bs.drop j) + 1)).dropWhile plain)
      (j + wsLen (bs.drop j)) := ⟨hjl, hok⟩
  unfold K169 x169
  generalize hB : keyBody bs (j + wsLen (bs.drop j) + 1) = body at *
  generalize hT : (bs.drop (j + wsLen (bs.drop j) + 1)).dropWhile plain = tail at *
  generalize hW : wsLen (bs.drop j) = w at *
  have hbody32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
  unfold cost380 SerdeString.cost618 SerdeString.costA AllocWalk.cost310W AllocWalk.walkCost
  rw [if_pos h380.1, if_pos h380]
  unfold ParseStr.cost646
  rw [if_pos h380.2]
  rw [cellPages_one (UInt32.ofNat body.length) (by rw [hbody32]; omega), hbody32]
  unfold AccountIdValid.cost554 FromUtf8.cost927 MemCpy.cost AllocWalk.wc
  rw [if_neg (by omega)]
  have hread : bs.length - r.length - j = w + body.length + 2 := by omega
  rw [hread]
  generalize cfg.regularOpCost = c
  generalize cfg.linearOpBaseCost = lb
  generalize cfg.linearOpUnitCost = lu
  calc _ = (2656 + 208 * body.length + 96 * w) * c + Fb * 320 * c + lb + lu := by ring
    _ ≤ (2656 + 208 * body.length + 208 * w + 416) * c + Fb * 320 * c + lb + lu := by
        have := Nat.mul_le_mul_right c (show 2656 + 208 * body.length + 96 * w ≤
          2656 + 208 * body.length + 208 * w + 416 by omega)
        omega
    _ = _ := by ring

end WNear.Binary.SerdeAcctHyp
