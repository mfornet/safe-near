import Bridge.Functions.SerdeEnds

/-!
# serde's `next_value_seed` for `ft_balance_of`'s struct: 201 and 205 (M6)

After a key, the map access reads `:` (89) and then the value: `ignore_value` (81) for an unknown
field (201), `ValidAccountId::deserialize` (169) for `account_id` (205). Both get the
`Deserializer` from the map access's first word.

```wat
;; 201 (acc) → err      e := parse_object_colon(*acc) (89); e ≠ 0 → e; else ignore_value(*acc) (81)
;; 205 (out, acc)       e := 89; e ≠ 0 → out := Err(e); else ValidAccountId::deserialize(out, *acc) (169)
```

The value readers are parameters: each spec takes the callee's specification as a hypothesis (in the
style of `ArgsLeaves.f65_of_66`), at the reader's position after the colon. So these hold for the
string layer as it is now (`SerdeAccountId.f169_s`, escape-free) and as the escapes work will
generalize it, and for any proof of 81.

* `f201_of_81`: on the colon, 81's result; otherwise 89's box.
* `f205_of_169`: on the colon, 169's result at `out`; otherwise `Err(box)` at `out`.
-/

namespace WNear.Binary.SerdeValueSeed

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode resEnd costEnd f89_spec)

section L201

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem resEnd_pos {ok : Prop} [Decidable ok] (h : ok) (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr : UInt32) (bs : List UInt8) (k j : Nat) (rs : List Value) :
    resEnd (GF := GF) ok n maxP mlen live F de ptr bs k j rs ⊢
      iprop(⌜rs = [.i32 0]⌝ ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs k) := by
  unfold resEnd; rw [if_pos h]

theorem resEnd_neg {ok : Prop} [Decidable ok] (h : ¬ ok) (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr : UInt32) (bs : List UInt8) (k j : Nat) (rs : List Value) :
    resEnd (GF := GF) ok n maxP mlen live F de ptr bs k j rs ⊢
      iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗ rd n de ptr bs j) := by
  unfold resEnd; rw [if_neg h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`next_value_seed` of an unknown field** (201), from any specification of `ignore_value` (81)
at the reader after the colon: `P81`, `K81`, `Q81`. -/
theorem f201_of_81 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp acc de ptr idx : UInt32) (bs : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hacc : acc.toNat + 4 ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20)
    (P81 : IProp GF) (K81 : Nat) (Q81 : List Value → IProp GF) :
    endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗
      MFunSpec cfg lim (d + 1) types[32]! inst mi f81 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs (i + wsLen (bs.drop i) + 1) ∗ P81))
        (fun _ => K81) (fun _ rs => iprop(⌜∃ v : UInt32, rs = [.i32 v]⌝ ∗ Q81 rs)) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f201 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i ∗ P81))
        (fun _ => 40 * cfg.regularOpCost +
          costEnd cfg F 200 (wsLen (bs.drop i)) (i + wsLen (bs.drop i))
            (bs[i + wsLen (bs.drop i)]? = some 0x3A) +
          if bs[i + wsLen (bs.drop i)]? = some 0x3A then K81 else 0)
        (fun _ rs => iprop(n ↦[i32][ acc.toNat ] de ∗
          if bs[i + wsLen (bs.drop i)]? = some 0x3A then Q81 rs
          else iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ P81 ∗
            ∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗
              rd n de ptr bs (i + wsLen (bs.drop i))))) := by
  iintro ⟨#Hv, #F89, #F81, #S81⟩
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, -⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha89 := hm.funcs 89 (by decide)
  have ha81 := hm.funcs 81 (by decide)
  have hn := hm.mem
  have t32 : types[32]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hg, Hs, Hvt, Hh, Hrd, HP81⟩
  subst hargs
  simp only [f201]
  generalize hw : wsLen (bs.drop i) = w
  have key := f89_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt sp de ptr idx
    bs i maxP mlen live F hlen hptr hde hsp hi hr
  rw [hw] at key
  generalize hE : costEnd cfg F 200 w (i + w) (bs[i + w]? = some 0x3A) = E at key ⊢
  generalize hX : (if bs[i + w]? = some 0x3A then K81 else 0) = X
  mstep; mstep
  mstep [Hacc]
  mcall key using [Hg Hs Hvt Hh Hrd]
  · iframe Hg Hs Hvt Hh Hrd
  clear key
  icases HQ with ⟨Hg, Hs, Hvt, HQ⟩
  by_cases hok : bs[i + w]? = some 0x3A
  · rw [if_pos hok] at hX
    subst hX
    ihave HQ := resEnd_pos hok $$ HQ
    icases HQ with ⟨%hrs, Hh, Hrd⟩
    subst hrs
    mstep
    mstep_not_taken with decide
    mstep
    mstep [Hacc]
    mcall S81 using [Hg Hs Hvt Hh Hrd HP81]
    · iframe Hg Hs Hvt Hh Hrd HP81
    icases HQ with ⟨%⟨v, hv⟩, HQ⟩
    subst hv
    mstep
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hacc
    rw [if_pos hok, show List.drop (1 - type.results.length) [Value.i32 v] = [Value.i32 v] by simp [htype]]
    iexact HQ
  · rw [if_neg hok] at hX
    subst hX
    ihave HQ := resEnd_neg hok $$ HQ
    icases HQ with ⟨%p, %⟨hrs, hp⟩, HA, Hrd⟩
    subst hrs
    mstep
    mstep_taken with (simp [Numeric.bool, hp])
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hacc
    rw [if_neg hok]
    iframe Hg Hs Hvt HP81
    iexists p
    iframe HA Hrd
    ipureintro; simp [htype, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`next_value_seed` of `account_id`** (205), from any specification of
`ValidAccountId::deserialize` (169) at the reader after the colon: `P169`, `K169`, `Q169`. -/
theorem f205_of_169 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out acc de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hacc : acc.toNat + 4 ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20)
    (P169 : IProp GF) (K169 : Nat) (Q169 : IProp GF) :
    endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
      MFunSpec cfg lim (d + 1) types[14]! inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs (i + wsLen (bs.drop i) + 1) ∗ P169))
        (fun _ => K169) (fun _ rs => iprop(⌜rs = []⌝ ∗ Q169)) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f205 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ P169))
        (fun _ => 40 * cfg.regularOpCost +
          costEnd cfg F 200 (wsLen (bs.drop i)) (i + wsLen (bs.drop i))
            (bs[i + wsLen (bs.drop i)]? = some 0x3A) +
          if bs[i + wsLen (bs.drop i)]? = some 0x3A then K169 else 0)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          if bs[i + wsLen (bs.drop i)]? = some 0x3A then Q169
          else iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ P169 ∗
            ∃ p : UInt32, ⌜p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗
              n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[wms][ out.toNat + 8 ] (ob.drop 8) ∗
              rd n de ptr bs (i + wsLen (bs.drop i))))) := by
  iintro ⟨#Hv, #F89, #F169, #S169⟩
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, -⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha89 := hm.funcs 89 (by decide)
  have ha169 := hm.funcs 169 (by decide)
  have hn := hm.mem
  have t32 : types[32]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hg, Hs, Hvt, Hh, Ho, Hrd, HP169⟩
  subst hargs
  simp only [f205]
  generalize hw : wsLen (bs.drop i) = w
  have key := f89_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt sp de ptr idx
    bs i maxP mlen live F hlen hptr hde hsp hi hr
  rw [hw] at key
  generalize hE : costEnd cfg F 200 w (i + w) (bs[i + w]? = some 0x3A) = E at key ⊢
  generalize hX : (if bs[i + w]? = some 0x3A then K169 else 0) = X
  mstep; mstep
  mstep [Hacc]
  mcall key using [Hg Hs Hvt Hh Hrd]
  · iframe Hg Hs Hvt Hh Hrd
  clear key
  icases HQ with ⟨Hg, Hs, Hvt, HQ⟩
  by_cases hok : bs[i + w]? = some 0x3A
  · rw [if_pos hok] at hX
    subst hX
    ihave HQ := resEnd_pos hok $$ HQ
    icases HQ with ⟨%hrs, Hh, Hrd⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    mstep; mstep
    mstep [Hacc]
    mcall S169 using [Hg Hs Hvt Hh Ho Hrd HP169]
    · iframe Hg Hs Hvt Hh Ho Hrd HP169
    icases HQ with ⟨%hrs, HQ⟩
    subst hrs
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    isplitr
    · ipureintro; simp [htype]
    iframe Hacc
    rw [if_pos hok]
    iexact HQ
  · rw [if_neg hok] at hX
    subst hX
    ihave HQ := resEnd_neg hok $$ HQ
    icases HQ with ⟨%p, %⟨hrs, hp⟩, HA, Hrd⟩
    subst hrs
    icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
    icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
    mstep; mstep
    mstep_not_taken with (simp [Numeric.bool, hp])
    mstep; mstep
    mstep [O0]
    mstep; mstep
    mstep [O4] with (simp [UInt32.toNat_add]; omega)
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    isplitr
    · ipureintro; simp [htype]
    iframe Hacc
    rw [if_neg hok]
    iframe Hg Hs Hvt HP169
    iexists p
    rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop], show out.toNat + 4 + 4 = out.toNat + 8 by omega]
    iframe HA O0 O4 O8 Hrd
    ipureintro; exact hp

end L201

end WNear.Binary.SerdeValueSeed
