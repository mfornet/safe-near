import Bridge.Functions.SerdeStructArr
import Bridge.Functions.SerdeStructLoop
import Bridge.Methods.BalanceOfArgs

/-!
# `deserialize_struct` (228) for `ft_balance_of`'s arguments: the object form (M6)

The object form `{ "account_id": "<a>", … }` of the struct, as 228 reads it: `{`, then the derived
`visit_map` loop around `next_key_seed` (193), with the field's value read by `next_value_seed`
(205 → 169) and any other key's by 201 (→ `ignore_value`, 81), then `end_map` (90).

```wat
;; 228 (out, de, …)   ws (339); '{' →
;;   remaining_depth -= 1; eat '{' (333); MapAccess (de, first = 1) at sp+32; seen := None at sp+40
;;   loop: 193 → Ok(None) with seen → exit; Ok(Some(account_id)) (not seen) → 205 into sp+8, seen := v;
;;         Ok(Some(__ignore)) → 201
;;   remaining_depth += 1; end_map (90) → 0; out := Ok(seen)
```

The callees that are not proved yet are hypotheses:

* `Hyp646`: `parse_str` (646) on a key `stringBody` decodes, as `SerdeNextKey.Spec646` (the escape-free
  instance is `SerdeNextKey.f646_key_noesc`), the heap unchanged;
* `SerdeStructArr.Hyp169`: 169 on an account id `dv` reads;
* `Hyp81`: `ignore_value` (81) on a value `ign` skips, the heap unchanged (true when it pushes no
  frame onto the scratch, i.e. on scalars; the scratch's growth from capacity 0 is not covered).

The loop's state is `SerdeStructLoop.loopRes` at the reader's index, and its cost `objCost`.
-/

namespace WNear.Binary.SerdeStructObj

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit)
open WNear.Binary.SerdeNextKey (Spec646 keyQ keyWs fieldOf)
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169)
open NearInterface.Json

/-- The field visitor's test on a decoded key is the model's. -/
theorem key_iff (k : String) : k.toUTF8.toList = WNear.BalanceOfArgs.keyBytes ↔ k = "account_id" := by
  constructor
  · intro h
    have h1 := WNear.BalanceOfArgs.fromUTF8_toUTF8 k
    have h2 := WNear.BalanceOfArgs.fromUTF8_toUTF8 "account_id"
    rw [h] at h1
    rw [show ("account_id" : String).toUTF8.toList = WNear.BalanceOfArgs.keyBytes by decide +kernel] at h2
    rw [h1] at h2
    exact Option.some.inj h2
  · rintro rfl; decide +kernel

section Hyps

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **The hypothesis on 646 for keys**: wherever `stringBody` decodes a key `k` from `q`, leaving
`rest1`, 646 called there (from 193's frame) returns `Ok(&k's bytes)` (`Spec646`), the heap
unchanged, the scratch cleared, and the reader at an index `q'` with `bs.drop q' = rest1`. -/
def Hyp646 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (A : Nat → Nat) (Cg : Nat) (gt : GlobalType) (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (K646 : Nat → Nat) (Cd : IProp GF) : Prop :=
  ∀ (d : Nat) (sp : UInt32) (ob : List UInt8) (q : Nat) (k : String) (rest1 : List UInt8)
    (mlen F : Nat) (live : List (Nat × Nat)),
    d + 16 < lim.maxCallDepth → ob.length = 16 → 176 ≤ sp.toNat → q ≤ bs.length → roomFor4 mlen maxP 20 →
    stringBody (bs.drop q) [] = some (some k, rest1) →
    Cd ⊢ Spec646 cfg lim d inst mi n g Cg gt sp de ptr ob bs q k.toUTF8.toList
      iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width)
      (K646 q)
      iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗
        ∃ q', ⌜bs.drop q' = rest1 ∧ q' ≤ bs.length⌝ ∗ rd n de ptr bs q')

/-- **The hypothesis on 81** (`ignore_value`), in the shape `SerdeValueSeed.f201_of_81` takes: wherever
`ign` skips a value from `j`, leaving `r`, 81 called there returns 0, the heap unchanged, the reader
at `|bs| - |r|`. Its stack is 256 bytes (96 of them given by 201). -/
def Hyp81 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (A : Nat → Nat) (Cg : Nat) (gt : GlobalType) (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (ign : List UInt8 → Option (Unit × List UInt8)) (K81 : Nat → Nat) (Cd : IProp GF) : Prop :=
  ∀ (d : Nat) (sp : UInt32) (j : Nat) (r : List UInt8) (mlen F : Nat) (live : List (Nat × Nat)),
    d + 16 < lim.maxCallDepth → 256 ≤ sp.toNat → j ≤ bs.length → roomFor4 mlen maxP 20 →
    ign (bs.drop j) = some ((), r) →
    Cd ⊢ MFunSpec (GF := GF) cfg lim d types[32]! inst mi f81 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
        vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs j ∗
        iprop(stk n (sp.toNat - 256) 160 ∗ tbl n de)))
      (fun _ => K81 j)
      (fun _ rs => iprop(⌜∃ v : UInt32, rs = [.i32 v]⌝ ∗ iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
        rd n de ptr bs (bs.length - r.length) ∗ stk n (sp.toNat - 256) 160 ∗ tbl n de)))

end Hyps

/-- The cost of 228's object loop from its head at `i` (`first`, fuel `N`): per member, 193 with
646's `K646`, then 205 with 169's `K169` or 201 with 81's `K81`; at the `}`, 193 and the exit. -/
def objCost (c : Nat) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) : Nat → Bool → Nat → Nat
  | N, first, i =>
    if bs[i + wsLen (bs.drop i)]? = some 0x7D then (300 + 96 * wsLen (bs.drop i)) * c
    else match N with
    | 0 => 0
    | n + 1 =>
      match keyQ first bs i with
      | none => 0
      | some q =>
        match stringBody (bs.drop q) [] with
        | some (some k, rest1) =>
          (1200 + 96 * (keyWs first bs i + wsLen (bs.drop (bs.length - rest1.length))) + SerdeKey.cost194) * c +
            K646 q +
          (if k = "account_id" then
            match dv (bs.drop (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1)) with
            | some (_, r3) => K169 (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1) +
                objCost c K646 K169 K81 dv ign bs n false (bs.length - r3.length)
            | none => 0
          else
            match ign (bs.drop (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1)) with
            | some (_, r3) => K81 (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1) +
                objCost c K646 K169 K81 dv ign bs n false (bs.length - r3.length)
            | none => 0)
        | _ => 0

section CostEq

variable (c : Nat) (K646 K169 K81 : Nat → Nat) (dv : List UInt8 → Option (WNear.AccountId × List UInt8))
  (ign : List UInt8 → Option (Unit × List UInt8)) (bs : List UInt8)

theorem objCost_end {N : Nat} {first : Bool} {i : Nat} (hb : bs[i + wsLen (bs.drop i)]? = some 0x7D) :
    objCost c K646 K169 K81 dv ign bs N first i = (300 + 96 * wsLen (bs.drop i)) * c := by
  rw [objCost.eq_def]; simp [hb]

theorem objCost_field {n : Nat} {first : Bool} {i q : Nat} {k : String} {rest1 : List UInt8}
    {a' : WNear.AccountId} {r3 : List UInt8}
    (hb : bs[i + wsLen (bs.drop i)]? ≠ some 0x7D) (hq : keyQ first bs i = some q)
    (hs : stringBody (bs.drop q) [] = some (some k, rest1)) (hk : k = "account_id")
    (hd : dv (bs.drop (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1)) = some (a', r3)) :
    objCost c K646 K169 K81 dv ign bs (n + 1) first i =
      (1200 + 96 * (keyWs first bs i + wsLen (bs.drop (bs.length - rest1.length))) + SerdeKey.cost194) * c +
        K646 q + (K169 (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1) +
        objCost c K646 K169 K81 dv ign bs n false (bs.length - r3.length)) := by
  rw [objCost]; simp only [hb, if_false, hq, hs, hk, if_true, hd]

theorem objCost_ign {n : Nat} {first : Bool} {i q : Nat} {k : String} {rest1 : List UInt8} {r3 : List UInt8}
    (hb : bs[i + wsLen (bs.drop i)]? ≠ some 0x7D) (hq : keyQ first bs i = some q)
    (hs : stringBody (bs.drop q) [] = some (some k, rest1)) (hk : k ≠ "account_id")
    (hd : ign (bs.drop (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1)) = some ((), r3)) :
    objCost c K646 K169 K81 dv ign bs (n + 1) first i =
      (1200 + 96 * (keyWs first bs i + wsLen (bs.drop (bs.length - rest1.length))) + SerdeKey.cost194) * c +
        K646 q + (K81 (bs.length - rest1.length + wsLen (bs.drop (bs.length - rest1.length)) + 1) +
        objCost c K646 K169 K81 dv ign bs n false (bs.length - r3.length)) := by
  rw [objCost]; simp only [hb, if_false, hq, hs, hk, hd]

end CostEq

section Seeds

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- 205's view of 169 (`SerdeValueSeed.f205_of_169`'s hypothesis), from `Hyp169`: 169 at 205's
`sp` (no frame of its own), `out` 228's buffer. -/
theorem spec169_205 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (A : Nat → Nat) (Cg : Nat) (gt : GlobalType) (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (K169 : Nat → Nat) (Fb : Nat) (Cd : IProp GF)
    [Persistent Cd] (h : Hyp169 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Fb Cd)
    (d : Nat) (hd : d + 16 < lim.maxCallDepth) (sp out : UInt32) (ob : List UInt8) (hob : ob.length = 16)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hsp : 256 ≤ sp.toNat) (j : Nat) (a : WNear.AccountId) (r : List UInt8)
    (hj : j ≤ bs.length) (mlen F : Nat) (live : List (Nat × Nat)) (hr : roomFor4 mlen maxP 20)
    (hF : F ≤ Fb) (hdv : dv (bs.drop j) = some (a, r)) :
    Cd ⊢ MFunSpec cfg lim d types[14]! inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs j ∗ iprop(stk n (sp.toNat - 256) 160 ∗ tbl n de)))
        (fun _ => K169 j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 256) 256 ∗
          vt n 1057464 idx ta (A 578) ∗ tbl n de ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - r.length)))) := by
  have s := h d sp out ob j a r mlen F live hd hob hout hsp hj hr hF hdv
  iintro #HC
  ihave #S := s $$ HC
  clear s
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 256) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs j ∗ tbl n de))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 256) 256 ∗
          vt n 1057464 idx ta (A 578) ∗ tbl n de ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - r.length))) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, S96, Hvt, Hh, Ho, Hrd, S160, Ht⟩
    iframe Hg Hvt Hh Ho Hrd Ht
    isplitr
    · ipureintro; exact ha
    ihave S96 := stk_addr (show sp.toNat - 96 = sp.toNat - 256 + 160 by omega) $$ S96
    iapply stk_join n (sp.toNat - 256) 160 96
    iframe S160 S96
  case hQ =>
    intro args rs
    iintro ⟨-, %hrs, H⟩
    isplitr
    · ipureintro; exact hrs
    iexact H
  iexact S

/-- `drop_in_place::<Option<ValidAccountId>>` (77) on `None` (the pointer 0): nothing. -/
theorem f77_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (v : UInt32) (hv : v.toNat + 4 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f77 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] 0))
        (fun _ => 10 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, H0⟩
  subst hargs
  simp only [f77]
  mstep; mstep; mstep [H0]; mstep
  mstep_taken with decide
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe H0

end Seeds

end WNear.Binary.SerdeStructObj
