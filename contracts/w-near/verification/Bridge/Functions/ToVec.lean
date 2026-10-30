import Bridge.Functions.ToString
import Binary.Code.Part00
import Mathlib.Tactic.IntervalCases

/-!
# `serde_json::to_vec::<U128>` (96) (milestone M5)

```
96  sp -= 16; Vec::with_capacity(128) at sp (94); *(sp + 12) = sp (the Serializer)
    r = <U128 as Serialize>::serialize(value, sp + 12) (385)
    r = 0 ⇒ out + 4 ← the Vec (12 bytes); tag 0      (the Err path, r ≠ 0, drops the Vec: not taken)
    *out = tag; sp += 16
```

`f96_spec`: on a `u128` `lo + 2^64 hi` at `value`, `Ok` (tag 0) with the `Vec` `(q, 128, k + 2)`
whose first `k + 2` bytes are `"` ++ the decimal digits ++ `"` (`k` digits), from `heapInv … F`
(`F ∈ {1, 2}`, default 1) to `heapInv … (F + 1)` (`to_string`'s buffer freed). The harness's
`toVecU128` asks exactly this (`jsonU128`); `json_bytes` relates its bytes to `decDigits`.
-/

namespace WNear.Binary.ToVec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtDigits (decDigits lut digit)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtSink (grown heapAfter_grown)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr roomFor costAlloc grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecWithCap (okG costAllocF vecCode2 pre373 post373)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.SerializeStr (esc serCode cost383)
open WNear.Binary.ToString (tsCode tsData serIn serOut cost385 f385_u128 hb32 w2)

/-! ## The harness's bytes: `"` ++ `toString n` ++ `"` in UTF-8 is `[34] ++ decDigits n ++ [34]` -/

theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
    rw [ih]
    have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.drop_eq_getElem_cons hi]
    simp [ByteArray.get!, h]
  | case2 i r h =>
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp [List.drop_eq_nil_of_le this]

theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  simp [ByteArray.toList, toList_loop]

theorem digitChar_byte (d : Nat) (h : d < 10) : (Nat.digitChar d).toUInt8 = digit d := by
  interval_cases d <;> rfl

theorem digitChar_lt (d : Nat) (h : d < 10) : (Nat.digitChar d).val ≤ 127 := by
  interval_cases d <;> decide

theorem toDigits_dec (n : Nat) : (Nat.toDigits 10 n).map (fun c => c.toUInt8) = decDigits n ∧
    ∀ c ∈ Nat.toDigits 10 n, c.val ≤ 127 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide), decDigits]
    split
    · simp [digitChar_byte n (by omega), digitChar_lt n (by omega)]
    · obtain ⟨h1, h2⟩ := ih (n / 10) (by omega)
      refine ⟨by simp [h1, digitChar_byte (n % 10) (by omega)], ?_⟩
      intro c hc
      simp at hc
      rcases hc with hc | hc
      · exact h2 c hc
      · subst hc; exact digitChar_lt _ (by omega)

theorem flat_ascii (l : List Char) (h : ∀ c ∈ l, c.val ≤ 127) :
    l.flatMap String.utf8EncodeChar = l.map (fun c => c.toUInt8) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.flatMap_cons, List.map_cons,
      String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.2 (h c (by simp))),
      ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem json_bytes (n : Nat) : ("\"" ++ toString n ++ "\"").toUTF8.toList = [34] ++ decDigits n ++ [34] := by
  obtain ⟨h1, h2⟩ := toDigits_dec n
  have e : toString n = String.ofList (Nat.toDigits 10 n) := rfl
  have q : ("\"" : String) = String.ofList ['"'] := rfl
  rw [e, q, String.toUTF8_eq_toByteArray, String.toByteArray_append, String.toByteArray_append,
    String.toByteArray_ofList, String.toByteArray_ofList, List.utf8Encode, List.utf8Encode,
    flat_ascii _ h2, flat_ascii _ (by decide), toList_eq]
  simp [h1]
  rfl

/-- The length the `Vec` ends with: the digits and the two quotes. -/
theorem len_json (lo hi : UInt64) :
    ((0 : UInt32) + kOf (val lo hi) + 2).toNat = (decDigits (val lo hi)).length + 2 := by
  have h1 := FmtString.kOf_toNat lo hi
  have h2 := FmtString.decDigits_le lo hi
  rw [UInt32.toNat_add, UInt32.toNat_add, h1]
  simp; omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 96 runs (persistent). -/
def tvCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(tsCode n maxP inst mi A ∗ serCode inst mi A ∗ vecCode2 n maxP inst mi A ∗
    A 94 ↪[wf] FuncInst.wasm types[14]! inst f94 ∗ A 385 ↪[wf] FuncInst.wasm types[13]! inst f385)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (tvCode (GF := GF) n maxP inst mi A) := by
  unfold tvCode; infer_instance

/-- The data `to_vec::<U128>` reads (owned, returned): `to_string`'s (`tsData`), the quote and the
digits' `ESCAPE` entries, the digit table. -/
def tvData (n ta : Nat) (ptr0 : UInt32) (a759 a353 : Nat) : IProp GF :=
  iprop(tsData n ta ptr0 a759 a353 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] esc ∗
    n ↦[wms][ 1070974 ] lut)

/-- The cost of `to_vec::<U128>` (96), activation excluded. -/
noncomputable def cost96F (cfg : WasmConfig) (F : Nat) (lo hi : UInt64) : Nat :=
  400 * cfg.regularOpCost + costAllocF cfg F 128 + cost385 cfg F lo hi

/-- `cost96F` on `heapInv … 1` (the same for `F ≤ 2`, `cost96F_le2`). -/
noncomputable def cost96 (cfg : WasmConfig) (lo hi : UInt64) : Nat := cost96F cfg 1 lo hi

theorem cost96F_le2 (cfg : WasmConfig) {F : Nat} (h : F ≤ 2) (lo hi : UInt64) :
    cost96F cfg F lo hi = cost96 cfg lo hi := by
  simp only [cost96, cost96F, cost385, FmtString.cost746, FmtString.cost872, FmtString.cost353,
    FmtString.costGrow, VecWithCap.costAllocF_le2 cfg h, VecWithCap.costAllocF_le2 cfg (show 1 ≤ 2 by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`serde_json::to_vec::<U128>(out, v)`** (96) on the `u128` `lo + 2^64 hi` at `v`: `Ok` (tag 0 at
`out`) with the `Vec` `(q, 128, k + 2)` at `out + 4`, its first `k + 2` bytes the JSON string
`[34] ++ decDigits N ++ [34]` (`json_bytes`: the harness's `jsonU128 N`; `len_json`: the length). -/
theorem f96_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 27 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s out v ptr0 aidx : UInt32) (ob : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hs : 416 ≤ s.toNat) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hv : v.toNat + 16 ≤ 2 ^ 32) (hr1 : roomFor hl maxP 128)
    (hr2 : ∀ hl1, hl1 = hl ∨ hl1 = grownLen hl 128 → roomFor hl1 maxP (newCap 0 (kOf (val lo hi))))
    (F : Nat := 1) (hF : okG F := by decide) :
    tvCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f96 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗
          vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F))
        (fun _ => cost96F cfg F lo hi)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗
          ∃ q : UInt32, ∃ rest : List UInt8, ⌜rest.length = 128 - ((kOf (val lo hi)).toNat + 2)⌝ ∗
            n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] q ∗ n ↦[i32][ out.toNat + 8 ] 128 ∗
            n ↦[i32][ out.toNat + 12 ] (0 + kOf (val lo hi) + 2) ∗
            n ↦[wms][ q.toNat ] (([34] ++ decDigits (val lo hi) ++ [34]) ++ rest) ∗
            ∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) (F + 1))) := by
  iintro #Hk
  iunfold tvCode at Hk
  icases Hk with ⟨#Hts, #Hser, #Hv2, #H94, #H385⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold tsCode at Hts; icases Hts with ⟨-, -, -, -, -, #Hdc, -⟩
    iunfold DropVec.dropCode at Hdc; icases Hdc with ⟨#Hi, -⟩; iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hsp : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h12 : (s - 16 + 12).toNat = (s - 16).toNat + 12 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have ha94 := hm.funcs 94 (by decide)
  have ha385 := hm.funcs 385 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  unfold cost96F
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hv, HD, Hvt, Hh⟩
  subst hargs
  icases stk_split n (s.toNat - 416) 400 16 $$ Hs with ⟨Hb, Hs⟩
  ihave Hs := stk_addr (show s.toNat - 416 + 400 = (s - 16).toNat by omega) $$ Hs
  icases stk_split n (s - 16).toNat 12 4 $$ Hs with ⟨S0, S12⟩
  iunfold stk at S0 S12
  icases S0 with ⟨%s0, %hs0, S0⟩
  icases S12 with ⟨%s12, %hs12, S12⟩
  icases stk_split n (s.toNat - 416) 320 80 $$ Hb with ⟨Hb1, Hb2⟩
  simp only [f96]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeLeaves.f94_spec cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16) (s - 16)
      128 aidx maxP hl live s0 hs0 (by omega) (by decide) (fun _ => hr1) (F := F) (hF := hF)) using [Hg Hb2 Hvt Hh S0]
  · iunfold pre373
    iframe Hg Hvt Hh S0
    isplitr [Hb2]; · ipureintro; rfl
    iapply stk_addr (show s.toNat - 416 + 320 = (s - 16).toNat - 80 by omega) $$ Hb2
  iunfold post373 at HQ
  icases HQ with ⟨%hrs, %q, Hg, Hb2, Hvt, V0, V4, V8, Ha⟩
  subst hrs
  icases heapAfter_grown (by simp) $$ Ha with ⟨%⟨hq0, hqb⟩, Hblk, Hgr⟩
  iunfold grown at Hgr
  icases Hgr with ⟨%hl1, %hhl1, Hh⟩
  iunfold block at Hblk
  icases Hblk with ⟨%bs, %hbs, Hq⟩
  iunfold tvData at HD
  icases HD with ⟨HD, Hqt, Hesc, Hl⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
  repeat mstep
  mstep [S12]
  repeat mstep
  mcall (f385_u128 cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16) v (s - 16 + 12)
      ptr0 aidx (s - 16) q bs maxP hl1 ((q.toNat, 128) :: live) lo hi (by omega) hv (hr2 hl1 hhl1) hbs
      (by omega) (by omega) (by simpa using hqb) (F := F) (hF := hF))
    using [Hg Hb1 Hb2 HD Hvt Hh Hv Hl Hqt Hesc S12 V0 V4 V8 Hq]
  · iframe Hg HD Hvt Hh Hv Hl
    isplitl [Hb1 Hb2]
    · iapply stk_addr (show s.toNat - 416 = (s - 16).toNat - 400 by omega)
      iapply stk_join n (s.toNat - 416) 320 80
      iframe Hb1
      iapply stk_addr (show (s - 16).toNat - 80 = s.toNat - 416 + 320 by omega) $$ Hb2
    iunfold serIn
    iframe Hqt Hesc V0 V4 V8 Hq
    iapply memBytes_addr (by omega) $$ S12
  icases HQ with ⟨%hrs, Hg, Hb, HD, Hvt, Hh, Hv, Hl, HS⟩
  subst hrs
  ihave Hc : credits Cg (100 * cfg.regularOpCost + R) $$ [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  iunfold serOut at HS
  icases HS with ⟨Hqt, Hesc, S12, V0, V4, V8, Hq⟩
  ihave L0 := (memBytes_append (GF := GF) (H := NearState) n (s - 16).toNat (bytes32 q) (bytes32 128)).2 $$ [V0 V4]
  · rw [hb32]; iframe V0 V4
  repeat mstep
  mstep [L0]
  mstep [O4]
  repeat mstep
  mstep [V8]
  mstep [O12]
  repeat mstep
  mstep [O0]
  repeat mstep
  rw [show s - 16 + 16 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  rw [ResultExpect.bytes64_decode _ (by simp [hb32])]
  icases (memBytes_append (GF := GF) (H := NearState) n (out.toNat + 4) (bytes32 q) (bytes32 128)).1 $$ O4
    with ⟨O4, O8⟩
  rw [hb32]
  iframe Hc Hg Hv Hvt
  isplitl [Hb L0 V8 S12]
  · iapply stk_addr (show (s - 16).toNat - 400 = s.toNat - 416 by omega)
    iapply stk_join n ((s - 16).toNat - 400) 400 16
    iframe Hb
    iapply stk_addr (show (s - 16).toNat = (s - 16).toNat - 400 + 400 by omega)
    iapply stk_join n (s - 16).toNat 12 4
    isplitl [L0 V8]
    · iapply stk_join n (s - 16).toNat 8 4
      isplitl [L0]; · iapply FmtU128.stk_of n _ 8 _ (by simp [hb32]) $$ L0
      iapply stk_word $$ V8
    iapply stk_word
    iapply memBytes_addr (by omega) $$ S12
  isplitl [HD Hqt Hesc Hl]
  · iunfold tvData; iframe HD Hqt Hesc Hl
  ihave Hh : (∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) (F + 1)) $$ [Hh]
  · icases Hh with ⟨%hl', -, Hh⟩; iexists hl'; iexact Hh
  iexists q
  iexists bs.drop ((kOf (val lo hi)).toNat + 2)
  iframe O0 O4 O8 Hq Hh
  isplitr; · ipureintro; simp [hbs]
  iapply memBytes_addr (by omega) $$ O12

end Spec

end WNear.Binary.ToVec
