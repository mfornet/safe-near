import Bridge.Functions.SerdeSink

/-!
# `<FungibleTokenMetadata as Serialize>::serialize` (102)

```wat
;; frame 16 (sp = s - 16), the `Compound` (ser, state) at sp + 8
write_all(ser, "{", 1) (98); state := First
381(c, "spec", v)  381(c, "name", v + 12)  381(c, "symbol", v + 24)      ;; the strings
103(c, "icon", v + 36)  103(c, "reference", v + 48)  104(c, "reference_hash", v + 60)  ;; None
105(c, "decimals", v + 72)                                              ;; the u8, 24
106(ser, state)                                                         ;; }
```

The JSON is 138 bytes (`MetadataFields.metaJson`), the serializer's `Vec` 128: the first six
fields are written with room (`MetadataFields`), the `u8` field through the sink
`WriteSink.vsink` (`SerdeSink.f105_s`), where the key `decimals` reallocates the buffer to 256
bytes; `}` with room again.

* `metaSer`: the data the serializer reads.
* `f102_meta`: the struct at `v` (`MetadataGetter.metaOut`) serialized: the `Vec` `(q, 256, 138)`
  holding `metaJson`, live on `heapInv … (max F 1 + 1)`, the old buffer freed.
-/

namespace WNear.Binary.MetadataStruct

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (join64' split64' splitB joinB stkJ stkSp stkA stkW stkB)
open WNear.Binary.SerializeStr (EscZero serCode escCode cost383)
open WNear.Binary.SerdeStruct (outV outV_eq keyInT wa_out f98_eq f97_eq f106_end)
open WNear.Binary.MetadataFields
open WNear.Binary.MetadataGetter (metaOut specStr nameStr symbolStr)
open WNear.Binary.WriteSink (vsink vsinkOk vsink_wa costW)
open WNear.Binary.SerdeSink (keyInS f105_s cost105s)
open WNear.Binary.VecGrow (waCode)

section Struct

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The data the struct serializer reads (owned, returned): the punctuation, the keys, the digits'
table, `ESCAPE` from `' '`. -/
def metaSer (n : Nat) : IProp GF :=
  iprop(n ↦[wms][ 1048744 ] [125] ∗ n ↦[wms][ 1048754 ] nullStr ∗ n ↦[wms][ 1048758 ] [123] ∗
    n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048761 ] metaKeys ∗
    n ↦[wms][ 1049500 ] FmtDigits.lut ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1051819 ] [44] ∗
    n ↦[wms][ 1051834 ] [58] ∗ n ↦[wms][ 1061808 + 32 ] escT)

/-- The code of 102 (persistent). -/
def metaCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(mfCode inst mi A ∗ waCode n maxP inst mi A ∗ A 381 ↪[wf] FuncInst.wasm types[33]! inst f381 ∗
    A 103 ↪[wf] FuncInst.wasm types[33]! inst f103 ∗ A 104 ↪[wf] FuncInst.wasm types[33]! inst f104 ∗
    A 105 ↪[wf] FuncInst.wasm types[33]! inst f105 ∗ A 106 ↪[wf] FuncInst.wasm types[13]! inst f106 ∗
    A 97 ↪[wf] FuncInst.wasm types[0]! inst f97)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (metaCode (GF := GF) n maxP inst mi A) := by
  unfold metaCode; infer_instance

/-- The keys at 1048761, one by one. -/
theorem metaKeys_split (n : Nat) :
    (n ↦[wms][ 1048761 ] metaKeys : IProp GF) ⊣⊢
      n ↦[wms][ 1048761 ] keySpec ∗ n ↦[wms][ 1048765 ] keyName ∗ n ↦[wms][ 1048769 ] keySymbol ∗
      n ↦[wms][ 1048775 ] keyIcon ∗ n ↦[wms][ 1048779 ] keyReference ∗
      n ↦[wms][ 1048788 ] keyReferenceHash ∗ n ↦[wms][ 1048802 ] keyDecimals := by
  constructor
  · iintro H
    iunfold metaKeys at H
    icases splitB (a := 1048761) (b := 1048802) _ keyDecimals rfl $$ H with ⟨H, H7⟩
    icases splitB (a := 1048761) (b := 1048788) _ keyReferenceHash rfl $$ H with ⟨H, H6⟩
    icases splitB (a := 1048761) (b := 1048779) _ keyReference rfl $$ H with ⟨H, H5⟩
    icases splitB (a := 1048761) (b := 1048775) _ keyIcon rfl $$ H with ⟨H, H4⟩
    icases splitB (a := 1048761) (b := 1048769) _ keySymbol rfl $$ H with ⟨H, H3⟩
    icases splitB (a := 1048761) (b := 1048765) _ keyName rfl $$ H with ⟨H1, H2⟩
    iframe H1 H2 H3 H4 H5 H6 H7
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7⟩
    iunfold metaKeys
    ihave H := joinB (a := 1048761) (b := 1048765) keySpec keyName rfl $$ [H1 H2]
    · iframe H1 H2
    ihave H := joinB (a := 1048761) (b := 1048769) (keySpec ++ keyName) keySymbol rfl $$ [H H3]
    · iframe H H3
    ihave H := joinB (a := 1048761) (b := 1048775) (keySpec ++ keyName ++ keySymbol) keyIcon rfl $$ [H H4]
    · iframe H H4
    ihave H := joinB (a := 1048761) (b := 1048779) (keySpec ++ keyName ++ keySymbol ++ keyIcon) keyReference rfl $$ [H H5]
    · iframe H H5
    ihave H := joinB (a := 1048761) (b := 1048788) (keySpec ++ keyName ++ keySymbol ++ keyIcon ++ keyReference) keyReferenceHash rfl $$ [H H6]
    · iframe H H6
    iapply joinB (a := 1048761) (b := 1048802) (keySpec ++ keyName ++ keySymbol ++ keyIcon ++ keyReference ++ keyReferenceHash) keyDecimals rfl
    iframe H H7

theorem strWords_addr {n a b : Nat} {p c l : UInt32} (h : a = b) :
    strWords (GF := GF) n a p c l ⊢ strWords n b p c l := by subst h; exact .rfl

/-- The cost of 102, activation excluded. -/
def cost102 (cfg : WasmConfig) (F : Nat) : Nat :=
  6000 * cfg.regularOpCost + 13 * (MemCpy.cost 1 * cfg.regularOpCost) +
    3 * (MemCpy.cost 4 * cfg.regularOpCost) +
    3 * (cost383 (UInt32.toNat 4) * cfg.regularOpCost) + cost383 (UInt32.toNat 8) * cfg.regularOpCost +
    cost383 (UInt32.toNat 27) * cfg.regularOpCost + cost383 (UInt32.toNat 6) * cfg.regularOpCost +
    cost383 (UInt32.toNat 5) * cfg.regularOpCost + cost383 (UInt32.toNat 9) * cfg.regularOpCost +
    cost383 (UInt32.toNat 14) * cfg.regularOpCost + cost105s cfg (costW cfg F 128) (UInt32.toNat 8)


/-- The JSON written before each field (`mw2` after `spec`, …, `mw7` after `reference_hash`). -/
def mw2 : List UInt8 := [123] ++ ([34] ++ keySpec ++ [34]) ++ [58] ++ ([34] ++ specStr ++ [34])
def mw3 : List UInt8 := mw2 ++ [44] ++ ([34] ++ keyName ++ [34]) ++ [58] ++ ([34] ++ nameStr ++ [34])
def mw4 : List UInt8 := mw3 ++ [44] ++ ([34] ++ keySymbol ++ [34]) ++ [58] ++ ([34] ++ symbolStr ++ [34])
def mw5 : List UInt8 := mw4 ++ [44] ++ ([34] ++ keyIcon ++ [34]) ++ [58] ++ nullStr
def mw6 : List UInt8 := mw5 ++ [44] ++ ([34] ++ keyReference ++ [34]) ++ [58] ++ nullStr
def mw7 : List UInt8 := mw6 ++ [44] ++ ([34] ++ keyReferenceHash ++ [34]) ++ [58] ++ nullStr
def mw8 : List UInt8 := mw7 ++ [44] ++ ([34] ++ keyDecimals ++ [34]) ++ [58] ++ FmtDigits.padDigits 2 24

theorem mw7_length : mw7.length = 123 := by rfl
theorem mw8_length : mw8.length = 137 := by rfl
theorem mw8_json : mw8 ++ [125] = metaJson := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`<FungibleTokenMetadata as Serialize>::serialize(v, ser)`** (102) of the metadata at `v`
into the empty `Vec` `(q, 128)` live on `heapInv … F`: `Ok`, the `Vec` reallocated at `q'` with the
capacity 256, holding `metaJson` (138 bytes), on `heapInv … (max F 1 + 1)`. A 16-byte frame and
160 bytes below it. -/
theorem f102_meta (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 25 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ser vec q idx ps pn py : UInt32) (maxP L0 hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hs : 176 ≤ s.toNat) (hv : v.toNat + 76 ≤ 2 ^ 32) (hser : ser.toNat + 4 ≤ 2 ^ 32)
    (hps : ps.toNat + 8 ≤ 2 ^ 32) (hpn : pn.toNat + 27 ≤ 2 ^ 32) (hpy : py.toNat + 5 ≤ 2 ^ 32)
    (hq0 : q ≠ 0) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0)
    (hL1 : L0 + 2 * 65536 ≤ 2 ^ 32) (hL2 : L0 + 65536 ≤ maxP * 65536) :
    metaCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f102 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 176) 176 ∗
          metaSer n ∗ metaOut n v.toNat ps pn py ∗ n ↦[wms][ ps.toNat ] specStr ∗
          n ↦[wms][ pn.toNat ] nameStr ∗ n ↦[wms][ py.toNat ] symbolStr ∗
          n ↦[i32][ ser.toNat ] vec ∗ vt n 1057464 idx ta (A 578) ∗ outV n vec q 128 [] ∗
          heapInv n maxP hl ((q.toNat, 128) :: live) F))
        (fun _ => cost102 cfg F)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 176) 176 ∗
          metaSer n ∗ metaOut n v.toNat ps pn py ∗ n ↦[wms][ ps.toNat ] specStr ∗
          n ↦[wms][ pn.toNat ] nameStr ∗ n ↦[wms][ py.toNat ] symbolStr ∗
          n ↦[i32][ ser.toNat ] vec ∗ vt n 1057464 idx ta (A 578) ∗
          ∃ (q' : UInt32) (hl' : Nat), ⌜q' ≠ 0 ∧ hl' % 65536 = 0 ∧ 0 < hl' ∧ hl' ≤ L0 + 65536⌝ ∗
            outV n vec q' 256 metaJson ∗ heapInv n maxP hl' ((q'.toNat, 256) :: live) (max F 1 + 1))) := by
  iintro #Hk
  iunfold metaCode at Hk
  icases Hk with ⟨#HF, #HW, #H381, #H103, #H104, #H105, #H106, #H97⟩
  ihave #HF' := HF
  iunfold mfCode at HF'
  icases HF' with ⟨#Hsc, -, -, -, -, -, -, -, -, #H98, -, -, -, -⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hvl := v.toNat_lt
  obtain ⟨ek1, ek2, ek3, ek4, ek5, ek6, ek7⟩ := escT_keys
  obtain ⟨ev1, ev2, ev3⟩ := escT_values
  have e16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by rw [UInt32.toNat_add, e16]; simp; omega
  have v12 : (v + 12).toNat = v.toNat + 12 := by rw [UInt32.toNat_add]; simp; omega
  have v24 : (v + 24).toNat = v.toNat + 24 := by rw [UInt32.toNat_add]; simp; omega
  have v36 : (v + 36).toNat = v.toNat + 36 := by rw [UInt32.toNat_add]; simp; omega
  have v48 : (v + 48).toNat = v.toNat + 48 := by rw [UInt32.toNat_add]; simp; omega
  have v60 : (v + 60).toNat = v.toNat + 60 := by rw [UInt32.toNat_add]; simp; omega
  have v72 : (v + 72).toNat = v.toNat + 72 := by rw [UInt32.toNat_add]; simp; omega
  -- the specifications of the calls
  have S98 := wa_out (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16) ser vec
    q 128 1048758 1 [] [123] (by omega) rfl hser (by decide) (by decide)
  rw [← f98_eq, show MemCpy.cost (UInt32.toNat 1) = MemCpy.cost 1 from rfl] at S98
  ihave #S98 := S98 $$ Happ
  ihave #S1 := f381_first (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048761 4 v vec q 128 ps 8 8 keySpec specStr [123] escT 32 (by omega) (by omega) (by omega)
    rfl (by decide) ek1 (by decide) rfl (by decide) ev1 hps (by decide) hser $$ HF
  have S2 := f381_rest (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048765 4 (v + 12) vec q 128 pn 27 27 keyName nameStr mw2 escT 32 (by omega) (by omega)
    (by omega) rfl (by decide) ek2 (by decide) rfl (by decide) ev2 hpn (by decide) hser
  have S3 := f381_rest (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048769 6 (v + 24) vec q 128 py 5 5 keySymbol symbolStr mw3 escT 32 (by omega) (by omega)
    (by omega) rfl (by decide) ek3 (by decide) rfl (by decide) ev3 hpy (by decide) hser
  have S4 := f103_none (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048775 4 (v + 36) vec q 128 keyIcon mw4 escT 32 (by omega) (by omega) rfl (by decide) ek4
    (by decide) (by decide) hser
  have S5 := f103_none (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048779 9 (v + 48) vec q 128 keyReference mw5 escT 32 (by omega) (by omega) rfl (by decide) ek5
    (by decide) (by decide) hser
  have S6 := f104_none (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048788 14 (v + 60) vec q 128 keyReferenceHash mw6 escT 32 (by omega) (by omega) rfl (by decide)
    ek6 (by decide) (by decide) hser
  have hW := vsink_wa (GF := GF) cfg lim inst mi A n g ta hm Cg gt maxP L0 live F ser vec 128 idx (by decide)
    (by decide) hL1 hL2 hser
  have S7 := f105_s (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt
    (waCode n maxP inst mi A) ser (vsink n maxP L0 live F ser vec 128 idx ta (A 578)) _ _ hW (s - 16) (s - 16 + 8)
    1048802 8 (v + 72) 24 mw7 keyDecimals escT 32 (by omega) (by omega) (by omega) (by decide) (by decide) rfl
    (by decide) ek7 (by decide) (by rw [mw7_length]; decide)
  simp only [mw2, mw3, mw4, mw5, mw6, mw7] at S2 S3 S4 S5 S6 S7
  ihave #S2 := S2 $$ HF
  ihave #S3 := S3 $$ HF
  ihave #S4 := S4 $$ HF
  ihave #S5 := S5 $$ HF
  ihave #S6 := S6 $$ HF
  ihave #S7 := S7 $$ [HF HW]
  · iframe HF HW
  have ha98 := hm.funcs 98 (by decide)
  have ha381 := hm.funcs 381 (by decide)
  have ha103 := hm.funcs 103 (by decide)
  have ha104 := hm.funcs 104 (by decide)
  have ha105 := hm.funcs 105 (by decide)
  have ha106 := hm.funcs 106 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t33 : types[33]!.params.length = 4 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  unfold cost102
  generalize hM1 : MemCpy.cost 1 * cfg.regularOpCost = M1
  generalize MemCpy.cost 4 * cfg.regularOpCost = M4
  generalize cost383 (UInt32.toNat 4) * cfg.regularOpCost = C4
  generalize cost383 (UInt32.toNat 8) * cfg.regularOpCost = C8
  generalize cost383 (UInt32.toNat 27) * cfg.regularOpCost = C27
  generalize cost383 (UInt32.toNat 6) * cfg.regularOpCost = C6
  generalize cost383 (UInt32.toNat 5) * cfg.regularOpCost = C5
  generalize cost383 (UInt32.toNat 9) * cfg.regularOpCost = C9
  generalize cost383 (UInt32.toNat 14) * cfg.regularOpCost = C14
  generalize cost105s cfg (costW cfg F 128) (UInt32.toNat 8) = C105
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HD, HO, Hps, Hpn, Hpy, Hser, Hvt, Ho, Hinv⟩
  subst hargs
  iunfold metaSer at HD
  icases HD with ⟨Hrb, Hnull, Hlb, Hcom, Hcol, Hkeys, Hlut, Hq, Hcom2, Hcol2, He⟩
  icases (metaKeys_split n).1 $$ Hkeys with ⟨K1, K2, K3, K4, K5, K6, K7⟩
  iunfold metaOut at HO
  icases HO with ⟨O0, O4, O8, O12, O16, O20, O24, O28, O32, O36, O40, O48, O52, O60, O64, O72, O73⟩
  icases stk_split n (s.toNat - 176) 160 16 $$ Hs with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 176 + 160) 8 8 $$ Fr with ⟨F0, F8⟩
  icases stk_split n (s.toNat - 176 + 160 + 8) 4 4 $$ F8 with ⟨W8, B12⟩
  icases stk_split n (s.toNat - 176 + 160 + 8 + 4) 1 3 $$ B12 with ⟨B12, B13⟩
  iunfold stk at W8 B12
  icases W8 with ⟨%wb, %hwb, W8⟩
  icases B12 with ⟨%bb, %hbb, B12⟩
  ihave W8 := memBytes_addr (show s.toNat - 176 + 160 + 8 = (s - 16 + 8).toNat by omega) $$ W8
  ihave B12 := memBytes_addr (show s.toNat - 176 + 160 + 8 + 4 = (s - 16 + 8).toNat + 4 by omega) $$ B12
  icases stk_split n (s.toNat - 176) 144 16 $$ Lo with ⟨Lo, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 176 + 144 = (s - 16).toNat - 16 by omega) $$ Hs16
  simp only [f102]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  -- `{`
  mcall S98 using [Hg Hs16 Hser Ho Hlb]
  · iframe Hg Hs16 Hser Ho Hlb
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hlb⟩
  subst hrs
  repeat mstep
  mstep [B12]
  repeat mstep
  mstep [W8]
  repeat mstep
  -- the first field, `spec`
  ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = s.toNat - 176 + 144 by omega) $$ Hs16
  ihave Lo := stk_join n (s.toNat - 176) 144 16 $$ [Lo Hs16]
  · iframe Lo Hs16
  icases stk_split n (s.toNat - 176) 96 64 $$ Lo with ⟨Lo, L64⟩
  ihave L64 := stk_addr (show s.toNat - 176 + 96 = (s - 16).toNat - 64 by omega) $$ L64
  mcredits (5700 * cfg.regularOpCost + 12 * M1 + 3 * M4 + 3 * C4 + C8 + C27 + C6 + C5 + C9 + C14 + C105 + R)
  mcall S1 using [Hg L64 W8 B12 Hcol2 Hq He Hser Ho K1 O0 O4 O8 Hps]
  · iframe Hg L64 W8 Hcol2
    isplitl [B12]
    · rw [show storeBytes (Value.i32 1) 1 = ([1] : List UInt8) from rfl]; iexact B12
    isplitl [Hq He Hser Ho K1]
    · iunfold keyInT
      iframe Hq He Hser Ho
      iapply memBytes_addr (by decide) $$ K1
    iunfold strWords
    iframe O0 O4 O8 Hps
  icases HQ with ⟨%hrs, Hg, L64, W8, B12, Hcol2, HK, HW1, Hps⟩
  subst hrs
  repeat mstep
  -- `name`
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, K1⟩
  mcall S2 using [Hg L64 W8 B12 Hcom2 Hcol2 Hq He Hser Ho K2 O12 O16 O20 Hpn]
  · iframe Hg L64 W8 B12 Hcom2 Hcol2
    isplitl [Hq He Hser Ho K2]
    · iunfold keyInT
      iframe Hq He Hser Ho
      iapply memBytes_addr (by decide) $$ K2
    iframe Hpn
    iapply strWords_addr (show v.toNat + 12 = (v + 12).toNat by omega)
    iunfold strWords
    iframe O12 O16 O20
  icases HQ with ⟨%hrs, Hg, L64, W8, B12, Hcom2, Hcol2, HK, HW2, Hpn⟩
  subst hrs
  repeat mstep
  -- `symbol`
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, K2⟩
  mcall S3 using [Hg L64 W8 B12 Hcom2 Hcol2 Hq He Hser Ho K3 O24 O28 O32 Hpy]
  · iframe Hg L64 W8 B12 Hcom2 Hcol2
    isplitl [Hq He Hser Ho K3]
    · iunfold keyInT
      iframe Hq He Hser Ho
      iapply memBytes_addr (by decide) $$ K3
    iframe Hpy
    iapply strWords_addr (show v.toNat + 24 = (v + 24).toNat by omega)
    iunfold strWords
    iframe O24 O28 O32
  icases HQ with ⟨%hrs, Hg, L64, W8, B12, Hcom2, Hcol2, HK, HW3, Hpy⟩
  subst hrs
  repeat mstep
  -- `icon`
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, K3⟩
  ihave O36 := memBytes_addr (show v.toNat + 36 = (v + 36).toNat by omega) $$ O36
  mcall S4 using [Hg L64 W8 B12 Hcom Hcol Hnull Hq He Hser Ho K4 O36]
  · iframe Hg L64 W8 B12 Hcom Hcol Hnull O36
    iunfold keyInT
    iframe Hq He Hser Ho
    iapply memBytes_addr (by decide) $$ K4
  icases HQ with ⟨%hrs, Hg, L64, W8, B12, Hcom, Hcol, Hnull, HK, O36⟩
  subst hrs
  repeat mstep
  -- `reference`
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, K4⟩
  ihave O48 := memBytes_addr (show v.toNat + 48 = (v + 48).toNat by omega) $$ O48
  mcall S5 using [Hg L64 W8 B12 Hcom Hcol Hnull Hq He Hser Ho K5 O48]
  · iframe Hg L64 W8 B12 Hcom Hcol Hnull O48
    iunfold keyInT
    iframe Hq He Hser Ho
    iapply memBytes_addr (by decide) $$ K5
  icases HQ with ⟨%hrs, Hg, L64, W8, B12, Hcom, Hcol, Hnull, HK, O48⟩
  subst hrs
  repeat mstep
  -- `reference_hash`
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, K5⟩
  ihave O60 := memBytes_addr (show v.toNat + 60 = (v + 60).toNat by omega) $$ O60
  icases stk_split n ((s - 16).toNat - 64) 16 48 $$ L64 with ⟨L16, L48⟩
  ihave L48 := stk_addr (show (s - 16).toNat - 64 + 16 = (s - 16).toNat - 48 by omega) $$ L48
  mcall S6 using [Hg L48 W8 B12 Hcom Hcol Hnull Hq He Hser Ho K6 O60]
  · iframe Hg L48 W8 B12 Hcom Hcol Hnull O60
    iunfold keyInT
    iframe Hq He Hser Ho
    iapply memBytes_addr (by decide) $$ K6
  icases HQ with ⟨%hrs, Hg, L48, W8, B12, Hcom, Hcol, Hnull, HK, O60⟩
  subst hrs
  repeat mstep
  -- `decimals`, through the sink: the buffer is reallocated
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, K6⟩
  ihave L48 := stk_addr (show (s - 16).toNat - 48 = (s - 16).toNat - 64 + 16 by omega) $$ L48
  ihave L64 := stk_join n ((s - 16).toNat - 64) 16 48 $$ [L16 L48]
  · iframe L16 L48
  ihave L64 := stk_addr (show (s - 16).toNat - 64 = s.toNat - 176 + 96 by omega) $$ L64
  ihave Lo := stk_join n (s.toNat - 176) 96 64 $$ [Lo L64]
  · iframe Lo L64
  ihave Lo := stk_addr (show s.toNat - 176 = (s - 16).toNat - 160 by omega) $$ Lo
  ihave O72 := memBytes_addr (show v.toNat + 72 = (v + 72).toNat by omega) $$ O72
  mcall S7 using [Hg Lo W8 B12 Hcom Hcol Hlut Hq He K7 Hser Hvt Ho Hinv O72]
  · iframe Hg Lo W8 B12 Hcom Hcol Hlut O72
    isplitl [Hq He K7]
    · iunfold keyInS
      iframe Hq He
      iapply memBytes_addr (by decide) $$ K7
    iunfold vsink
    iframe Hser Hvt
    iexists q, 128, hl, F
    isplitr
    · ipureintro
      exact ⟨Or.inl ⟨rfl, rfl, hlL⟩, hl0, hl1, hq0⟩
    iframe Ho
    iapply (show heapInv (GF := GF) n maxP hl ((q.toNat, 128) :: live) F ⊢
      heapInv n maxP hl ((q.toNat, (128 : UInt32).toNat) :: live) F from .rfl) $$ Hinv
  icases HQ with ⟨%hrs, Hg, Lo, W8, B12, Hcom, Hcol, Hlut, HKS, HS, O72⟩
  subst hrs
  iunfold vsink at HS
  icases HS with ⟨Hser, Hvt, %q', %cap, %hl', %F', %hok, Ho, Hinv⟩
  ihave Ho := outV_eq (w' := mw8) (by rfl) $$ Ho
  mcredits (300 * cfg.regularOpCost + M1 + R)
  iunfold outV at Ho
  icases Ho with ⟨%rest, %⟨hr1, hr2, hr3⟩, V0, V4, V8, Hb⟩
  rw [mw8_length] at hr1
  obtain ⟨hcase, hl0', hl1', hq0'⟩ := hok
  have hcap : cap.toNat = 256 ∧ F' = max F 1 + 1 ∧ hl' ≤ L0 + 65536 := by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · subst h1; simp at hr1; omega
    · exact ⟨h1, h2, h3⟩
  obtain ⟨hc256, hF', hlL'⟩ := hcap
  have hcapE : cap = 256 := UInt32.toNat_inj.mp hc256
  subst hcapE hF'
  ihave Ho : outV n vec q' 256 mw8 $$ [V0 V4 V8 Hb]
  · iunfold outV
    iexists rest
    iframe V0 V4 V8 Hb
    ipureintro; exact ⟨by rw [mw8_length]; omega, hr2, hr3⟩
  have S106 := f106_end (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16) ser
    vec q' 256 mw8 (by omega) hser (by rw [mw8_length]; decide)
  rw [hM1] at S106
  ihave #S106 := S106 $$ [Happ H97 H98]
  · iframe Happ H97 H98
  repeat mstep
  ihave W8 := memBytes_addr (show (s - 16 + 8).toNat = (s - 16).toNat + 8 by omega) $$ W8
  ihave B12 := memBytes_addr (show (s - 16 + 8).toNat + 4 = (s - 16).toNat + 12 by omega) $$ B12
  mstep [W8]
  repeat mstep
  mstep [B12]
  repeat mstep
  simp only [show loadValue NumType.i32 (some { bits := 8, signed := false }) (Memory.decodeLE [2]) = Value.i32 2 from rfl]
  icases stk_split n ((s - 16).toNat - 160) 144 16 $$ Lo with ⟨Lo, Hs16⟩
  ihave Hs16 := stk_addr (show (s - 16).toNat - 160 + 144 = (s - 16).toNat - 16 by omega) $$ Hs16
  mcall S106 using [Hg Hs16 Hser Ho Hrb]
  · iframe Hg Hs16 Hser Ho Hrb
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hrb⟩
  subst hrs
  repeat mstep
  rw [show s - 16 + 16 = s by simp]
  mstep [Hg]
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hser Hvt
  isplitr
  · ipureintro; simp [htype]
  isplitl [Lo Hs16 F0 W8 B12 B13]
  · ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = (s - 16).toNat - 160 + 144 by omega) $$ Hs16
    ihave Lo := stk_join n ((s - 16).toNat - 160) 144 16 $$ [Lo Hs16]
    · iframe Lo Hs16
    ihave Lo := stk_addr (show (s - 16).toNat - 160 = s.toNat - 176 by omega) $$ Lo
    ihave W8 := stk_word n _ ser $$ W8
    ihave B12 := ReadRegister.stk_bytes n _ [2] 1 rfl $$ B12
    iapply stk_join n (s.toNat - 176) 160 16
    iframe Lo
    iapply stk_join n (s.toNat - 176 + 160) 8 8
    iframe F0
    iapply stk_join n (s.toNat - 176 + 160 + 8) 4 4
    isplitl [W8]
    · iapply stk_addr (show (s - 16).toNat + 8 = s.toNat - 176 + 160 + 8 by omega) $$ W8
    iapply stk_join n (s.toNat - 176 + 160 + 8 + 4) 1 3
    iframe B13
    iapply stk_addr (show (s - 16).toNat + 12 = s.toNat - 176 + 160 + 8 + 4 by omega) $$ B12
  isplitl [Hrb Hnull Hlb Hcom Hcol K1 K2 K3 K4 K5 K6 HKS Hlut Hcom2 Hcol2]
  · iunfold metaSer
    iunfold keyInS at HKS
    icases HKS with ⟨Hq, He, K7⟩
    iframe Hrb Hnull Hlb Hcom Hcol Hlut Hq Hcom2 Hcol2 He
    iapply (metaKeys_split n).2
    iframe K1 K2 K3 K4 K5 K6
    iapply memBytes_addr (by decide) $$ K7
  isplitl [HW1 HW2 HW3 O36 O40 O48 O52 O60 O64 O72 O73]
  · iunfold metaOut
    iunfold strWords at HW1 HW2 HW3
    icases HW1 with ⟨O0, O4, O8⟩
    icases HW2 with ⟨O12, O16, O20⟩
    icases HW3 with ⟨O24, O28, O32⟩
    iframe O0 O4 O8 O40 O52 O64 O73
    ihave O12 := memBytes_addr (show (v + 12).toNat = v.toNat + 12 by omega) $$ O12
    ihave O16 := memBytes_addr (show (v + 12).toNat + 4 = v.toNat + 16 by omega) $$ O16
    ihave O20 := memBytes_addr (show (v + 12).toNat + 8 = v.toNat + 20 by omega) $$ O20
    ihave O24 := memBytes_addr (show (v + 24).toNat = v.toNat + 24 by omega) $$ O24
    ihave O28 := memBytes_addr (show (v + 24).toNat + 4 = v.toNat + 28 by omega) $$ O28
    ihave O32 := memBytes_addr (show (v + 24).toNat + 8 = v.toNat + 32 by omega) $$ O32
    ihave O36 := memBytes_addr (show (v + 36).toNat = v.toNat + 36 by omega) $$ O36
    ihave O48 := memBytes_addr (show (v + 48).toNat = v.toNat + 48 by omega) $$ O48
    ihave O60 := memBytes_addr (show (v + 60).toNat = v.toNat + 60 by omega) $$ O60
    ihave O72 := memBytes_addr (show (v + 72).toNat = v.toNat + 72 by omega) $$ O72
    iframe O12 O16 O20 O24 O28 O32 O36 O48 O60 O72
  iframe Hps Hpn Hpy
  iexists q', hl'
  iframe Hinv
  isplitr
  · ipureintro; exact ⟨hq0', hl0', hl1', hlL'⟩
  iapply outV_eq mw8_json $$ Ho

end Struct

end WNear.Binary.MetadataStruct
