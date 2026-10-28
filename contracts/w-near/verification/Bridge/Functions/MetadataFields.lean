import Bridge.Functions.SerdeStructTab
import Bridge.Functions.MetadataGetter
import Bridge.Functions.VecDeref

/-!
# The fields of `FungibleTokenMetadata`'s serializer (102)

`#[derive(Serialize)]` on `FungibleTokenMetadata` (near-contract-standards 3.1.0) compiles to 102,
one `serialize_field` per field, each a monomorphization:

```
381 String           key (382 = keyFn 345 1051819 383), `:` (347), deref (779), serialize_str (383)
103 Option<String>   key (173 = keyFn 98 1048759 176), `:` (99); None: `null` (174); Some: 779, 176
104 Option<Base64VecU8>  key (173), `:` (99); None: `null` (174); Some: 175
105 u8               key (173), `:` (99), the digits (160) into a 48-byte frame, write_all (98)
174 serialize_none   write_all(ser, "null" at 1048754, 4)
160 u8 to decimal    the digits at the end of a 3-byte buffer, from DEC_DIGITS_LUT at 1049500
147 drop Option<String>  the String's drop (68) unless the pointer is null
```

The strings' bytes land on zero entries of `ESCAPE` (`SerializeStr.EscZero`, the `_tab` pieces of
SerdeStructTab.lean): the struct's keys (`reference_hash` holds `_`) and values (spaces,
capitals, `-`, `.` and digits) span the entries of `"` and `\`.

* `f381_first`, `f381_rest`: a `String` field (`strWords`, its bytes at its pointer), first or later.
* `f103_none`, `f104_none`: an `Option` field holding `None` (the null pointer): the key and `null`.
* `f174_null`, `f147_none`: `null`; the drop of a `None`.
* `f160_two`: a two-digit `u8` (`10 ≤ v < 100`): its two digits (`FmtDigits.padDigits 2 v`).
-/

namespace WNear.Binary.MetadataFields

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (join64' split64' splitB joinB stkJ stkSp stkA stkW stkB)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.SerializeStr (EscZero serCode escCode cost383)
open WNear.Binary.SerdeStruct (outV outV_eq keyInT keyFirst_tab keyRest_tab str_out_tab piece_out wa_out
  f382_eq f383_eq f173_eq f176_eq f98_eq f159_eq f347_eq f99_eq)

/-- `null`, at 1048754. -/
def nullStr : List UInt8 := [110, 117, 108, 108]

/-! ## The keys, the `ESCAPE` entries and the JSON -/

/-- The keys, in field order, at 1048761 .. 1048810: `spec`, `name`, `symbol`, `icon`,
`reference`, `reference_hash`, `decimals`. -/
def keySpec : List UInt8 := [115, 112, 101, 99]
def keyName : List UInt8 := [110, 97, 109, 101]
def keySymbol : List UInt8 := [115, 121, 109, 98, 111, 108]
def keyIcon : List UInt8 := [105, 99, 111, 110]
def keyReference : List UInt8 := [114, 101, 102, 101, 114, 101, 110, 99, 101]
def keyReferenceHash : List UInt8 := [114, 101, 102, 101, 114, 101, 110, 99, 101, 95, 104, 97, 115, 104]
def keyDecimals : List UInt8 := [100, 101, 99, 105, 109, 97, 108, 115]

/-- The 49 bytes of the keys. -/
def metaKeys : List UInt8 :=
  keySpec ++ keyName ++ keySymbol ++ keyIcon ++ keyReference ++ keyReferenceHash ++ keyDecimals

/-- `ESCAPE` from `' '` (32) to 127, at 1061840: zero but for `"` (34) and `\` (92). -/
def escT : List UInt8 :=
  List.replicate 2 0 ++ [34] ++ List.replicate 57 0 ++ [92] ++ List.replicate 35 0

theorem escT_length : escT.length = 96 := rfl

set_option maxRecDepth 100000 in
theorem escT_zero : ∀ i < 96, i ≠ 2 → i ≠ 60 → escT[i]? = some 0 := by decide

/-- Printable ASCII but `"` and `\` land on zero entries of `escT`. -/
theorem escZero_of (ds : List UInt8) (h : ∀ b ∈ ds, 32 ≤ b.toNat ∧ b.toNat < 128 ∧ b.toNat ≠ 34 ∧ b.toNat ≠ 92) :
    EscZero 32 escT ds := by
  intro b hb
  obtain ⟨h1, h2, h3, h4⟩ := h b hb
  exact ⟨h1, by rw [escT_length]; omega, escT_zero (b.toNat - 32) (by omega) (by omega) (by omega)⟩

set_option maxRecDepth 100000 in
theorem escT_keys : EscZero 32 escT keySpec ∧ EscZero 32 escT keyName ∧ EscZero 32 escT keySymbol ∧
    EscZero 32 escT keyIcon ∧ EscZero 32 escT keyReference ∧ EscZero 32 escT keyReferenceHash ∧
    EscZero 32 escT keyDecimals :=
  ⟨escZero_of _ (by decide), escZero_of _ (by decide), escZero_of _ (by decide), escZero_of _ (by decide),
    escZero_of _ (by decide), escZero_of _ (by decide), escZero_of _ (by decide)⟩

set_option maxRecDepth 100000 in
theorem escT_values : EscZero 32 escT MetadataGetter.specStr ∧ EscZero 32 escT MetadataGetter.nameStr ∧
    EscZero 32 escT MetadataGetter.symbolStr :=
  ⟨escZero_of _ (by decide), escZero_of _ (by decide), escZero_of _ (by decide)⟩

/-- The JSON `ft_metadata` returns: the struct serializer's pieces in field order. -/
def metaJson : List UInt8 :=
  [123] ++ SerdeStruct.jstr keySpec ++ [58] ++ SerdeStruct.jstr MetadataGetter.specStr ++
    [44] ++ SerdeStruct.jstr keyName ++ [58] ++ SerdeStruct.jstr MetadataGetter.nameStr ++
    [44] ++ SerdeStruct.jstr keySymbol ++ [58] ++ SerdeStruct.jstr MetadataGetter.symbolStr ++
    [44] ++ SerdeStruct.jstr keyIcon ++ [58] ++ nullStr ++
    [44] ++ SerdeStruct.jstr keyReference ++ [58] ++ nullStr ++
    [44] ++ SerdeStruct.jstr keyReferenceHash ++ [58] ++ nullStr ++
    [44] ++ SerdeStruct.jstr keyDecimals ++ [58] ++ FmtDigits.padDigits 2 24 ++ [125]

set_option maxRecDepth 100000 in
/-- 138 bytes: more than the 128 the `Vec` of `ft_metadata` (309) is created with, so the
serializer's `write_all` reallocates it (at the contents of the key `decimals`). -/
theorem metaJson_length : metaJson.length = 138 := by rfl

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the fields (persistent). -/
def mfCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(serCode inst mi A ∗ A 382 ↪[wf] FuncInst.wasm types[15]! inst f382 ∗
    A 383 ↪[wf] FuncInst.wasm types[15]! inst f383 ∗ A 173 ↪[wf] FuncInst.wasm types[15]! inst f173 ∗
    A 176 ↪[wf] FuncInst.wasm types[15]! inst f176 ∗ A 159 ↪[wf] FuncInst.wasm types[35]! inst f159 ∗
    A 367 ↪[wf] FuncInst.wasm types[35]! inst f367 ∗ A 347 ↪[wf] FuncInst.wasm types[0]! inst f347 ∗
    A 99 ↪[wf] FuncInst.wasm types[0]! inst f99 ∗ A 98 ↪[wf] FuncInst.wasm types[31]! inst f98 ∗
    A 345 ↪[wf] FuncInst.wasm types[31]! inst f345 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
    A 174 ↪[wf] FuncInst.wasm types[32]! inst f174 ∗ A 160 ↪[wf] FuncInst.wasm types[31]! inst f160)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (mfCode (GF := GF) inst mi A) := by
  unfold mfCode; infer_instance

/-- A `String` `(p, c, l)` at `v`. -/
def strWords (n v : Nat) (p c l : UInt32) : IProp GF :=
  iprop(n ↦[i32][ v ] p ∗ n ↦[i32][ v + 4 ] c ∗ n ↦[i32][ v + 8 ] l)

end Code

/-! ## `null` and the drop of a `None` -/

section Null

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`serialize_none`** (174): `null` (at 1048754) appended; `Ok`. -/
theorem f174_null (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ser vec ptr cap : UInt32) (w : List UInt8) (hs : 16 ≤ s.toNat)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + 4 ≤ cap.toNat) :
    VecAppend.appCode inst mi A ∗ A 98 ↪[wf] FuncInst.wasm types[31]! inst f98
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f174 Cg
        (fun args => iprop(⌜args = [.i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗ n ↦[wms][ 1048754 ] nullStr))
        (fun _ => 150 * cfg.regularOpCost + MemCpy.cost 4 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap (w ++ nullStr) ∗ n ↦[wms][ 1048754 ] nullStr)) := by
  iintro ⟨#Hk, #H98⟩
  have S := wa_out (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s ser vec
    ptr cap 1048754 4 w nullStr hs rfl hser hroom (by decide)
  rw [← f98_eq] at S
  ihave #S := S $$ Hk
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Hk; icases Hk with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have ha98 := hm.funcs 98 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost (UInt32.toNat 4) * cfg.regularOpCost = M
  rw [show MemCpy.cost 4 * cfg.regularOpCost = M by rw [← hM]; rfl]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hser, Ho, Hnull⟩
  subst hargs
  simp only [f174]
  repeat mstep
  mcall S using [Hg Hs Hser Ho Hnull]
  · iframe Hg Hs Hser Ho
    iapply memBytes_addr (by decide) $$ Hnull
  icases HQ with ⟨%hrs, Hg, Hs, Hser, Ho, Hnull⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hs Hser Ho
  isplitr
  · ipureintro; simp [htype]
  iapply memBytes_addr (by decide) $$ Hnull

/-- **The drop of an `Option<String>` holding `None`** (147): the null pointer, nothing freed. -/
theorem f147_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (v : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f147 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] 0))
        (fun _ => 10 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, H0⟩
  subst hargs
  simp only [f147]
  repeat mstep
  mstep [H0]
  repeat mstep
  mcredits R
  iframe Hc H0

end Null

/-! ## A two-digit `u8` (160) -/

section U8

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.FmtDigits (lut lut_length lut_pair padDigits memBytes_focus storeBytes_load16')

/-- The pair of digits `x` in a copy of the table at `a`. -/
theorem lut_focusAt (n a x : Nat) (hx : x < 100) :
    memBytes (H := NearState) (GF := GF) n a lut ⊢
      n ↦[wms][ a + 2 * x ] padDigits 2 x ∗ (n ↦[wms][ a + 2 * x ] padDigits 2 x -∗ n ↦[wms][ a ] lut) := by
  iintro H
  icases memBytes_focus n a (2 * x) 2 lut (by rw [lut_length]; omega) $$ H with ⟨H1, H2⟩
  rw [lut_pair x hx]
  iframe H1
  iintro H1
  have e : lut.take (2 * x) ++ padDigits 2 x ++ lut.drop (2 * x + 2) = lut := by
    rw [← lut_pair x hx, List.append_assoc, ← List.drop_drop, List.take_append_drop,
      List.take_append_drop]
  ispecialize H2 $$ %(padDigits 2 x)
  rw [e]
  iapply H2
  · ipureintro; simp [FmtDigits.padDigits]
  · iexact H1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`u8` to decimal** (160) of `10 ≤ v < 100`: its two digits at `buf + 1`, and the slice
`(buf + 1, 2)` at `out`. -/
theorem f160_two (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out buf v : UInt32) (ob db : List UInt8)
    (hob : ob.length = 8) (hdb : db.length = 2) (hv1 : 10 ≤ v.toNat) (hv2 : v.toNat < 100)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hbuf : buf.toNat + 3 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f160 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 buf, .i32 v]⌝ ∗ n ↦[wms][ out.toNat ] ob ∗
          n ↦[wms][ buf.toNat + 1 ] db ∗ n ↦[wms][ 1049500 ] lut))
        (fun _ => 50 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] (buf + 1) ∗ n ↦[i32][ out.toNat + 4 ] 2 ∗
          n ↦[wms][ buf.toNat + 1 ] padDigits 2 v.toNat ∗ n ↦[wms][ 1049500 ] lut)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho, Hd, Hl⟩
  subst hargs
  have hlt := v.toNat_lt
  have hand : v &&& 255 = v := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_and]; simp only [UInt32.reduceToNat]
    rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  icases lut_focusAt n 1049500 v.toNat hv2 $$ Hl with ⟨Hp, Hl⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  simp only [f160]
  repeat mstep
  rw [hand]
  mstep_taken with (simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega)
  repeat mstep
  mstep_taken with (simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega)
  repeat mstep
  have hsh : (v <<< (1 % 32) + 1049500).toNat = 1049500 + 2 * v.toNat := by
    simp [UInt32.toNat_add, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hpl : (padDigits 2 v.toNat).length = 2 := by simp [FmtDigits.padDigits]
  generalize padDigits 2 v.toNat = pd at hpl ⊢
  generalize v <<< (1 % 32) + 1049500 = la at hsh ⊢
  ihave Hp := memBytes_addr (b := la.toNat) (by omega) $$ Hp
  mstep [Hp]
  mstep [Hd]
  rw [storeBytes_load16' _ hpl]
  repeat mstep
  mstep [O4]
  repeat mstep
  mstep [O0]
  repeat mstep
  mcredits R
  ihave Hp := memBytes_addr (b := 1049500 + 2 * v.toNat) (by omega) $$ Hp
  ihave Hl := Hl $$ Hp
  iframe Hc Hl Hd O0
  rw [show (3 : UInt32) - 1 = 2 from rfl]
  iexact O4

end U8

/-! ## A `String` field (381) -/

section Str

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's first field, a `String`** (381 with the `Compound`'s state `First`): the key
`"ds"`, `:` (at 1051834), the value's JSON string `"vs"`, the `String` `(pv, cv, lv)` at `v`. -/
theorem f381_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s c ser p k v vec ptr cap pv cv lv : UInt32) (ds vs w et : List UInt8) (lo : Nat)
    (hs : 64 ≤ s.toNat) (hc : c.toNat + 8 ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hkey : EscZero lo et ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hvs : vs.length = lv.toNat) (hl0 : 0 < lv.toNat) (hval : EscZero lo et vs)
    (hpv : pv.toNat + lv.toNat ≤ 2 ^ 32)
    (hroom : w.length + (k.toNat + 2) + 1 + (lv.toNat + 2) ≤ cap.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32) :
    mfCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f381 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [1] ∗
          n ↦[wms][ 1051834 ] [58] ∗ keyInT n ser vec ptr cap w lo et p ds ∗ strWords n v.toNat pv cv lv ∗
          n ↦[wms][ pv.toNat ] vs))
        (fun _ => 300 * cfg.regularOpCost + MemCpy.cost 1 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost +
          cost383 lv.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1051834 ] [58] ∗
          keyInT n ser vec ptr cap (w ++ ([34] ++ ds ++ [34]) ++ [58] ++ ([34] ++ vs ++ [34])) lo et p ds ∗
          strWords n v.toNat pv cv lv ∗ n ↦[wms][ pv.toNat ] vs)) := by
  iintro #Hk
  iunfold mfCode at Hk
  icases Hk with ⟨#Hsc, #H382, #H383, -, -, -, #H367, #H347, -, -, #H345, #H779, -, -⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hlt := s.toNat_lt
  have hvl := v.toNat_lt
  have e16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by rw [UInt32.toNat_add, e16]; simp; omega
  have S382 := keyFirst_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 345 383 367
    1051819 (by decide) (by decide) gt (s - 16) c ser vec ptr cap p k w ds (by omega) hc hds hk0 lo et hkey hser
    (by omega) hp
  rw [← f382_eq, ← f383_eq] at S382
  ihave #S382 := S382 $$ [Hsc H383 H367]
  · iframe Hsc H383 H367
  have S347 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 345 (by decide)
    1051834 gt (s - 16) ser vec ptr cap (w ++ ([34] ++ ds ++ [34])) 58 (by omega) hser (by simp; omega) (by decide)
  rw [← f347_eq] at S347
  ihave #S347 := S347 $$ [Happ H345]
  · iframe Happ H345
  have S383 := str_out_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 367
    (by decide) gt (s - 16) ser vec ptr cap pv lv (w ++ ([34] ++ ds ++ [34]) ++ [58]) vs (by omega) hvs hl0 lo et
    hval hser (by simp; omega) hpv
  rw [← f383_eq] at S383
  ihave #S383 := S383 $$ [Hsc H367]
  · iframe Hsc H367
  have hg := hm.glob
  have hn := hm.mem
  have ha382 := hm.funcs 382 (by decide)
  have ha347 := hm.funcs 347 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha383 := hm.funcs 383 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize cost383 lv.toNat * cfg.regularOpCost = C2
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcol, HK, HW, Hvs⟩
  subst hargs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  iunfold strWords at HW
  icases HW with ⟨V0, V4, V8⟩
  icases stk_split n (s.toNat - 64) 48 16 $$ Hs with ⟨Hs48, Hfr⟩
  icases stk_split n (s.toNat - 64 + 48) 8 8 $$ Hfr with ⟨F0, F8⟩
  iunfold stk at F8
  icases F8 with ⟨%fb, %hfb, F8⟩
  ihave Hs48 := stk_addr (show s.toNat - 64 = (s - 16).toNat - 48 by omega) $$ Hs48
  simp only [f381]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  -- the key
  mcall S382 using [Hg Hs48 Hcs Hst Hq He Hser Ho Hds]
  · iframe Hg Hs48 Hcs Hst
    iunfold keyInT
    iframe Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs48, Hcs, Hst, HK⟩
  subst hrs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- `:`
  icases stk_split n ((s - 16).toNat - 48) 32 16 $$ Hs48 with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show (s - 16).toNat - 48 + 32 = (s - 16).toNat - 16 by omega) $$ Hs16
  mcall S347 using [Hg Hs16 Hser Ho Hcol]
  · iframe Hg Hs16 Hser Ho Hcol
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- deref
  ihave VB := join64' (a := v.toNat) (b := v.toNat + 4) pv cv rfl $$ [V0 V4]
  · iframe V0 V4
  ihave VB := joinB (a := v.toNat) (b := v.toNat + 8) (bytes32 pv ++ bytes32 cv) (bytes32 lv) (by simp) $$ [VB V8]
  · iframe VB V8
  ihave F8 := memBytes_addr (b := (s - 16 + 8).toNat) (by omega) $$ F8
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 16 + 8) v fb
      (bytes32 pv ++ bytes32 cv ++ bytes32 lv) hfb (by simp)) using [F8 VB]
  · iunfold VecDeref.pre
    iframe F8 VB
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, F8, VB⟩
  subst hrs
  have hvb : (bytes32 pv ++ (bytes32 cv ++ bytes32 lv)).take 4 ++ (bytes32 pv ++ (bytes32 cv ++ bytes32 lv)).drop 8 =
      bytes32 pv ++ bytes32 lv := by
    simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  ihave F8 := memBytes_addr (b := (s - 16).toNat + 8) (by omega) $$ F8
  icases split64' (a := (s - 16).toNat + 8) (b := (s - 16).toNat + 12) pv lv (by omega) $$ F8 with ⟨F8, F12⟩
  repeat mstep
  mstep [F8]
  repeat mstep
  mstep [F12]
  repeat mstep
  -- the value
  ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = (s - 16).toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs48 := stk_join n ((s - 16).toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  mcall S383 using [Hg Hs48 Hq He Hser Ho Hvs]
  · iframe Hg Hs48 Hq He Hser Ho Hvs
  icases HQ with ⟨%hrs, Hg, Hs48, Hq, He, Hser, Ho, Hvs⟩
  subst hrs
  repeat mstep
  rw [show s - 16 + 16 = s by simp]
  mstep [Hg]
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hcs Hst Hcol Hvs
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hs48 F0 F8 F12]
  · ihave Hs48 := stk_addr (show (s - 16).toNat - 48 = s.toNat - 64 by omega) $$ Hs48
    ihave F8 := stk_word n _ pv $$ F8
    ihave F12 := stk_word n _ lv $$ F12
    ihave F8 := stk_join n ((s - 16).toNat + 8) 4 4 $$ [F8 F12]
    · iframe F8; iapply stk_addr (show (s - 16).toNat + 12 = (s - 16).toNat + 8 + 4 by omega) $$ F12
    iapply stk_join n (s.toNat - 64) 48 16
    iframe Hs48
    iapply stk_join n (s.toNat - 64 + 48) 8 8
    iframe F0
    iapply stk_addr (show (s - 16).toNat + 8 = s.toNat - 64 + 48 + 8 by omega) $$ F8
  isplitl [Hq He Hser Ho Hds]
  · iunfold keyInT
    iframe Hq He Hser Hds
    iapply outV_eq (by simp) $$ Ho
  iunfold strWords
  icases splitB (a := v.toNat) (b := v.toNat + 4) (bytes32 pv) (bytes32 cv ++ bytes32 lv) (by simp) $$ VB with ⟨V0, VB⟩
  icases split64' (a := v.toNat + 4) (b := v.toNat + 8) cv lv rfl $$ VB with ⟨V4, V8⟩
  iframe V0 V4 V8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's later field, a `String`** (381 with the `Compound`'s state `Rest`): `,` (at
1051819), the key `"ds"`, `:` (at 1051834), the value's JSON string `"vs"`, the `String` `(pv, cv, lv)` at `v`. -/
theorem f381_rest (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s c ser p k v vec ptr cap pv cv lv : UInt32) (ds vs w et : List UInt8) (lo : Nat)
    (hs : 64 ≤ s.toNat) (hc : c.toNat + 8 ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hkey : EscZero lo et ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hvs : vs.length = lv.toNat) (hl0 : 0 < lv.toNat) (hval : EscZero lo et vs)
    (hpv : pv.toNat + lv.toNat ≤ 2 ^ 32)
    (hroom : w.length + 1 + (k.toNat + 2) + 1 + (lv.toNat + 2) ≤ cap.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32) :
    mfCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f381 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗ n ↦[wms][ 1051819 ] [44] ∗
          n ↦[wms][ 1051834 ] [58] ∗ keyInT n ser vec ptr cap w lo et p ds ∗ strWords n v.toNat pv cv lv ∗
          n ↦[wms][ pv.toNat ] vs))
        (fun _ => 500 * cfg.regularOpCost + 2 * (MemCpy.cost 1 * cfg.regularOpCost) + cost383 k.toNat * cfg.regularOpCost +
          cost383 lv.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗ n ↦[wms][ 1051819 ] [44] ∗
          n ↦[wms][ 1051834 ] [58] ∗
          keyInT n ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58] ++ ([34] ++ vs ++ [34])) lo et p ds ∗
          strWords n v.toNat pv cv lv ∗ n ↦[wms][ pv.toNat ] vs)) := by
  iintro #Hk
  iunfold mfCode at Hk
  icases Hk with ⟨#Hsc, #H382, #H383, -, -, -, #H367, #H347, -, -, #H345, #H779, -, -⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hlt := s.toNat_lt
  have hvl := v.toNat_lt
  have e16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by rw [UInt32.toNat_add, e16]; simp; omega
  have S382 := keyRest_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 345 383 367
    1051819 (by decide) (by decide) (by decide) 44 gt (s - 16) c ser vec ptr cap p k w ds (by omega) hc hds hk0 lo et hkey hser
    (by omega) hp (by decide)
  rw [← f382_eq, ← f383_eq] at S382
  ihave #S382 := S382 $$ [Hsc H345 H383 H367]
  · iframe Hsc H345 H383 H367
  have S347 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 345 (by decide)
    1051834 gt (s - 16) ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34])) 58 (by omega) hser (by simp; omega) (by decide)
  rw [← f347_eq] at S347
  ihave #S347 := S347 $$ [Happ H345]
  · iframe Happ H345
  have S383 := str_out_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 367
    (by decide) gt (s - 16) ser vec ptr cap pv lv (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58]) vs (by omega) hvs hl0 lo et
    hval hser (by simp; omega) hpv
  rw [← f383_eq] at S383
  ihave #S383 := S383 $$ [Hsc H367]
  · iframe Hsc H367
  have hg := hm.glob
  have hn := hm.mem
  have ha382 := hm.funcs 382 (by decide)
  have ha347 := hm.funcs 347 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha383 := hm.funcs 383 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize cost383 lv.toNat * cfg.regularOpCost = C2
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcom, Hcol, HK, HW, Hvs⟩
  subst hargs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  iunfold strWords at HW
  icases HW with ⟨V0, V4, V8⟩
  icases stk_split n (s.toNat - 64) 48 16 $$ Hs with ⟨Hs48, Hfr⟩
  icases stk_split n (s.toNat - 64 + 48) 8 8 $$ Hfr with ⟨F0, F8⟩
  iunfold stk at F8
  icases F8 with ⟨%fb, %hfb, F8⟩
  ihave Hs48 := stk_addr (show s.toNat - 64 = (s - 16).toNat - 48 by omega) $$ Hs48
  simp only [f381]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  -- the key
  mcall S382 using [Hg Hs48 Hcs Hst Hcom Hq He Hser Ho Hds]
  · iframe Hg Hs48 Hcs Hst Hcom
    iunfold keyInT
    iframe Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs48, Hcs, Hst, Hcom, HK⟩
  subst hrs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- `:`
  icases stk_split n ((s - 16).toNat - 48) 32 16 $$ Hs48 with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show (s - 16).toNat - 48 + 32 = (s - 16).toNat - 16 by omega) $$ Hs16
  mcall S347 using [Hg Hs16 Hser Ho Hcol]
  · iframe Hg Hs16 Hser Ho Hcol
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- deref
  ihave VB := join64' (a := v.toNat) (b := v.toNat + 4) pv cv rfl $$ [V0 V4]
  · iframe V0 V4
  ihave VB := joinB (a := v.toNat) (b := v.toNat + 8) (bytes32 pv ++ bytes32 cv) (bytes32 lv) (by simp) $$ [VB V8]
  · iframe VB V8
  ihave F8 := memBytes_addr (b := (s - 16 + 8).toNat) (by omega) $$ F8
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 16 + 8) v fb
      (bytes32 pv ++ bytes32 cv ++ bytes32 lv) hfb (by simp)) using [F8 VB]
  · iunfold VecDeref.pre
    iframe F8 VB
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, F8, VB⟩
  subst hrs
  have hvb : (bytes32 pv ++ (bytes32 cv ++ bytes32 lv)).take 4 ++ (bytes32 pv ++ (bytes32 cv ++ bytes32 lv)).drop 8 =
      bytes32 pv ++ bytes32 lv := by
    simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  ihave F8 := memBytes_addr (b := (s - 16).toNat + 8) (by omega) $$ F8
  icases split64' (a := (s - 16).toNat + 8) (b := (s - 16).toNat + 12) pv lv (by omega) $$ F8 with ⟨F8, F12⟩
  repeat mstep
  mstep [F8]
  repeat mstep
  mstep [F12]
  repeat mstep
  -- the value
  ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = (s - 16).toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs48 := stk_join n ((s - 16).toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  mcall S383 using [Hg Hs48 Hq He Hser Ho Hvs]
  · iframe Hg Hs48 Hq He Hser Ho Hvs
  icases HQ with ⟨%hrs, Hg, Hs48, Hq, He, Hser, Ho, Hvs⟩
  subst hrs
  repeat mstep
  rw [show s - 16 + 16 = s by simp]
  mstep [Hg]
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hcs Hst Hcom Hcol Hvs
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hs48 F0 F8 F12]
  · ihave Hs48 := stk_addr (show (s - 16).toNat - 48 = s.toNat - 64 by omega) $$ Hs48
    ihave F8 := stk_word n _ pv $$ F8
    ihave F12 := stk_word n _ lv $$ F12
    ihave F8 := stk_join n ((s - 16).toNat + 8) 4 4 $$ [F8 F12]
    · iframe F8; iapply stk_addr (show (s - 16).toNat + 12 = (s - 16).toNat + 8 + 4 by omega) $$ F12
    iapply stk_join n (s.toNat - 64) 48 16
    iframe Hs48
    iapply stk_join n (s.toNat - 64 + 48) 8 8
    iframe F0
    iapply stk_addr (show (s - 16).toNat + 8 = s.toNat - 64 + 48 + 8 by omega) $$ F8
  isplitl [Hq He Hser Ho Hds]
  · iunfold keyInT
    iframe Hq He Hser Hds
    iapply outV_eq (by simp) $$ Ho
  iunfold strWords
  icases splitB (a := v.toNat) (b := v.toNat + 4) (bytes32 pv) (bytes32 cv ++ bytes32 lv) (by simp) $$ VB with ⟨V0, VB⟩
  icases split64' (a := v.toNat + 4) (b := v.toNat + 8) cv lv rfl $$ VB with ⟨V4, V8⟩
  iframe V0 V4 V8

end Str

/-! ## An `Option` field holding `None` (103, 104) -/

section None

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's later field, an `Option<String>` holding `None`** (103, the state `Rest`): `,` (at
1048759), the key `"ds"`, `:` (at 1048760), `null`; the null pointer at `v`. -/
theorem f103_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s c ser p k v vec ptr cap : UInt32) (ds w et : List UInt8) (lo : Nat)
    (hs : 64 ≤ s.toNat) (hc : c.toNat + 8 ≤ 2 ^ 32)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hkey : EscZero lo et ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hroom : w.length + 1 + (k.toNat + 2) + 1 + 4 ≤ cap.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32) :
    mfCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f103 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048754 ] nullStr ∗
          keyInT n ser vec ptr cap w lo et p ds ∗ n ↦[i32][ v.toNat ] 0))
        (fun _ => 600 * cfg.regularOpCost + 2 * (MemCpy.cost 1 * cfg.regularOpCost) +
          MemCpy.cost 4 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048754 ] nullStr ∗
          keyInT n ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58] ++ nullStr) lo et p ds ∗
          n ↦[i32][ v.toNat ] 0)) := by
  iintro #Hk
  iunfold mfCode at Hk
  icases Hk with ⟨#Hsc, -, -, #H173, #H176, #H159, -, -, #H99, #H98, -, -, #H174, -⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hlt := s.toNat_lt
  have e16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have S173 := keyRest_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 98 176 159
    1048759 (by decide) (by decide) (by decide) 44 gt (s - 16) c ser vec ptr cap p k w ds (by omega) hc hds hk0 lo et
    hkey hser (by omega) hp (by decide)
  rw [← f173_eq, ← f176_eq, ← f98_eq, ← f159_eq] at S173
  ihave #S173 := S173 $$ [Hsc H98 H176 H159]
  · iframe Hsc H98 H176 H159
  have S99 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 98 (by decide)
    1048760 gt (s - 16) ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34])) 58 (by omega) hser (by simp; omega)
    (by decide)
  rw [← f99_eq, ← f98_eq] at S99
  ihave #S99 := S99 $$ [Happ H98]
  · iframe Happ H98
  ihave #S174 := f174_null (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58]) (by omega) hser (by simp; omega) $$ [Happ H98]
  · iframe Happ H98
  have hn := hm.mem
  have hg := hm.glob
  have ha173 := hm.funcs 173 (by decide)
  have ha99 := hm.funcs 99 (by decide)
  have ha174 := hm.funcs 174 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  generalize hM4 : MemCpy.cost 4 * cfg.regularOpCost = M4
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcom, Hcol, Hnull, HK, Hv⟩
  subst hargs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  icases stk_split n (s.toNat - 64) 48 16 $$ Hs with ⟨Hs48, Hfr⟩
  ihave Hs48 := stk_addr (show s.toNat - 64 = (s - 16).toNat - 48 by omega) $$ Hs48
  simp only [f103]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  -- the key
  mcall S173 using [Hg Hs48 Hcs Hst Hcom Hq He Hser Ho Hds]
  · iframe Hg Hs48 Hcs Hst Hcom
    iunfold keyInT
    iframe Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs48, Hcs, Hst, Hcom, HK⟩
  subst hrs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- `:`
  icases stk_split n ((s - 16).toNat - 48) 32 16 $$ Hs48 with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show (s - 16).toNat - 48 + 32 = (s - 16).toNat - 16 by omega) $$ Hs16
  mcall S99 using [Hg Hs16 Hser Ho Hcol]
  · iframe Hg Hs16 Hser Ho Hcol
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  mstep [Hv]
  repeat mstep
  -- `null`
  mcall S174 using [Hg Hs16 Hser Ho Hnull]
  · iframe Hg Hs16 Hser Ho Hnull
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hnull⟩
  subst hrs
  repeat mstep
  rw [show s - 16 + 16 = s by simp]
  mstep [Hg]
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hcs Hst Hcom Hcol Hnull Hv
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hs32 Hs16 Hfr]
  · ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = (s - 16).toNat - 48 + 32 by omega) $$ Hs16
    ihave Hs48 := stk_join n ((s - 16).toNat - 48) 32 16 $$ [Hs32 Hs16]
    · iframe Hs32 Hs16
    ihave Hs48 := stk_addr (show (s - 16).toNat - 48 = s.toNat - 64 by omega) $$ Hs48
    iapply stk_join n (s.toNat - 64) 48 16
    iframe Hs48 Hfr
  iunfold keyInT
  iframe Hq He Hser Hds
  iapply outV_eq (by simp) $$ Ho

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's later field, an `Option<Base64VecU8>` holding `None`** (104, the state `Rest`): as
`f103_none`, without a frame. -/
theorem f104_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s c ser p k v vec ptr cap : UInt32) (ds w et : List UInt8) (lo : Nat)
    (hs : 48 ≤ s.toNat) (hc : c.toNat + 8 ≤ 2 ^ 32)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hkey : EscZero lo et ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hroom : w.length + 1 + (k.toNat + 2) + 1 + 4 ≤ cap.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32) :
    mfCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f104 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048754 ] nullStr ∗
          keyInT n ser vec ptr cap w lo et p ds ∗ n ↦[i32][ v.toNat ] 0))
        (fun _ => 600 * cfg.regularOpCost + 2 * (MemCpy.cost 1 * cfg.regularOpCost) +
          MemCpy.cost 4 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048754 ] nullStr ∗
          keyInT n ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58] ++ nullStr) lo et p ds ∗
          n ↦[i32][ v.toNat ] 0)) := by
  iintro #Hk
  iunfold mfCode at Hk
  icases Hk with ⟨#Hsc, -, -, #H173, #H176, #H159, -, -, #H99, #H98, -, -, #H174, -⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hlt := s.toNat_lt
  have S173 := keyRest_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 98 176 159
    1048759 (by decide) (by decide) (by decide) 44 gt s c ser vec ptr cap p k w ds (by omega) hc hds hk0 lo et
    hkey hser (by omega) hp (by decide)
  rw [← f173_eq, ← f176_eq, ← f98_eq, ← f159_eq] at S173
  ihave #S173 := S173 $$ [Hsc H98 H176 H159]
  · iframe Hsc H98 H176 H159
  have S99 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 98 (by decide)
    1048760 gt s ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34])) 58 (by omega) hser (by simp; omega)
    (by decide)
  rw [← f99_eq, ← f98_eq] at S99
  ihave #S99 := S99 $$ [Happ H98]
  · iframe Happ H98
  ihave #S174 := f174_null (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm (by omega) Cg gt s
    ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58]) (by omega) hser (by simp; omega) $$ [Happ H98]
  · iframe Happ H98
  have hn := hm.mem
  have ha173 := hm.funcs 173 (by decide)
  have ha99 := hm.funcs 99 (by decide)
  have ha174 := hm.funcs 174 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  generalize hM4 : MemCpy.cost 4 * cfg.regularOpCost = M4
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcom, Hcol, Hnull, HK, Hv⟩
  subst hargs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  simp only [f104]
  repeat mstep
  -- the key
  mcall S173 using [Hg Hs Hcs Hst Hcom Hq He Hser Ho Hds]
  · iframe Hg Hs Hcs Hst Hcom
    iunfold keyInT
    iframe Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hcs, Hst, Hcom, HK⟩
  subst hrs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- `:`
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  mcall S99 using [Hg Hs16 Hser Ho Hcol]
  · iframe Hg Hs16 Hser Ho Hcol
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  mstep [Hv]
  repeat mstep
  -- `null`
  mcall S174 using [Hg Hs16 Hser Ho Hnull]
  · iframe Hg Hs16 Hser Ho Hnull
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hnull⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hcs Hst Hcom Hcol Hnull Hv
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hs32 Hs16]
  · ihave Hs16 := stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
    iapply stk_join n (s.toNat - 48) 32 16
    iframe Hs32 Hs16
  iunfold keyInT
  iframe Hq He Hser Hds
  iapply outV_eq (by simp) $$ Ho

end None

end WNear.Binary.MetadataFields
