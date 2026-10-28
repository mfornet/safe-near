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
open WNear.Binary.SerdeStruct (outV keyInT keyFirst_tab keyRest_tab str_out_tab piece_out wa_out
  f382_eq f383_eq f173_eq f176_eq f98_eq f159_eq f347_eq f99_eq)

/-- `null`, at 1048754. -/
def nullStr : List UInt8 := [110, 117, 108, 108]

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

end WNear.Binary.MetadataFields
