import Bridge.Functions.ToString
import Binary.Code.Part00
import Binary.Code.Part01
import Bridge.Functions.BorshFT

/-!
# `serde_json` struct serialization into a `Vec<u8>` with room (M5)

`#[derive(Serialize)]` on a struct with named fields, serialized by `serde_json::to_writer` into
`&mut Vec<u8>` (capacity known, never grown on these paths), compiles to a struct serializer
calling one `serialize_field` per field. The pieces, for the `Vec` behind the serializer `ser`
(`*ser = vec`):

```
345 / 98      write_all(ser, p, k)            the k bytes at p appended (98 is 345's code)
pieceFn cw a  (ser)                           write_all(ser, a, 1) through cw: 97 `}`, 99 `:`, 347 `:`
strFn ce      serialize_str(ser, p, k)        format_escaped_str (344); the io result (367 / 159)
                                              383 = strFn 367, 176 = strFn 159
keyFn cw a ck (c, p, k)                       the Compound c = (ser, state byte): unless state = 1, the
                                              comma at a through cw; state := 2; the key through ck
                                              382 = keyFn 345 1051819 383, 173 = keyFn 98 1048759 176
```

The output is `outV n vec ptr cap w`: the `Vec` `(ptr, cap, |w|)` at `vec` holding the bytes `w`,
its spare capacity owned. Each piece appends to `w` with room (`|w| + k ≤ cap`).

* `outV_open`, `outV_close`: `outV` to the `(ptr, cap, len)` words and the bytes at
  `ptr + len`, and back.
* `wa_out`: 345 (and 98) on `outV`.
* `piece_out`: a one-byte piece (`pieceFn`).
* `str_out`: `serialize_str` of a string whose bytes lie in a zero chunk of `ESCAPE`
  (`SerializeStr.InRange`), quotes included.
* `keyFirst_out`, `keyRest_out`: the key of the first field (no comma) and of the others.
* `f385_out`: `<U128 as Serialize>::serialize` into `outV` at any length (`ToString.f385_gen`
  with `str_out`); its `String` freed, the free list one longer (`F + 1`, any `F ≥ 1`).
* `f384_first`, `f109_some`: a struct's first field, a `U128` (384), and a later one, an
  `Option<U128>` holding `Some` (109): the key, `:`, the value.
* `f106_end`: `SerializeStruct::end` (106), `}`.
* `f108_bounds`: `StorageBalanceBounds` (108): `{"min":"a","max":"b"}` (`boundsJson`), at
  `cost108`; the second value's `to_string` allocates on `heapInv … (F + 1)`.

The keys, punctuation and the lowercase letters' `ESCAPE` entries are data the caller owns
(`boundsData`).
-/

namespace WNear.Binary.SerdeStruct

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.U128From (memBytes_split memBytes_join)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtSink (roomPre roomPost)
open WNear.Binary.SerializeStr (InRange serCode escCode cost344 cost383 f383_esc f344_esc f367_ok)

/-! ## The functions, by shape -/

theorem f98_eq : f98 = f345 := rfl
theorem f159_eq : f159 = f367 := rfl

/-- `write_all(ser, a, 1)` through `cw` (a one-byte piece). -/
def pieceFn (cw : Nat) (a : UInt32) : Func :=
  { type := 0, locals := [], body := [.local_get 0, .i32_const a, .i32_const 1, .call cw], bodySize := 18 }

theorem f97_eq : f97 = pieceFn 98 1048744 := rfl
theorem f99_eq : f99 = pieceFn 98 1048760 := rfl
theorem f347_eq : f347 = pieceFn 345 1051834 := rfl

/-- `serialize_str(ser, p, k)`: `format_escaped_str` (344), then the io result through `ce`. -/
def strFn (ce : Nat) : Func :=
  { type := 15, locals := [],
    body := [.local_get 0, .local_get 0, .local_get 1, .local_get 2, .call 344, .call ce], bodySize := 22 }

theorem f383_eq : f383 = strFn 367 := rfl
theorem f176_eq : f176 = strFn 159 := rfl

/-- `SerializeMap::serialize_key` of a `Compound` at `c`: unless its state byte is 1 (`First`),
the comma at `a` through `cw`; the state 2 (`Rest`); the key through `ck`. -/
def keyFn (cw : Nat) (a : UInt32) (ck : Nat) : Func :=
  { type := 15, locals := [],
    body := [.block .empty [.local_get 0, .load .i32 (some { bits := 8, signed := false }) { align := 0, offset := 4 },
        .i32_const 1, .i32_relop .eq, .br_if 0, .local_get 0, .load .i32 none { align := 2, offset := 0 },
        .i32_const a, .i32_const 1, .call cw],
      .local_get 0, .i32_const 2, .store .i32 (some 8) { align := 0, offset := 4 }, .local_get 0,
      .load .i32 none { align := 2, offset := 0 }, .local_get 1, .local_get 2, .call ck],
    bodySize := 56 }

theorem f382_eq : f382 = keyFn 345 1051819 383 := rfl
theorem f173_eq : f173 = keyFn 98 1048759 176 := rfl

/-! ## The output `Vec` -/

section Out

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The serializer's output: the `Vec<u8>` `(ptr, cap, |w|)` at `vec` holding `w`, the spare
capacity owned. -/
def outV (n : Nat) (vec ptr cap : UInt32) (w : List UInt8) : IProp GF :=
  iprop(∃ rest : List UInt8, ⌜w.length + rest.length = cap.toNat ∧ ptr.toNat + cap.toNat < 2 ^ 32 ∧
      vec.toNat + 12 ≤ 2 ^ 32⌝ ∗
    n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat w.length ∗
    n ↦[wms][ ptr.toNat ] (w ++ rest))

theorem ofNat_len {w : List UInt8} {cap : UInt32} (h : w.length ≤ cap.toNat) :
    (UInt32.ofNat w.length).toNat = w.length := by
  have := cap.toNat_lt
  simp only [UInt32.toNat_ofNat']
  omega

/-- `outV` opened for `k` more bytes: the words, the bytes so far, the `k` bytes after them. -/
theorem outV_open (n : Nat) (vec ptr cap : UInt32) (w : List UInt8) (k : Nat) (hk : w.length + k ≤ cap.toNat) :
    outV (GF := GF) n vec ptr cap w ⊢
      ∃ ob rest : List UInt8, ⌜ob.length = k ∧ w.length + k + rest.length = cap.toNat ∧
          ptr.toNat + cap.toNat < 2 ^ 32 ∧ vec.toNat + 12 ≤ 2 ^ 32⌝ ∗
        n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat w.length ∗ n ↦[wms][ ptr.toNat ] w ∗
        n ↦[wms][ ptr.toNat + (UInt32.ofNat w.length).toNat ] ob ∗ n ↦[wms][ ptr.toNat + w.length + k ] rest := by
  have hl := ofNat_len (w := w) (cap := cap) (by omega)
  iintro H
  iunfold outV at H
  icases H with ⟨%rest, %⟨h1, h2, h3⟩, V0, V4, V8, Hb⟩
  icases splitB (a := ptr.toNat) (b := ptr.toNat + w.length) w rest rfl $$ Hb with ⟨Hw, Hr⟩
  icases memBytes_split n (ptr.toNat + w.length) k rest (by omega) $$ Hr with ⟨Ho, Hr⟩
  iexists rest.take k, rest.drop k
  iframe V0 V4 V8 Hw Hr
  isplitr
  · ipureintro; simp; omega
  iapply memBytes_addr (by rw [hl]) $$ Ho

theorem outV_eq {n : Nat} {vec ptr cap : UInt32} {w w' : List UInt8} (h : w = w') :
    outV (GF := GF) n vec ptr cap w ⊢ outV n vec ptr cap w' := by
  subst h; exact .rfl

/-- `outV` closed after the bytes `b`: the length word `len'` is `|w| + |b|`. -/
theorem outV_close (n : Nat) (vec ptr cap len' : UInt32) (w b rest : List UInt8)
    (hlen : len'.toNat = w.length + b.length) (hr : w.length + b.length + rest.length = cap.toNat)
    (hp : ptr.toNat + cap.toNat < 2 ^ 32) (hv : vec.toNat + 12 ≤ 2 ^ 32) :
    n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len' ∗
      n ↦[wms][ ptr.toNat ] w ∗ n ↦[wms][ ptr.toNat + w.length ] b ∗
      n ↦[wms][ ptr.toNat + w.length + b.length ] rest ⊢ outV (GF := GF) n vec ptr cap (w ++ b) := by
  have e : len' = UInt32.ofNat (w ++ b).length := by
    apply UInt32.toNat_inj.mp
    rw [ofNat_len (cap := cap) (by simp; omega)]
    simp [hlen]
  subst e
  iintro ⟨V0, V4, V8, Hw, Hb, Hr⟩
  iunfold outV
  iexists rest
  iframe V0 V4 V8
  isplitr
  · ipureintro; simp; omega
  ihave Hbr := joinB (a := ptr.toNat + w.length) (b := ptr.toNat + w.length + b.length) b rest rfl $$ [Hb Hr]
  · iframe Hb Hr
  ihave H := joinB (a := ptr.toNat) (b := ptr.toNat + w.length) w (b ++ rest) rfl $$ [Hw Hbr]
  · iframe Hw Hbr
  rw [List.append_assoc]
  iexact H

end Out

/-! ## Specifications through an existential frame -/

section Conseq

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A specification for every `x` with `φ x` gives one whose precondition chooses such an `x`, a
frame `Fr x` kept. -/
theorem MFunSpec_wrap {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {Hk : IProp GF} [Persistent Hk] {α : Type} (φ : α → Prop)
    {P0 : α → List Value → IProp GF} {K : List Value → Nat} {Q0 : α → List Value → List Value → IProp GF}
    {P' : List Value → IProp GF} {Q' : List Value → List Value → IProp GF} (Fr : α → IProp GF)
    (hS : ∀ x, φ x → Hk ⊢ MFunSpec cfg lim d type inst mi code Cg (P0 x) K (Q0 x))
    (hP : ∀ args, P' args ⊢ ∃ x, ⌜φ x⌝ ∗ P0 x args ∗ Fr x)
    (hQ : ∀ x, φ x → ∀ args rs, Fr x ∗ Q0 x args rs ⊢ Q' args rs) :
    Hk ⊢ MFunSpec cfg lim d type inst mi code Cg P' K Q' := by
  iintro #Hk
  unfold MFunSpec
  imodintro
  iintro %args %R HP Hc
  icases hP args $$ HP with ⟨%x, %hx, HP, HF⟩
  have hS' := hS x hx
  unfold MFunSpec at hS'
  ihave #H := hS' $$ Hk
  iapply mwpInvoke_wand
  isplitl [HP Hc]
  · iapply H $$ %args %R HP Hc
  isplit
  · dsimp only
    iintro %rs ⟨Hc, HQ⟩
    iframe Hc
    iapply hQ x hx args rs
    iframe HF HQ
  · iintro HT; iexact HT

/-- **`write_all(ser, p, k)`** (345's code, also 98's) on `outV`: the `k` bytes `sb` at `p`
appended. -/
theorem wa_out (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ser vec ptr cap p k : UInt32) (w sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hsb : sb.length = k.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + k.toNat ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    VecAppend.appCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f345 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗ n ↦[wms][ p.toNat ] sb))
        (fun _ => 135 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)) := by
  have hl := ofNat_len (w := w) (cap := cap) (by omega)
  refine MFunSpec_wrap (α := List UInt8 × List UInt8)
    (fun x => x.1.length = k.toNat ∧ w.length + k.toNat + x.2.length = cap.toNat ∧
      ptr.toNat + cap.toNat < 2 ^ 32 ∧ vec.toNat + 12 ≤ 2 ^ 32)
    (P0 := fun x args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ ser.toNat ] vec ∗
      roomPre n g gt s vec ptr cap (UInt32.ofNat w.length) p x.1 sb))
    (Q0 := fun _ _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ ser.toNat ] vec ∗
      roomPost n g gt s vec ptr cap (UInt32.ofNat w.length) p k sb))
    (fun x => iprop(n ↦[wms][ ptr.toNat ] w ∗ n ↦[wms][ ptr.toNat + w.length + k.toNat ] x.2))
    (fun x hx => VecAppend.f345_room cfg lim d type htype inst mi A n g ta hm hd Cg gt s ser vec ptr cap
      (UInt32.ofNat w.length) p k x.1 sb hs hx.1 hsb hser hx.2.2.2 (by omega) hx.2.2.1 hp) ?_ ?_
  · intro args
    iintro ⟨%ha, Hg, Hs, Hser, Ho, Hsb⟩
    icases outV_open n vec ptr cap w k.toNat hroom $$ Ho with ⟨%ob, %rest, %⟨h1, h2, h3, h4⟩, V0, V4, V8, Hw, Hob, Hr⟩
    iexists (ob, rest)
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4⟩
    iframe Hw Hr Hser
    isplitr
    · ipureintro; exact ha
    iunfold roomPre
    iframe Hg Hs V0 V4 V8 Hob Hsb
  · intro x hx args rs
    iintro ⟨⟨Hw, Hr⟩, %hrs, Hser, HQ⟩
    iunfold roomPost at HQ
    icases HQ with ⟨Hg, Hs, V0, V4, V8, Hb, Hsb⟩
    iframe Hg Hs Hser Hsb
    isplitr
    · ipureintro; exact hrs
    obtain ⟨h1, h2, h3, h4⟩ := hx
    iapply outV_close n vec ptr cap (UInt32.ofNat w.length + k) w sb x.2
      (by rw [UInt32.toNat_add, hl, hsb]; have := cap.toNat_lt; omega) (by omega) h3 h4
    iframe V0 V4 V8 Hw
    isplitl [Hb]
    · iapply memBytes_addr (by rw [hl]) $$ Hb
    iapply memBytes_addr (by rw [hsb]) $$ Hr

end Conseq

/-! ## One-byte pieces and strings -/

section Pieces

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A one-byte piece** (`pieceFn cw a`, `cw` with 345's code): the byte `b` at `a` appended. -/
theorem piece_out (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat) (cw : Nat) (hcw : cw < 955)
    (a : UInt32) (gt : GlobalType) (s ser vec ptr cap : UInt32) (w : List UInt8) (b : UInt8) (hs : 16 ≤ s.toNat)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + 1 ≤ cap.toNat) (ha : a.toNat + 1 ≤ 2 ^ 32) :
    VecAppend.appCode inst mi A ∗ A cw ↪[wf] FuncInst.wasm types[31]! inst f345
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (pieceFn cw a) Cg
        (fun args => iprop(⌜args = [.i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗ n ↦[wms][ a.toNat ] [b]))
        (fun _ => 150 * cfg.regularOpCost + MemCpy.cost 1 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap (w ++ [b]) ∗ n ↦[wms][ a.toNat ] [b])) := by
  iintro ⟨#Hk, #Hw⟩
  ihave #S := wa_out (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s ser vec
    ptr cap a 1 w [b] hs rfl hser hroom ha $$ Hk
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Hk; icases Hk with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hcw' := hm.funcs cw hcw
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost (UInt32.toNat 1) * cfg.regularOpCost = M
  rw [show MemCpy.cost 1 * cfg.regularOpCost = M by rw [← hM]; rfl]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [pieceFn]
  repeat mstep
  mcall S using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `serialize_str` (`strFn ce`, `ce` with 367's code) of `k` bytes in a zero chunk of
`ESCAPE`: as `SerializeStr.f383_esc`. -/
theorem strFn_esc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat) (ce : Nat) (hce : ce < 955)
    (gt : GlobalType) (s ser vec ptr cap len p k : UInt32) (ob ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hob : ob.length = k.toNat + 2) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo m : Nat)
    (hdig : InRange lo m ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hroom : len.toNat + k.toNat + 2 ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (strFn ce) Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] (len + k + 2) ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ([34] ++ ds ++ [34]) ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro ⟨#Hk, #H367⟩
  ihave #S344 := f344_esc (GF := GF) cfg lim (d + 1) types[48]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s ser ser vec ptr cap len p k ob ds hs hob hds hk0 lo m hdig hser hvec hroom hptr hp $$ Hk
  iunfold serCode at Hk
  icases Hk with ⟨#He, -, #H344, -⟩
  iunfold escCode at He
  icases He with ⟨#Happ, -, -, -, -⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have ha344 := hm.funcs 344 (by decide)
  have hace := hm.funcs ce hce
  have t48 : types[48]!.params.length = 4 := by rfl
  have t35 : types[35]!.params.length = 1 := by rfl
  unfold cost383
  rw [Nat.add_mul]
  generalize cost344 k.toNat * cfg.regularOpCost = C
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [strFn]
  repeat mstep
  mcall S344 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HP⟩
  subst hrs
  mcall (f367_ok cfg lim (d + 1) types[35]! (by rfl) inst mi Cg) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc HP
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`serialize_str` on `outV`** (`strFn ce`): the JSON string `"ds"` appended, `ds` in a zero
chunk of `ESCAPE` (`InRange lo m`). -/
theorem str_out (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat) (ce : Nat) (hce : ce < 955)
    (gt : GlobalType) (s ser vec ptr cap p k : UInt32) (w ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo m : Nat)
    (hdig : InRange lo m ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + k.toNat + 2 ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (strFn ce) Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap (w ++ ([34] ++ ds ++ [34])) ∗ n ↦[wms][ p.toNat ] ds)) := by
  have hl := ofNat_len (w := w) (cap := cap) (by omega)
  refine MFunSpec_wrap (α := List UInt8 × List UInt8)
    (fun x => x.1.length = k.toNat + 2 ∧ w.length + (k.toNat + 2) + x.2.length = cap.toNat ∧
      ptr.toNat + cap.toNat < 2 ^ 32 ∧ vec.toNat + 12 ≤ 2 ^ 32)
    (P0 := fun x args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗
      n ↦[i32][ ser.toNat ] vec ∗
      n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat w.length ∗
      n ↦[wms][ ptr.toNat + (UInt32.ofNat w.length).toNat ] x.1 ∗ n ↦[wms][ p.toNat ] ds))
    (Q0 := fun _ _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗
      n ↦[i32][ ser.toNat ] vec ∗
      n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
      n ↦[i32][ vec.toNat + 8 ] (UInt32.ofNat w.length + k + 2) ∗
      n ↦[wms][ ptr.toNat + (UInt32.ofNat w.length).toNat ] ([34] ++ ds ++ [34]) ∗ n ↦[wms][ p.toNat ] ds))
    (fun x => iprop(n ↦[wms][ ptr.toNat ] w ∗ n ↦[wms][ ptr.toNat + w.length + (k.toNat + 2) ] x.2))
    (fun x hx => strFn_esc cfg lim d type htype inst mi A n g ta hm hd Cg ce hce gt s ser vec ptr cap
      (UInt32.ofNat w.length) p k x.1 ds hs hx.1 hds hk0 lo m hdig hser hx.2.2.2 (by omega) hx.2.2.1 hp) ?_ ?_
  · intro args
    iintro ⟨%ha, Hg, Hs, Hq, He, Hser, Ho, Hds⟩
    icases outV_open n vec ptr cap w (k.toNat + 2) (by omega) $$ Ho with
      ⟨%ob, %rest, %⟨h1, h2, h3, h4⟩, V0, V4, V8, Hw, Hob, Hr⟩
    iexists (ob, rest)
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4⟩
    iframe Hw Hr Hg Hs Hq He Hser V0 V4 V8 Hob Hds
    ipureintro; exact ha
  · intro x hx args rs
    iintro ⟨⟨Hw, Hr⟩, %hrs, Hg, Hs, Hq, He, Hser, V0, V4, V8, Hb, Hds⟩
    iframe Hg Hs Hq He Hser Hds
    isplitr
    · ipureintro; exact hrs
    obtain ⟨h1, h2, h3, h4⟩ := hx
    iapply outV_close n vec ptr cap (UInt32.ofNat w.length + k + 2) w ([34] ++ ds ++ [34]) x.2
      (by simp only [UInt32.toNat_add, hl]; have := cap.toNat_lt; simp; omega) (by simp; omega) h3 h4
    iframe V0 V4 V8 Hw
    isplitl [Hb]
    · iapply memBytes_addr (by rw [hl]) $$ Hb
    iapply memBytes_addr (by simp; omega) $$ Hr

end Pieces

/-! ## Keys -/

section Keys

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What a key writer (`keyFn cw a ck`) reads besides the `Compound`: the quote, the `ESCAPE`
chunk, `*ser = vec`, the output and the key's bytes. -/
def keyIn (n : Nat) (ser vec ptr cap : UInt32) (w : List UInt8) (lo m : Nat) (p : UInt32) (ds : List UInt8) :
    IProp GF :=
  iprop(n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] List.replicate m 0 ∗ n ↦[i32][ ser.toNat ] vec ∗
    outV n vec ptr cap w ∗ n ↦[wms][ p.toNat ] ds)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The key of a struct's first field** (`keyFn cw a ck` with the state byte 1, `First`): no
comma; the state 2; the key `"ds"` appended (`ck = strFn ce`). -/
theorem keyFirst_out (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (cw ck ce : Nat) (a : UInt32)
    (hck : ck < 955) (hce : ce < 955)
    (gt : GlobalType) (s c ser vec ptr cap p k : UInt32) (w ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hc : c.toNat + 8 ≤ 2 ^ 32) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo m : Nat)
    (hdig : InRange lo m ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + k.toNat + 2 ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A ∗ A ck ↪[wf] FuncInst.wasm types[15]! inst (strFn ce) ∗
      A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (keyFn cw a ck) Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [1] ∗
          keyIn n ser vec ptr cap w lo m p ds))
        (fun _ => 30 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          keyIn n ser vec ptr cap (w ++ ([34] ++ ds ++ [34])) lo m p ds)) := by
  iintro ⟨#Hk, #Hck, #Hce⟩
  ihave #S := str_out (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg ce hce gt s ser
    vec ptr cap p k w ds hs hds hk0 lo m hdig hser hroom hp $$ [Hk Hce]
  · iframe Hk Hce
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold serCode, escCode, VecAppend.appCode at Hk; icases Hk with ⟨⟨⟨-, -, -, -, -, -, #Hi⟩, -⟩, -⟩; iexact Hi
  have hn := hm.mem
  have hack := hm.funcs ck hck
  have t15 : types[15]!.params.length = 3 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, HK⟩
  subst hargs
  iunfold keyIn at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  simp only [keyFn]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  have hloc : actSize ((strFn ce).locals.map ValType.default) = 0 := rfl
  mcall S using [Hg Hs Hq He Hser Ho Hds]
    with (mstep_norm_full; simp only [hloc, Nat.reduceAdd, Nat.reduceDiv] at *; omega)
  · iframe Hg Hs Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hq, He, Hser, Ho, Hds⟩
  subst hrs
  repeat mstep
  mstep_post
  simp only [hloc, Nat.reduceAdd, Nat.reduceDiv, show storeBytes (Value.i32 2) 1 = ([2] : List UInt8) from rfl]
  mcredits R
  iframe Hc Hg Hs Hcs Hst
  isplitr
  · ipureintro; simp [htype]
  iunfold keyIn
  iframe Hq He Hser Ho Hds

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The key of a struct's later field** (`keyFn cw a ck` with the state byte 2, `Rest`): the
comma `cb` at `a` through `cw` (345's code), then the key `"ds"` (`ck = strFn ce`). -/
theorem keyRest_out (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (cw ck ce : Nat) (a : UInt32)
    (hcw : cw < 955) (hck : ck < 955) (hce : ce < 955) (cb : UInt8)
    (gt : GlobalType) (s c ser vec ptr cap p k : UInt32) (w ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hc : c.toNat + 8 ≤ 2 ^ 32) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo m : Nat)
    (hdig : InRange lo m ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + 1 + k.toNat + 2 ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (ha : a.toNat + 1 ≤ 2 ^ 32) :
    serCode inst mi A ∗ A cw ↪[wf] FuncInst.wasm types[31]! inst f345 ∗
      A ck ↪[wf] FuncInst.wasm types[15]! inst (strFn ce) ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (keyFn cw a ck) Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ a.toNat ] [cb] ∗ keyIn n ser vec ptr cap w lo m p ds))
        (fun _ => 200 * cfg.regularOpCost + MemCpy.cost 1 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ a.toNat ] [cb] ∗ keyIn n ser vec ptr cap (w ++ [cb] ++ ([34] ++ ds ++ [34])) lo m p ds)) := by
  iintro ⟨#Hk, #Hcw, #Hck, #Hce⟩
  ihave #S := str_out (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg ce hce gt s ser
    vec ptr cap p k (w ++ [cb]) ds hs hds hk0 lo m hdig hser (by simp; omega) hp $$ [Hk Hce]
  · iframe Hk Hce
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hk; icases Hk with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #SW := wa_out (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s ser vec
    ptr cap a 1 w [cb] (by omega) rfl hser (by simp; omega) (by simpa using ha) $$ Happ
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hn := hm.mem
  have hack := hm.funcs ck hck
  have hacw := hm.funcs cw hcw
  have t15 : types[15]!.params.length = 3 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize hM : MemCpy.cost (UInt32.toNat 1) * cfg.regularOpCost = M
  rw [show MemCpy.cost 1 * cfg.regularOpCost = M by rw [← hM]; rfl]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcb, HK⟩
  subst hargs
  iunfold keyIn at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  simp only [keyFn]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  mcall SW using [Hg Hs16 Hser Ho Hcb]
  · iframe Hg Hs16 Hser Ho Hcb
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcb⟩
  subst hrs
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  ihave Hs16 := stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs := stk_join n (s.toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  have hloc : actSize ((strFn ce).locals.map ValType.default) = 0 := rfl
  mcall S using [Hg Hs Hq He Hser Ho Hds]
    with (mstep_norm_full; simp only [hloc, Nat.reduceAdd, Nat.reduceDiv] at *; omega)
  · iframe Hg Hs Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hq, He, Hser, Ho, Hds⟩
  subst hrs
  repeat mstep
  mstep_post
  simp only [hloc, Nat.reduceAdd, Nat.reduceDiv, show storeBytes (Value.i32 2) 1 = ([2] : List UInt8) from rfl]
  mcredits R
  iframe Hc Hg Hs Hcs Hst Hcb
  isplitr
  · ipureintro; simp [htype]
  iunfold keyIn
  iframe Hq He Hser Ho Hds

end Keys

/-! ## A `U128` value: `<U128 as Serialize>::serialize` (385) on `outV` -/

section Value

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.VecFromElem (roomFor grownLen)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.ToString (tsCode tsData cost385 f385_gen decDigits_all newCap_ge)
open WNear.Binary.SerializeStr (esc)

theorem esc_at (n : Nat) : (n ↦[wms][ 1061856 ] esc : IProp GF) ⊢ n ↦[wms][ 1061808 + 48 ] List.replicate 10 0 := .rfl
theorem esc_at' (n : Nat) : (n ↦[wms][ 1061808 + 48 ] List.replicate 10 0 : IProp GF) ⊢ n ↦[wms][ 1061856 ] esc := .rfl

/-- What `serialize_str` reads of the serializer: the quote, the digits' `ESCAPE` entries,
`*ser = vec` and the output. -/
def strIn (n : Nat) (ser vec ptr cap : UInt32) (w : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] esc ∗ n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<U128 as Serialize>::serialize(v, ser)`** (385) of the `u128` at `v` into `outV` with room:
`Ok`, its JSON string `"digits"` appended; the `String` freed (the free list one longer, the heap
grown by at most the `String`'s allocation). -/
theorem f385_out (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 25 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ser ptr0 aidx vec ptr cap : UInt32) (w : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hs : 400 ≤ s.toNat) (hv : v.toNat + 16 ≤ 2 ^ 32)
    (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi))))
    (hroom : w.length + (kOf (val lo hi)).toNat + 2 ≤ cap.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32)
    (F : Nat) (hF : okG F) :
    tsCode n maxP inst mi A ∗ serCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f385 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗
          tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut ∗ strIn n ser vec ptr cap w))
        (fun _ => cost385 cfg F lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗
          tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗
          (∃ hl', ⌜hl' = hl ∨ hl' = grownLen hl (newCap 0 (kOf (val lo hi)))⌝ ∗ heapInv n maxP hl' live (F + 1)) ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut ∗
          strIn n ser vec ptr cap (w ++ ([34] ++ decDigits (val lo hi) ++ [34])))) := by
  iintro ⟨#Hk, #Hs⟩
  have hlt := s.toNat_lt
  have hsp : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hK := FmtString.kOf_toNat lo hi
  have hL1 := FmtString.decDigits_le lo hi
  have hL2 := FmtDigits.decDigits_length_pos (val lo hi)
  have hk := newCap_ge (kOf (val lo hi))
  iunfold cost385
  iapply f385_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt s v ser ptr0 aidx maxP hl live lo hi hs hv hr
    (F := F) (hF := hF)
  iframe Hk
  imodintro
  iintro %q %⟨hq0, hqc⟩
  iapply AllocFresh.MFunSpec_frame (Fr := stk n ((s - 64).toNat - 336) 288)
    (P := fun args => iprop(⌜args = [.i32 ser, .i32 q, .i32 (kOf (val lo hi))]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 64)⟩ ∗
      stk n ((s - 64).toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗
      n ↦[wms][ 1061808 + 48 ] List.replicate 10 0 ∗ n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗
      n ↦[wms][ q.toNat ] decDigits (val lo hi)))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 64)⟩ ∗
      stk n ((s - 64).toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗
      n ↦[wms][ 1061808 + 48 ] List.replicate 10 0 ∗ n ↦[i32][ ser.toNat ] vec ∗
      outV n vec ptr cap (w ++ ([34] ++ decDigits (val lo hi) ++ [34])) ∗
      n ↦[wms][ q.toNat ] decDigits (val lo hi)))
  · intro args
    iintro ⟨%ha, Hg, Hb, Hds, HP⟩
    iunfold strIn at HP
    icases HP with ⟨Hq, He, Hser, Ho⟩
    icases stk_split n ((s - 64).toNat - 336) 288 48 $$ Hb with ⟨Hb1, Hb2⟩
    iframe Hb1
    isplitr; · ipureintro; exact ha
    iframe Hg Hq Hser Ho Hds
    isplitl [Hb2]
    · iapply stk_addr (show (s - 64).toNat - 336 + 288 = (s - 64).toNat - 48 by omega) $$ Hb2
    iapply esc_at n $$ He
  · intro args rs
    iintro ⟨Hb1, %hrs, Hg, Hb2, Hq, He, Hser, Ho, Hds⟩
    iframe Hg Hds
    isplitr; · ipureintro; exact hrs
    isplitl [Hb1 Hb2]
    · iapply stk_join n ((s - 64).toNat - 336) 288 48
      iframe Hb1
      iapply stk_addr (show (s - 64).toNat - 48 = (s - 64).toNat - 336 + 288 by omega) $$ Hb2
    iunfold strIn
    iframe Hq Hser Ho
    iapply esc_at' n $$ He
  rw [f383_eq]
  iapply str_out cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg 367 (by decide) gt (s - 64)
    ser vec ptr cap q (kOf (val lo hi)) w (decDigits (val lo hi)) (by omega) (by omega) (by omega) 48 10
    (SerializeStr.inRange_of_digits (decDigits_all _)) hser (by omega) (by omega)
  iframe Hs
  iunfold serCode at Hs
  icases Hs with ⟨-, -, -, #H367⟩
  iexact H367

/-- The code of a struct's `U128` and `Option<U128>` fields (persistent): `to_string`'s and
`serialize_str`'s, the key writers 382 and 173, `serialize_str` 176 and its 159, the pieces 347
and 99 and the `write_all` 98. -/
def fieldCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(tsCode n maxP inst mi A ∗ serCode inst mi A ∗ A 385 ↪[wf] FuncInst.wasm types[13]! inst f385 ∗
    A 382 ↪[wf] FuncInst.wasm types[15]! inst f382 ∗ A 173 ↪[wf] FuncInst.wasm types[15]! inst f173 ∗
    A 176 ↪[wf] FuncInst.wasm types[15]! inst f176 ∗ A 159 ↪[wf] FuncInst.wasm types[35]! inst f159 ∗
    A 347 ↪[wf] FuncInst.wasm types[0]! inst f347 ∗ A 99 ↪[wf] FuncInst.wasm types[0]! inst f99 ∗
    A 98 ↪[wf] FuncInst.wasm types[31]! inst f98)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (fieldCode (GF := GF) n maxP inst mi A) := by
  unfold fieldCode; infer_instance

/-- What a `U128` value's serialization reads (owned, returned), but the output: `to_string`'s
data, the allocator's vtable, the digit table. -/
def valIn (n ta : Nat) (A : Nat → Nat) (ptr0 aidx : UInt32) : IProp GF :=
  iprop(tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗ n ↦[wms][ 1070974 ] lut)

/-- The lowercase letters' entries of `ESCAPE` (at `1061808 + 97`): no escape. -/
abbrev escLower : List UInt8 := List.replicate 26 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's first field, a `U128`** (384: `serialize_field::<U128>` with the `Compound`'s state
`First`): the key `"ds"` (lowercase letters), `:` (at 1051834), the value's JSON string. -/
theorem f384_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 27 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s c ser p k v ptr0 aidx vec ptr cap : UInt32) (ds w : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hs : 400 ≤ s.toNat) (hc : c.toNat + 8 ≤ 2 ^ 32) (hv : v.toNat + 16 ≤ 2 ^ 32)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hdig : InRange 97 26 ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi))))
    (hroom : w.length + (k.toNat + 2) + 1 + ((kOf (val lo hi)).toNat + 2) ≤ cap.toNat)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (F : Nat) (hF : okG F) :
    fieldCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f384 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 400) 400 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [1] ∗
          n ↦[wms][ p.toNat ] ds ∗ n ↦[wms][ 1061808 + 97 ] escLower ∗ n ↦[wms][ 1051834 ] [58] ∗
          valIn n ta A ptr0 aidx ∗ heapInv n maxP hl live F ∗ n ↦[wms][ v.toNat ] u128Bytes lo hi ∗
          strIn n ser vec ptr cap w))
        (fun _ => 300 * cfg.regularOpCost + MemCpy.cost 1 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost +
          cost385 cfg F lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 400) 400 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ p.toNat ] ds ∗ n ↦[wms][ 1061808 + 97 ] escLower ∗ n ↦[wms][ 1051834 ] [58] ∗
          valIn n ta A ptr0 aidx ∗
          (∃ hl', ⌜hl' = hl ∨ hl' = grownLen hl (newCap 0 (kOf (val lo hi)))⌝ ∗ heapInv n maxP hl' live (F + 1)) ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗
          strIn n ser vec ptr cap (w ++ ([34] ++ ds ++ [34]) ++ [58] ++ ([34] ++ decDigits (val lo hi) ++ [34])))) := by
  iintro #Hk
  iunfold fieldCode at Hk
  icases Hk with ⟨#Hts, #Hsc, #H385, #H382, #H173, #H176, #H159, #H347, #H99, #H98⟩
  ihave #H383 : A 383 ↪[wf] FuncInst.wasm types[15]! inst f383 $$ []
  · iunfold tsCode at Hts; icases Hts with ⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩; iexact H
  ihave #H367 : A 367 ↪[wf] FuncInst.wasm types[35]! inst f367 $$ []
  · iunfold serCode at Hsc; icases Hsc with ⟨-, -, -, #H⟩; iexact H
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #H345 : A 345 ↪[wf] FuncInst.wasm types[31]! inst f345 $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨-, #H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hK := FmtString.kOf_toNat lo hi
  have S382 := keyFirst_out (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 345 383 367
    1051819 (by decide) (by decide) gt s c ser vec ptr cap p k w ds (by omega) hc hds hk0 97 26 hdig hser
    (by omega) hp
  rw [← f382_eq, ← f383_eq] at S382
  ihave #S382 := S382 $$ [Hsc H383 H367]
  · iframe Hsc H383 H367
  have S347 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 345 (by decide)
    1051834 gt s ser vec ptr cap (w ++ ([34] ++ ds ++ [34])) 58 (by omega) hser (by simp; omega) (by decide)
  rw [← f347_eq] at S347
  ihave #S347 := S347 $$ [Happ H345]
  · iframe Happ H345
  ihave #S385 := f385_out (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt s v ser
    ptr0 aidx vec ptr cap (w ++ ([34] ++ ds ++ [34]) ++ [58]) maxP hl live lo hi hs hv hr (by simp; omega) hser F hF
    $$ [Hts Hsc]
  · iframe Hts Hsc
  have hn := hm.mem
  have ha382 := hm.funcs 382 (by decide)
  have ha347 := hm.funcs 347 (by decide)
  have ha385 := hm.funcs 385 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize cost385 cfg F lo hi = C5
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hds, Hlow, Hcol, HV, Hh, Hv, HS⟩
  subst hargs
  iunfold strIn at HS
  icases HS with ⟨Hq, He, Hser, Ho⟩
  iunfold valIn at HV
  icases HV with ⟨HD, Hvt, Hl⟩
  icases stk_split n (s.toNat - 400) 352 48 $$ Hs with ⟨Hs352, Hs48⟩
  ihave Hs48 := stk_addr (show s.toNat - 400 + 352 = s.toNat - 48 by omega) $$ Hs48
  simp only [f384]
  repeat mstep
  mcall S382 using [Hg Hs48 Hcs Hst Hq Hlow Hser Ho Hds]
  · iframe Hg Hs48 Hcs Hst
    iunfold keyIn
    iframe Hq Hlow Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs48, Hcs, Hst, HK⟩
  subst hrs
  iunfold keyIn at HK
  icases HK with ⟨Hq, Hlow, Hser, Ho, Hds⟩
  repeat mstep
  mstep [Hcs]
  repeat mstep
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs48 with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  mcall S347 using [Hg Hs16 Hser Ho Hcol]
  · iframe Hg Hs16 Hser Ho Hcol
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  ihave Hs16 := stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs48 := stk_join n (s.toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  ihave Hs48 := stk_addr (show s.toNat - 48 = s.toNat - 400 + 352 by omega) $$ Hs48
  ihave Hs := stk_join n (s.toNat - 400) 352 48 $$ [Hs352 Hs48]
  · iframe Hs352 Hs48
  mcall S385 using [Hg Hs HD Hvt Hh Hv Hl Hq He Hser Ho]
  · iframe Hg Hs HD Hvt Hh Hv Hl
    iunfold strIn
    iframe Hq He Hser Ho
  icases HQ with ⟨%hrs, Hg, Hs, HD, Hvt, Hh, Hv, Hl, HS⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hs Hcs Hst Hds Hlow Hh Hv Hcol
  isplitr
  · ipureintro; simp [htype]
  iunfold valIn
  iframe HD Hvt Hl
  iexact HS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's later field, an `Option<U128>` holding `Some`** (109: `serialize_field::<Option<U128>>`
with the state `Rest`): `,` (at 1048759), the key `"ds"`, `:` (at 1048760), the value's JSON
string (the tag 1 at `v`, the `u128` at `v + 8`). -/
theorem f109_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 27 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s c ser p k v ptr0 aidx vec ptr cap : UInt32) (ds w : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hs : 400 ≤ s.toNat) (hc : c.toNat + 8 ≤ 2 ^ 32) (hv : v.toNat + 24 ≤ 2 ^ 32)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hdig : InRange 97 26 ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi))))
    (hroom : w.length + 1 + (k.toNat + 2) + 1 + ((kOf (val lo hi)).toNat + 2) ≤ cap.toNat)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (F : Nat) (hF : okG F) :
    fieldCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f109 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 400) 400 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ p.toNat ] ds ∗ n ↦[wms][ 1061808 + 97 ] escLower ∗ n ↦[wms][ 1048759 ] [44] ∗
          n ↦[wms][ 1048760 ] [58] ∗
          valIn n ta A ptr0 aidx ∗ heapInv n maxP hl live F ∗ n ↦[wms][ v.toNat ] storeBytes (.i64 1) 8 ∗
          n ↦[wms][ v.toNat + 8 ] u128Bytes lo hi ∗ strIn n ser vec ptr cap w))
        (fun _ => 500 * cfg.regularOpCost + 2 * (MemCpy.cost 1 * cfg.regularOpCost) +
          cost383 k.toNat * cfg.regularOpCost + cost385 cfg F lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 400) 400 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ p.toNat ] ds ∗ n ↦[wms][ 1061808 + 97 ] escLower ∗ n ↦[wms][ 1048759 ] [44] ∗
          n ↦[wms][ 1048760 ] [58] ∗ valIn n ta A ptr0 aidx ∗
          (∃ hl', ⌜hl' = hl ∨ hl' = grownLen hl (newCap 0 (kOf (val lo hi)))⌝ ∗ heapInv n maxP hl' live (F + 1)) ∗
          n ↦[wms][ v.toNat ] storeBytes (.i64 1) 8 ∗ n ↦[wms][ v.toNat + 8 ] u128Bytes lo hi ∗
          strIn n ser vec ptr cap
            (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58] ++ ([34] ++ decDigits (val lo hi) ++ [34])))) := by
  iintro #Hk
  iunfold fieldCode at Hk
  icases Hk with ⟨#Hts, #Hsc, #H385, #H382, #H173, #H176, #H159, #H347, #H99, #H98⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hK := FmtString.kOf_toNat lo hi
  have hlt := v.toNat_lt
  have h8 : (v + 8).toNat = v.toNat + 8 := by rw [UInt32.toNat_add]; simp; omega
  have S173 := keyRest_out (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg 98 176 159
    1048759 (by decide) (by decide) (by decide) 44 gt s c ser vec ptr cap p k w ds (by omega) hc hds hk0 97 26 hdig
    hser (by omega) hp (by decide)
  rw [← f173_eq, ← f176_eq, ← f98_eq, ← f159_eq] at S173
  ihave #S173 := S173 $$ [Hsc H98 H176 H159]
  · iframe Hsc H98 H176 H159
  have S99 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 98 (by decide)
    1048760 gt s ser vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34])) 58 (by omega) hser (by simp; omega) (by decide)
  rw [← f99_eq, ← f98_eq] at S99
  ihave #S99 := S99 $$ [Happ H98]
  · iframe Happ H98
  ihave #S385 := f385_out (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt s (v + 8)
    ser ptr0 aidx vec ptr cap (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58]) maxP hl live lo hi hs (by omega) hr
    (by simp; omega) hser F hF $$ [Hts Hsc]
  · iframe Hts Hsc
  have hn := hm.mem
  have ha173 := hm.funcs 173 (by decide)
  have ha99 := hm.funcs 99 (by decide)
  have ha385 := hm.funcs 385 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize cost385 cfg F lo hi = C5
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hds, Hlow, Hcom, Hcol, HV, Hh, Htag, Hv, HS⟩
  subst hargs
  iunfold strIn at HS
  icases HS with ⟨Hq, He, Hser, Ho⟩
  iunfold valIn at HV
  icases HV with ⟨HD, Hvt, Hl⟩
  icases stk_split n (s.toNat - 400) 352 48 $$ Hs with ⟨Hs352, Hs48⟩
  ihave Hs48 := stk_addr (show s.toNat - 400 + 352 = s.toNat - 48 by omega) $$ Hs48
  simp only [f109]
  repeat mstep
  mcall S173 using [Hg Hs48 Hcs Hst Hcom Hq Hlow Hser Ho Hds]
  · iframe Hg Hs48 Hcs Hst Hcom
    iunfold keyIn
    iframe Hq Hlow Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs48, Hcs, Hst, Hcom, HK⟩
  subst hrs
  iunfold keyIn at HK
  icases HK with ⟨Hq, Hlow, Hser, Ho, Hds⟩
  repeat mstep
  mstep [Hcs]
  repeat mstep
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs48 with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  mcall S99 using [Hg Hs16 Hser Ho Hcol]
  · iframe Hg Hs16 Hser Ho Hcol
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  mstep [Htag]
  repeat mstep
  ihave Hs16 := stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs48 := stk_join n (s.toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  ihave Hs48 := stk_addr (show s.toNat - 48 = s.toNat - 400 + 352 by omega) $$ Hs48
  ihave Hs := stk_join n (s.toNat - 400) 352 48 $$ [Hs352 Hs48]
  · iframe Hs352 Hs48
  ihave Hv := memBytes_addr (show v.toNat + 8 = (v + 8).toNat by omega) $$ Hv
  mcall S385 using [Hg Hs HD Hvt Hh Hv Hl Hq He Hser Ho]
  · iframe Hg Hs HD Hvt Hh Hv Hl
    iunfold strIn
    iframe Hq He Hser Ho
  icases HQ with ⟨%hrs, Hg, Hs, HD, Hvt, Hh, Hv, Hl, HS⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc Hg Hs Hcs Hst Hds Hlow Hcom Hcol Hh Htag
  isplitr
  · ipureintro; simp [htype]
  iunfold valIn
  iframe HD Hvt Hl
  isplitl [Hv]
  · iapply memBytes_addr (show (v + 8).toNat = v.toNat + 8 by omega) $$ Hv
  iexact HS

end Value

/-! ## The end of a struct (106) and `StorageBalanceBounds` (108) -/

section Struct

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.VecFromElem (roomFor grownLen)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.ToString (cost385)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`SerializeStruct::end`** (106) of a `Compound` whose state is not `Empty` (the byte 2): `}`
(at 1048744, through 97) appended; `Ok`. -/
theorem f106_end (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s ser vec ptr cap : UInt32) (w : List UInt8) (hs : 16 ≤ s.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32)
    (hroom : w.length + 1 ≤ cap.toNat) :
    VecAppend.appCode inst mi A ∗ A 97 ↪[wf] FuncInst.wasm types[0]! inst f97 ∗
      A 98 ↪[wf] FuncInst.wasm types[31]! inst f98
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f106 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 2]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗ n ↦[wms][ 1048744 ] [125]))
        (fun _ => 200 * cfg.regularOpCost + MemCpy.cost 1 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap (w ++ [125]) ∗ n ↦[wms][ 1048744 ] [125])) := by
  iintro ⟨#Happ, #H97, #H98⟩
  have S97 := piece_out (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg 98 (by decide)
    1048744 gt s ser vec ptr cap w 125 hs hser hroom (by decide)
  rw [← f97_eq, ← f98_eq] at S97
  ihave #S97 := S97 $$ [Happ H98]
  · iframe Happ H98
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have ha97 := hm.funcs 97 (by decide)
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize hM : MemCpy.cost 1 * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f106]
  repeat mstep
  mcall S97 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HP⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc HP
  ipureintro; simp [htype]

/-- The keys of `StorageBalanceBounds`: `min` (at 1048824) and `max` (at 1048827). -/
def keyMin : List UInt8 := [109, 105, 110]
def keyMax : List UInt8 := [109, 97, 120]

theorem keyMin_range : InRange 97 26 keyMin := by
  intro b hb; simp only [keyMin, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide
theorem keyMax_range : InRange 97 26 keyMax := by
  intro b hb; simp only [keyMax, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide

/-- A JSON string's bytes: the quotes around `ds`. -/
def jstr (ds : List UInt8) : List UInt8 := [34] ++ ds ++ [34]

/-- The JSON of `StorageBalanceBounds { min: a, max: Some(b) }`. -/
def boundsJson (a b : Nat) : List UInt8 :=
  [123] ++ jstr keyMin ++ [58] ++ jstr (decDigits a) ++ [44] ++ jstr keyMax ++ [58] ++ jstr (decDigits b) ++ [125]

/-- The data the struct serializer reads (owned, returned): the punctuation, the keys, the
lowercase letters' `ESCAPE` entries. -/
def boundsData (n : Nat) : IProp GF :=
  iprop(n ↦[wms][ 1048744 ] [125] ∗ n ↦[wms][ 1048758 ] [123] ∗ n ↦[wms][ 1048759 ] [44] ∗
    n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048824 ] keyMin ∗ n ↦[wms][ 1048827 ] keyMax ∗
    n ↦[wms][ 1051834 ] [58] ∗ n ↦[wms][ 1061808 + 97 ] escLower)

/-- The code of 108 (persistent). -/
def structCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(fieldCode n maxP inst mi A ∗ A 384 ↪[wf] FuncInst.wasm types[33]! inst f384 ∗
    A 109 ↪[wf] FuncInst.wasm types[33]! inst f109 ∗ A 106 ↪[wf] FuncInst.wasm types[13]! inst f106 ∗
    A 97 ↪[wf] FuncInst.wasm types[0]! inst f97)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (structCode (GF := GF) n maxP inst mi A) := by
  unfold structCode; infer_instance

/-- The cost of 108, activation excluded. -/
noncomputable def cost108 (cfg : WasmConfig) (F : Nat) (lo1 hi1 lo2 hi2 : UInt64) : Nat :=
  2500 * cfg.regularOpCost + 5 * (MemCpy.cost 1 * cfg.regularOpCost) + 2 * (cost383 3 * cfg.regularOpCost) +
    cost385 cfg F lo1 hi1 + cost385 cfg (F + 1) lo2 hi2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **`<StorageBalanceBounds as Serialize>::serialize(v, ser)`** (108) of `{ min, max: Some(_) }`
at `v` (the `u128` `(lo1, hi1)`, the tag 1, the `u128` `(lo2, hi2)`), into `outV` with room:
`Ok`, `boundsJson` of the two values appended; each value's `String` freed (the free list two
longer). A 16-byte frame, and 400 bytes for the fields below it. -/
theorem f108_bounds (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ser ptr0 aidx vec ptr cap : UInt32) (w : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo1 hi1 lo2 hi2 : UInt64) (hs : 416 ≤ s.toNat) (hv : v.toNat + 40 ≤ 2 ^ 32)
    (hr1 : roomFor hl maxP (newCap 0 (kOf (val lo1 hi1))))
    (hr2 : ∀ hl1, hl1 = hl ∨ hl1 = grownLen hl (newCap 0 (kOf (val lo1 hi1))) →
      roomFor hl1 maxP (newCap 0 (kOf (val lo2 hi2))))
    (hroom : w.length + 19 + (kOf (val lo1 hi1)).toNat + (kOf (val lo2 hi2)).toNat ≤ cap.toNat)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (F : Nat) (hF : okG F) :
    structCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f108 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
          boundsData n ∗ valIn n ta A ptr0 aidx ∗ heapInv n maxP hl live F ∗
          n ↦[wms][ v.toNat ] u128Bytes lo1 hi1 ∗ n ↦[wms][ v.toNat + 16 ] storeBytes (.i64 1) 8 ∗
          n ↦[wms][ v.toNat + 24 ] u128Bytes lo2 hi2 ∗ strIn n ser vec ptr cap w))
        (fun _ => cost108 cfg F lo1 hi1 lo2 hi2)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
          boundsData n ∗ valIn n ta A ptr0 aidx ∗ (∃ hl', heapInv n maxP hl' live (F + 2)) ∗
          n ↦[wms][ v.toNat ] u128Bytes lo1 hi1 ∗ n ↦[wms][ v.toNat + 16 ] storeBytes (.i64 1) 8 ∗
          n ↦[wms][ v.toNat + 24 ] u128Bytes lo2 hi2 ∗
          strIn n ser vec ptr cap (w ++ boundsJson (val lo1 hi1) (val lo2 hi2)))) := by
  iintro #Hk
  iunfold structCode at Hk
  icases Hk with ⟨#HF, #H384, #H109, #H106, #H97⟩
  ihave #HF' := HF
  iunfold fieldCode at HF'
  icases HF' with ⟨#Hts, #Hsc, -, -, -, -, -, -, -, #H98⟩
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hsc; icases Hsc with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hvl := v.toNat_lt
  have hK1 := FmtString.kOf_toNat lo1 hi1
  have hK2 := FmtString.kOf_toNat lo2 hi2
  have e16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by rw [UInt32.toNat_add, e16]; simp; omega
  have v16 : (v + 16).toNat = v.toNat + 16 := by rw [UInt32.toNat_add]; simp; omega
  -- the specifications of the calls
  have S98 := wa_out (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16) ser vec
    ptr cap 1048758 1 w [123] (by omega) rfl hser (by simp; omega) (by decide)
  rw [← f98_eq] at S98
  ihave #S98 := S98 $$ Happ
  ihave #S384 := f384_first (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048824 3 v ptr0 aidx vec ptr cap keyMin (w ++ [123]) maxP hl live lo1 hi1 (by omega)
    (by omega) (by omega) rfl (by decide) keyMin_range (by decide) hr1 (by simp; omega) hser F hF $$ HF
  ihave #S106 := f106_end (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16) ser
    vec ptr cap (w ++ [123] ++ ([34] ++ keyMin ++ [34]) ++ [58] ++ ([34] ++ decDigits (val lo1 hi1) ++ [34]) ++ [44] ++
      ([34] ++ keyMax ++ [34]) ++ [58] ++ ([34] ++ decDigits (val lo2 hi2) ++ [34])) (by omega) hser
    (by simp [keyMin, keyMax]; omega) $$ [Happ H97 H98]
  · iframe Happ H97 H98
  have ha98 := hm.funcs 98 (by decide)
  have ha384 := hm.funcs 384 (by decide)
  have ha109 := hm.funcs 109 (by decide)
  have ha106 := hm.funcs 106 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t33 : types[33]!.params.length = 4 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  unfold cost108
  generalize hM : MemCpy.cost (UInt32.toNat 1) * cfg.regularOpCost = M
  rw [show MemCpy.cost 1 * cfg.regularOpCost = M by rw [← hM]; rfl]
  generalize hC : cost383 (UInt32.toNat 3) * cfg.regularOpCost = C3
  rw [show cost383 3 * cfg.regularOpCost = C3 by rw [← hC]; rfl]
  generalize cost385 cfg F lo1 hi1 = C51
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HB, HV, Hh, Hv0, Hv16, Hv24, HS⟩
  subst hargs
  iunfold boundsData at HB
  icases HB with ⟨Hrb, Hlb, Hcom, Hcol2, Hmin, Hmax, Hcol, Hlow⟩
  iunfold strIn at HS
  icases HS with ⟨Hq, He, Hser, Ho⟩
  icases stk_split n (s.toNat - 416) 400 16 $$ Hs with ⟨Hlo, Hfr⟩
  icases stk_split n (s.toNat - 416 + 400) 8 8 $$ Hfr with ⟨F0, F8⟩
  icases stk_split n (s.toNat - 416 + 400 + 8) 4 4 $$ F8 with ⟨W8, B12⟩
  icases stk_split n (s.toNat - 416 + 400 + 8 + 4) 1 3 $$ B12 with ⟨B12, B13⟩
  iunfold stk at W8 B12
  icases W8 with ⟨%wb, %hwb, W8⟩
  icases B12 with ⟨%bb, %hbb, B12⟩
  ihave W8 := memBytes_addr (show s.toNat - 416 + 400 + 8 = (s - 16).toNat + 8 by omega) $$ W8
  ihave B12 := memBytes_addr (show s.toNat - 416 + 400 + 8 + 4 = (s - 16).toNat + 12 by omega) $$ B12
  icases stk_split n (s.toNat - 416) 384 16 $$ Hlo with ⟨Hlo, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 416 + 384 = (s - 16).toNat - 16 by omega) $$ Hs16
  simp only [f108]
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
  -- the first field, `min`
  ihave W8 := memBytes_addr (show (s - 16).toNat + 8 = (s - 16 + 8).toNat by omega) $$ W8
  ihave B12 := memBytes_addr (show (s - 16).toNat + 12 = (s - 16 + 8).toNat + 4 by omega) $$ B12
  ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = s.toNat - 416 + 384 by omega) $$ Hs16
  ihave Hlo := stk_join n (s.toNat - 416) 384 16 $$ [Hlo Hs16]
  · iframe Hlo Hs16
  ihave Hlo := stk_addr (show s.toNat - 416 = (s - 16).toNat - 400 by omega) $$ Hlo
  mcall S384 using [Hg Hlo W8 B12 Hmin Hlow Hcol HV Hh Hv0 Hq He Hser Ho]
  · iframe Hg Hlo W8 Hmin Hlow Hcol HV Hh Hv0
    isplitl [B12]
    · rw [show storeBytes (Value.i32 1) 1 = ([1] : List UInt8) from rfl]; iexact B12
    iunfold strIn
    iframe Hq He Hser Ho
  icases HQ with ⟨%hrs, Hg, Hlo, W8, B12, Hmin, Hlow, Hcol, HV, ⟨%hl1, %hhl1, Hh⟩, Hv0, HS⟩
  subst hrs
  repeat mstep
  -- the second field, `max`
  have S109 := f109_some (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) ser 1048827 3 (v + 16) ptr0 aidx vec ptr cap keyMax
    (w ++ 123 :: 34 :: (keyMin ++ 34 :: 58 :: 34 :: (decDigits (val lo1 hi1) ++ [34]))) maxP hl1 live lo2 hi2
    (by omega) (by omega) (by omega) rfl (by decide) keyMax_range (by decide) (hr2 hl1 hhl1)
    (by simp [keyMin, keyMax]; omega) hser (F + 1) (by unfold okG; omega)
  have hM' : MemCpy.cost 1 * cfg.regularOpCost = M := by rw [← hM]; rfl
  have hC' : cost383 3 * cfg.regularOpCost = C3 := by rw [← hC]; rfl
  simp only [hM, hM', hC, hC'] at S109
  ihave #S109 := S109 $$ HF
  mcall S109 using [Hg Hlo W8 B12 Hmax Hlow Hcom Hcol2 HV Hh Hv16 Hv24 HS]
  · iframe Hg Hlo W8 B12 Hmax Hlow Hcom Hcol2 HV Hh
    isplitl [Hv16]
    · iapply memBytes_addr (show v.toNat + 16 = (v + 16).toNat by omega) $$ Hv16
    isplitl [Hv24]
    · iapply memBytes_addr (show v.toNat + 24 = (v + 16).toNat + 8 by omega) $$ Hv24
    iexact HS
  icases HQ with ⟨%hrs, Hg, Hlo, W8, B12, Hmax, Hlow, Hcom, Hcol2, HV, ⟨%hl2, -, Hh⟩, Hv16, Hv24, HS⟩
  subst hrs
  repeat mstep
  -- the end, `}`
  ihave W8 := memBytes_addr (show (s - 16 + 8).toNat = (s - 16).toNat + 8 by omega) $$ W8
  ihave B12 := memBytes_addr (show (s - 16 + 8).toNat + 4 = (s - 16).toNat + 12 by omega) $$ B12
  mstep [W8]
  repeat mstep
  mstep [B12]
  repeat mstep
  icases stk_split n ((s - 16).toNat - 400) 384 16 $$ Hlo with ⟨Hlo, Hs16⟩
  ihave Hs16 := stk_addr (show (s - 16).toNat - 400 + 384 = (s - 16).toNat - 16 by omega) $$ Hs16
  iunfold strIn at HS
  icases HS with ⟨Hq, He, Hser, Ho⟩
  simp only [show loadValue NumType.i32 (some { bits := 8, signed := false }) (Memory.decodeLE [2]) = Value.i32 2 from rfl]
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
  iframe Hc Hg HV Hv0
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hlo Hs16 F0 W8 B12 B13]
  · ihave Hs16 := stk_addr (show (s - 16).toNat - 16 = (s - 16).toNat - 400 + 384 by omega) $$ Hs16
    ihave Hlo := stk_join n ((s - 16).toNat - 400) 384 16 $$ [Hlo Hs16]
    · iframe Hlo Hs16
    ihave Hlo := stk_addr (show (s - 16).toNat - 400 = s.toNat - 416 by omega) $$ Hlo
    ihave W8 := stk_word n _ ser $$ W8
    ihave B12 := ReadRegister.stk_bytes n _ [2] 1 rfl $$ B12
    iapply stk_join n (s.toNat - 416) 400 16
    iframe Hlo
    iapply stk_join n (s.toNat - 416 + 400) 8 8
    iframe F0
    iapply stk_join n (s.toNat - 416 + 400 + 8) 4 4
    isplitl [W8]
    · iapply stk_addr (show (s - 16).toNat + 8 = s.toNat - 416 + 400 + 8 by omega) $$ W8
    iapply stk_join n (s.toNat - 416 + 400 + 8 + 4) 1 3
    iframe B13
    iapply stk_addr (show (s - 16).toNat + 12 = s.toNat - 416 + 400 + 8 + 4 by omega) $$ B12
  isplitl [Hrb Hlb Hcom Hcol2 Hmin Hmax Hcol Hlow]
  · iunfold boundsData
    iframe Hrb Hlb Hcom Hcol2 Hmin Hmax Hcol Hlow
  isplitl [Hh]
  · iexists hl2
    rw [show F + 2 = F + 1 + 1 by omega]
    iexact Hh
  isplitl [Hv16]
  · iapply memBytes_addr (show (v + 16).toNat = v.toNat + 16 by omega) $$ Hv16
  isplitl [Hv24]
  · iapply memBytes_addr (show (v + 16).toNat + 8 = v.toNat + 24 by omega) $$ Hv24
  iunfold strIn
  iframe Hq He Hser
  iapply outV_eq (by simp [boundsJson, jstr]) $$ Ho

end Struct

end WNear.Binary.SerdeStruct
