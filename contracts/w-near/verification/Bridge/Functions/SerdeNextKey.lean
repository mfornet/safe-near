import Bridge.Functions.SerdeValueSeed
import Bridge.Functions.SerdeKey

/-!
# serde's `next_key_seed` for `ft_balance_of`'s struct: 193 (M6)

`MapAccess::next_key_seed` (193) reads the next key of the object, or its end. The map access at
`acc` is the `Deserializer` pointer `de` and the `first` byte at `acc + 4`.

```wat
;; 193 (acc) → i64        ws (339); None → EofWhileParsingObject (3)
;;   '}'                  → Ok(None) (512)
;;   ',' with first = 0   → eat (333), ws; None → EofWhileParsingValue (5); else the byte below
;;   ',' with first = 1   → the byte below (KeyMustBeAString)
;;   another byte, first = 0 → ExpectedObjectCommaOrEnd (8); first = 1 → first := 0, the byte below
;;   the byte: '"' → eat (333), clear the scratch (82), parse_str (646) into the frame;
;;                   Err → its box; Ok(&key) → the field visitor (194): Ok(Some(field)) (0 or 256)
;;             '}' → TrailingComma (18); else KeyMustBeAString (16)
```

The result is `Result<Option<__Field>>` packed in an `i64`: bit 0 the `Err` tag (the box in the
high word), and bits 8..9 the option: 0 for `account_id`, 1 (256) for any other key, 2 (512) for
`None`.

This file proves the accepting cases, the ones a run that `fromSlice` accepts goes through (the
rejecting ones are ruled out by `SerdeStructModel.fromSlice_eq` on such a run):

* `f193_end`: `}` after the whitespace gives `Ok(None)`, the reader at the `}` (not eaten);
* `f193_key`: a key, after `first = 1`, or `first = 0` and a `,` (`keyQ`). The key goes through
  `parse_str` (646), taken as a hypothesis `H646`: its `Ok` reference `(p, |kb|)` to the key's
  bytes `kb`, with the points-to `p ↦ kb` lent to 194 and given back by a wand. The escape-free
  instance, from `ParseStrErr.f646_spec_noesc`, is `f646_key_noesc`.

With `j = i + wsLen (bs.drop i)`, the cost of the key case is `(400 + 96·(w + w') + cost194)·c` plus
646's `K646`, `w'` the whitespace after the `,`.
-/

namespace WNear.Binary.SerdeNextKey

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit byte_is125 byte_is44 byte_is34)

/-- Where the key's body starts, on the accepting paths of 193: after the whitespace, `"` (when
`first`), or `,`, whitespace, then `"` (when not `first`). -/
def keyQ (first : Bool) (bs : List UInt8) (i : Nat) : Option Nat :=
  if first then
    if bs[i + wsLen (bs.drop i)]? = some 0x22 then some (i + wsLen (bs.drop i) + 1) else none
  else if bs[i + wsLen (bs.drop i)]? = some 0x2C then
    if bs[i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1))]? = some 0x22 then
      some (i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) + 1)
    else none
  else none

/-- The whitespace 193 skips on the way to a key. -/
def keyWs (first : Bool) (bs : List UInt8) (i : Nat) : Nat :=
  if first then wsLen (bs.drop i)
  else wsLen (bs.drop i) + wsLen (bs.drop (i + wsLen (bs.drop i) + 1))

/-- The field visitor's answer for the key bytes `kb`, as 193 packs it. -/
def fieldOf (kb : List UInt8) : UInt64 := if kb = WNear.BalanceOfArgs.keyBytes then 0 else 256

theorem f82_eq : f82 = f343 := rfl

section L193

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 193 runs on its accepting paths (persistent). -/
def code193 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(endCode n maxP inst mi A ∗ A 82 ↪[wf] FuncInst.wasm types[0]! inst f82 ∗
    A 674 ↪[wf] FuncInst.wasm types[14]! inst f674 ∗ A 646 ↪[wf] FuncInst.wasm types[31]! inst f646 ∗
    A 194 ↪[wf] FuncInst.wasm types[30]! inst f194 ∗ A 754 ↪[wf] FuncInst.wasm types[33]! inst f754 ∗
    A 755 ↪[wf] FuncInst.wasm types[33]! inst f755 ∗ A 953 ↪[wf] FuncInst.wasm types[15]! inst f953)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (code193 (GF := GF) n maxP inst mi A) := by
  unfold code193; infer_instance

/-- The specification of `parse_str` (646) that 193 needs at a key whose body starts at `q`: called
with the frame `out` of 193, the reader at `q` and the scratch's length 0, it returns `Ok` with a
reference `(p, |kb|)` to the key's bytes `kb`, whose points-to it lends (the wand gives `Q646` back
for it). `P646` and `Q646` carry the rest of its state (the heap, the tables, the reader after). -/
def Spec646 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (Cg : Nat) (gt : GlobalType) (sp de ptr : UInt32) (ob bs : List UInt8) (q : Nat) (kb : List UInt8)
    (P646 : IProp GF) (K646 : Nat) (Q646 : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[31]! inst mi f646 Cg
    (fun args => iprop(⌜args = [.i32 (sp - 16), .i32 de, .i32 (de + 12)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
      stk n (sp.toNat - 176) 160 ∗ n ↦[wms][ (sp - 16).toNat ] ob ∗ rd n de ptr bs q ∗
      n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗ P646))
    (fun _ => K646)
    (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n (sp.toNat - 176) 160 ∗
      ∃ (t p : UInt32), ⌜p.toNat + kb.length ≤ 2 ^ 32 ∧ kb.length < 2 ^ 32⌝ ∗
        n ↦[i32][ (sp - 16).toNat ] 0 ∗ n ↦[i32][ (sp - 16).toNat + 4 ] t ∗
        n ↦[i32][ (sp - 16).toNat + 8 ] p ∗ n ↦[i32][ (sp - 16).toNat + 12 ] (UInt32.ofNat kb.length) ∗
        n ↦[wms][ p.toNat ] kb ∗ (n ↦[wms][ p.toNat ] kb -∗ Q646)))

theorem end_bits (x : UInt32) : (((0 : UInt64) ||| 512) ||| (x.toUInt64 <<< (32 : UInt64))) &&& 65281 = 512 := by
  bv_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **193 at the object's end**: `}` after the whitespace. `Ok(None)` (the option bits 512), the
reader at the `}`, which `end_map` (90) eats. -/
theorem f193_end (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp acc de ptr : UInt32) (fb : UInt8) (bs : List UInt8) (i : Nat)
    (maxP : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 176 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hb : bs[i + wsLen (bs.drop i)]? = some 0x7D) :
    code193 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f193 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [fb] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 176 ∗ rd n de ptr bs i))
        (fun _ => (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜∃ v : UInt64, rs = [.i64 v] ∧ v &&& 65281 = 512⌝ ∗
          n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [fb] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 176 ∗ rd n de ptr bs (i + wsLen (bs.drop i)))) := by
  iintro #Hv
  iunfold code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  iunfold endCode at Hv
  icases Hv with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hfb, Hg, Hs, Hrd⟩
  subst hargs
  have hlt := sp.toNat_lt
  generalize hw : wsLen (bs.drop i) = w at hb
  generalize hj : i + w = j at hb
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  rw [show (200 + 96 * w) * cfg.regularOpCost + R =
    100 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + R) by simp only [Nat.add_mul]; omega]
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W
  simp only [f193]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mstep [Hacc]
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, hj, hW] at key
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (70 * cfg.regularOpCost + R)
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb]
  have hok1 : Numeric.bool (optByte (some 0x7D) &&& 1 == 0) = 1 := by decide
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hacc Hfb Hg Hs Hrd
  ipureintro
  exact ⟨_, by simp [htype], end_bits acc⟩

theorem getElem_lt {bs : List UInt8} {j : Nat} {b : UInt8} (h : bs[j]? = some b) : j < bs.length := by
  by_contra h'; rw [List.getElem?_eq_none (by omega)] at h; simp at h


instance (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (Cg : Nat) (gt : GlobalType) (sp de ptr : UInt32) (ob bs : List UInt8) (q : Nat) (kb : List UInt8)
    (P646 : IProp GF) (K646 : Nat) (Q646 : IProp GF) :
    Persistent (Spec646 cfg lim d inst mi n g Cg gt sp de ptr ob bs q kb P646 K646 Q646) := by
  unfold Spec646; infer_instance

theorem store0 (n a : Nat) : n ↦[wms][ a ] (storeBytes (.i32 0) 1) ⊢ (n ↦[wms][ a ] [0] : IProp GF) := by
  have : MemSet.byteOf 0 = 0 := by decide
  rw [MemSet.storeBytes_i32_1, this]

set_option hygiene false in
/-- The key block of 193, from its `block`s to the end of the function: the quote at `jq`, eaten;
the scratch cleared (82); `parse_str` (646, `S646`); the field visitor (194) on its reference. -/
local macro "key_tail" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep [Hacc]; mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs jq (getElem_lt hq1)
    (by omega) (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (150 * cfg.regularOpCost + (K646 + (C194 + R)))
  mstep; mstep; mstep; mstep
  mcall S82 using [Hsc]
  · iframe Hsc
  icases HQ with ⟨%hrs, Hsc⟩
  subst hrs
  mcredits (100 * cfg.regularOpCost + (K646 + (C194 + R)))
  mstep; mstep; mstep
  mcall S646 using [Hg H160 Hob Hrd Hsc HP]
  · iframe Hg H160 Hob Hrd Hsc HP
  icases HQ with ⟨%hrs, Hg, H160, %t, %p, %⟨hp, hkl⟩, O0, O4, O8, O12, Hk, Hw⟩
  subst hrs
  mcredits (60 * cfg.regularOpCost + (C194 + R))
  mstep; mstep; mstep [O0]; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep [O8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  have s194 := SerdeKey.f194_spec (GF := GF) cfg lim (d + 1) types[30]! (by rfl) inst mi n hn (A 754) (A 755) (A 953)
    (hm.funcs 754 (by decide)) (hm.funcs 755 (by decide)) (hm.funcs 953 (by decide)) (by omega) Cg p
    (UInt32.ofNat kb.length) kb (by simp; omega) (by simp; omega)
  rw [hC194] at s194
  ihave #S194 := s194 $$ [F754 F755 F953 Hi]
  · iframe F754 F755 F953 Hi
  clear s194
  mcall S194 using [Hk Hkey]
  · iframe Hk Hkey
  icases HQ with ⟨%hrs, Hk, Hkey⟩
  subst hrs
  mcredits (30 * cfg.regularOpCost + R)
  ihave HQ := Hw $$ Hk
  have hf : (if kb = WNear.BalanceOfArgs.keyBytes then (0 : UInt64) else 256) &&& 1 = 0 := by split <;> decide
  mstep; mstep; mstep
  rw [hf]
  mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hacc Hg Hkey HQ
  isplitr
  · ipureintro
    rw [htype]
    simp only [fieldOf]
    split <;> decide
  isplitl [Hfb]
  · first | iexact Hfb | (iapply store0; iexact Hfb)
  ihave O0 := stk_word $$ O0
  ihave O4 := stk_word $$ O4
  ihave O8 := stk_word $$ O8
  ihave O12 := stk_word $$ O12
  ihave F16 := VecFromElem.stk16_join n (sp - 16).toNat $$ [O0 O4 O8 O12]
  · iframe O0 O4 O8 O12
  ihave F16 := stk_addr (show (sp - 16).toNat = sp.toNat - 176 + 160 by omega) $$ F16
  iapply stk_join n (sp.toNat - 176) 160 16
  iframe H160 F16))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **193 at a key**: after `first = 1`, or `first = 0` and a `,` (`keyQ first bs i = some q`), the
key's body starts at `q`; `parse_str` (646) there is the hypothesis `Spec646` for the key's bytes
`kb`. The result is `Ok(Some(field))`, `fieldOf kb` (0 for `account_id`, 256 for any other key),
`first` cleared, and 646's `Q646`. -/
theorem f193_key (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp acc de ptr : UInt32) (first : Bool) (ob bs kb : List UInt8) (i q : Nat) (x : UInt32)
    (maxP : Nat) (hob : ob.length = 16)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 176 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hq : keyQ first bs i = some q) (P646 : IProp GF) (K646 : Nat) (Q646 : IProp GF) :
    code193 n maxP inst mi A ∗ Spec646 cfg lim (d + 1) inst mi n g Cg gt sp de ptr ob bs q kb P646 K646 Q646 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f193 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [if first then 1 else 0] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 160 ∗ n ↦[wms][ (sp - 16).toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[i32][ (de + 12).toNat + 8 ] x ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ P646))
        (fun _ => (572 + 96 * keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost + K646)
        (fun _ rs => iprop(⌜rs = [.i64 (fieldOf kb)]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [0] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 176 ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ Q646)) := by
  iintro ⟨#Hv, #S646⟩
  iunfold Spec646 at S646
  iunfold code193 at Hv
  icases Hv with ⟨#Hv, #F82, #F674, #F646, #F194, #F754, #F755, #F953⟩
  iunfold endCode at Hv
  icases Hv with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha82 := hm.funcs 82 (by decide)
  have ha646 := hm.funcs 646 (by decide)
  have ha194 := hm.funcs 194 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t30 : types[30]!.params.length = 2 := by rfl
  have s82 := SerdeDeStr.f343_s (GF := GF) cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg
    (de + 12) x (by simp [UInt32.toNat_add]; omega)
  rw [← f82_eq] at s82
  ihave #S82 := s82 $$ [F674 Hi]
  · iframe F674 Hi
  clear s82
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hfb, Hg, H160, Hob, Hrd, Hsc, Hkey, HP⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  generalize hC194 : SerdeKey.cost194 * cfg.regularOpCost = C194
  simp only [f193]
  unfold keyQ at hq
  simp only [keyWs]
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  generalize hw : wsLen (bs.drop i) = w at hq key ⊢
  generalize hj : i + w = j at hq key
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W at key
  cases first with
  | true =>
    simp only [if_true] at hq ⊢
    split at hq
    · rename_i hb
      simp only [Option.some.injEq] at hq
      subst hq
      rw [show (572 + 96 * w + SerdeKey.cost194) * cfg.regularOpCost + K646 + R =
        120 * cfg.regularOpCost + (W + (352 * cfg.regularOpCost + (K646 + (C194 + R)))) by
          rw [← hW, ← hC194]; simp only [Nat.add_mul]; omega]
      mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
      mstep; mstep; mstep; mstep; mstep
      mstep [Hacc]
      mcall key using [Hrd]
      · iframe Hrd
      clear key
      mcredits (260 * cfg.regularOpCost + (K646 + (C194 + R)))
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      rw [hb]
      mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      rw [SerdeRead.optByte_byte]
      mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep [Hfb]; mstep
      mstep_not_taken with decide
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep [Hfb]
      mstep
      have hq1 := hb
      generalize hjq : j = jq at hq1 hjl ⊢
      key_tail
    · simp at hq
  | false =>
    simp only [Bool.false_eq_true, if_false] at hq ⊢
    split at hq
    · rename_i hb
      have hjlt := getElem_lt hb
      have key2 := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
        (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs (j + 1) (by omega) (by omega)
        (by omega) (by omega)
      generalize hw2 : wsLen (bs.drop (j + 1)) = w2 at hq key2 ⊢
      generalize hW2 : (100 + 96 * w2) * cfg.regularOpCost = W2 at key2
      have hj2l : j + 1 + w2 ≤ bs.length := by
        have := SerdeRead.wsLen_le (bs.drop (j + 1)); simp at this; omega
      split at hq
      · rename_i hb2
        simp only [Option.some.injEq] at hq
        subst hq
        rw [show (572 + 96 * (w + w2) + SerdeKey.cost194) * cfg.regularOpCost + K646 + R =
          120 * cfg.regularOpCost + (W + (82 * cfg.regularOpCost + (W2 + (170 * cfg.regularOpCost +
            (K646 + (C194 + R)))))) by
            rw [← hW, ← hW2, ← hC194]; simp only [Nat.add_mul, Nat.mul_add]; omega]
        mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
        mstep; mstep; mstep; mstep; mstep
        mstep [Hacc]
        mcall key using [Hrd]
        · iframe Hrd
        clear key
        mcredits (180 * cfg.regularOpCost + (W2 + (170 * cfg.regularOpCost + (K646 + (C194 + R)))))
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        rw [hb]
        mstep; mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        rw [SerdeRead.optByte_byte]
        mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep_not_taken with decide
        mstep; mstep [Hfb]
        mstep_not_taken with decide
        mstep; mstep [Hacc]
        mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j hjlt
          (by omega) (by omega)) using [Hrd]
        · iframe Hrd
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        mcredits (100 * cfg.regularOpCost + (W2 + (170 * cfg.regularOpCost + (K646 + (C194 + R)))))
        mstep; mstep [Hacc]
        mcall key2 using [Hrd]
        · iframe Hrd
        clear key2
        mcredits (250 * cfg.regularOpCost + (K646 + (C194 + R)))
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        rw [hb2]
        mstep; mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep
        mstep_not_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep
        (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
        have hq1 := hb2
        have hjl' := hj2l
        generalize hjq : j + 1 + w2 = jq at hq1 hjl' ⊢
        key_tail
      · simp at hq
    · simp at hq

/-- The bytes `body` of the input at `q` lent out of the reader, and given back. -/
theorem rd_lend (n : Nat) (de ptr : UInt32) (bs body tail : List UInt8) (k q : Nat)
    (h : bs.drop q = body ++ tail) (hq : q ≤ bs.length) :
    rd (GF := GF) n de ptr bs k ⊢
      n ↦[wms][ ptr.toNat + q ] body ∗ (n ↦[wms][ ptr.toNat + q ] body -∗ rd n de ptr bs k) := by
  iintro H
  iunfold rd at H
  icases H with ⟨Hs, Hb⟩
  icases U128From.memBytes_split n ptr.toNat q bs hq $$ Hb with ⟨H1, H2⟩
  ihave H2 := AllocNewCell.memBytes_eq h $$ H2
  icases U128From.memBytes_split n (ptr.toNat + q) body.length (body ++ tail) (by simp) $$ H2 with ⟨H2, H3⟩
  rw [List.take_left' rfl, List.drop_left' rfl]
  iframe H2
  iintro H2
  iunfold rd
  iframe Hs
  ihave H2 := U128From.memBytes_join n (ptr.toNat + q) body.length body tail rfl $$ [H2 H3]
  · iframe H2 H3
  ihave H2 := AllocNewCell.memBytes_eq h.symm $$ H2
  ihave H := U128From.memBytes_join n ptr.toNat q (bs.take q) (bs.drop q) (by simp; omega) $$ [H1 H2]
  · iframe H1 H2
  rw [List.take_append_drop]
  iexact H

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Spec646` from `ParseStrErr.f646_spec_noesc`**, for a key without escapes that 646 accepts
(`ok646 body tail`): the reference is `(ptr + q, |body|)`, into the input, and its bytes are lent
out of the reader. `P646` is the heap and the two tables; `Q646` adds the cleared scratch and the
reader past the closing quote. -/
theorem f646_key_noesc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (ob bs body tail : List UInt8) (q : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 176 ≤ sp.toNat) (hq : q ≤ bs.length)
    (hsplit : bs.drop q = body ++ tail) (hplain : ∀ b ∈ body, ParseStr.plain b = true)
    (hstop : ∀ x rest, tail = x :: rest → ParseStr.plain x = false ∧ x ≠ 0x5C)
    (hok : ParseStr.ok646 body tail) (hr : roomFor4 mlen maxP 20) :
    errCode n maxP inst mi A ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗
      A 657 ↪[wf] FuncInst.wasm types[31]! inst f657 ∗ A 647 ↪[wf] FuncInst.wasm types[31]! inst f647 ∗
      A 648 ↪[wf] FuncInst.wasm types[45]! inst f648 ⊢
      Spec646 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs q body
        iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width)
        (ParseStr.cost646 cfg F q body tail)
        iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗
          rd n de ptr bs (q + body.length + 1)) := by
  iintro H
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have s := ParseStr.f646_spec_noesc (GF := GF) cfg lim d types[31]! (by rfl) inst mi A n g ta hm hd Cg gt
    (sp - 16) (sp - 16) de (de + 12) ptr idx ob bs body tail q maxP mlen live F hob (by omega) (by omega)
    (by omega) (by omega) (by simp [UInt32.toNat_add]; omega) (by omega) hq hsplit hplain hstop hr
  rw [show (sp - 16).toNat - 160 = sp.toNat - 176 by omega] at s
  ihave #S := s $$ H
  clear s
  iunfold Spec646
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 (sp - 16), .i32 de, .i32 (de + 12)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          stk n (sp.toNat - 176) 160 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ (sp - 16).toNat ] ob ∗ rd n de ptr bs q ∗
          n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n (sp.toNat - 176) 160 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          ParseStr.res646 n maxP mlen live F (sp - 16) de ptr ob bs body tail q)) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hs, Ho, Hrd, Hsc, Hvt, Hh, He, Hw⟩
    iframe Hg Hs Ho Hrd Hsc Hvt Hh He Hw
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨-, %hrs, Hg, Hs, Hvt, Hsc, He, Hw, HR⟩
    iunfold ParseStr.res646 at HR
    rw [if_pos hok]
    iframe Hg Hs
    isplitr
    · ipureintro; exact hrs
    icases HR with ⟨Hh, O0, O4, O8, O12, Hrd⟩
    have hbl : body.length ≤ bs.length - q := by
      have := congrArg List.length hsplit; simp at this; omega
    have hpq : (ptr + UInt32.ofNat q).toNat = ptr.toNat + q := by
      simp [UInt32.toNat_add]; omega
    ihave Hl := rd_lend n de ptr bs body tail (q + body.length + 1) q hsplit hq $$ Hrd
    icases Hl with ⟨Hk, Hw2⟩
    iexists 0
    iexists ptr + UInt32.ofNat q
    rw [hpq]
    iframe O0 O4 O8 O12 Hk
    isplitr
    · ipureintro; omega
    iintro Hk
    ihave Hrd := Hw2 $$ Hk
    iframe Hvt Hh He Hw Hsc Hrd
  iexact S

end L193

end WNear.Binary.SerdeNextKey
