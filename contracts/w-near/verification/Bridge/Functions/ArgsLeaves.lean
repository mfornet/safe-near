import Bridge.Functions.StorageReadWrap

/-!
# The leaves of a method's argument prologue (M6)

Every method with arguments starts, after the environment, with

```wat
;; sp0 = sp - frame
input(sp0 + 88)                                   ;; 527 (EnvInput.lean): Option<Vec<u8>>
expect(sp0 + 48, sp0 + 88, 1050984)               ;; 157: the Vec, "Failed to read the input"
deref(sp0 + 24, sp0 + 48)                         ;; 779 (VecDeref.lean): the slice (ptr, len)
from_slice(sp0 + 88, [sp0 + 24], [sp0 + 28])       ;; 65 for ft_balance_of: Result<Args, Error>

;; 157 Option<Vec<u8>>::expect(out, opt, loc)
[opt] = 0 → panic(1050700, 42, loc)                ;; 879 (not covered: `input` is always Some)
out := [opt .. opt + 12]

;; 65 from_slice(out, ptr, len)
sp -= 16
SliceRead::new(sp, ptr, len)                      ;; 644: (ptr, len, index 0) at sp
from_trait(out, sp)                               ;; 66: the deserializer, the struct, `end`
sp += 16

;; 644 SliceRead::new(out, ptr, len)
[out + 8] := 0;  [out + 4] := len;  [out] := ptr
```

* `f157_spec`: `Option::<Vec<u8>>::expect` on `Some`: the three words copied (as 498,
  `StorageReadWrap.f498_spec`, with the message fixed).
* `f644_spec`: `SliceRead::new`: the slice and the index 0.
* `f65_of_66`: `from_slice` from any specification of `from_trait` (66) on the `SliceRead`
  644 builds, in a 16-byte frame: 66's pre- and postcondition, with 16 more bytes of stack
  and 45 more `regular_op_cost`s (its 13 instructions, 644 and its activation, 66's activation).
-/

namespace WNear.Binary.ArgsLeaves

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)

/-! ## `Option::expect` (157) on `Some` -/

section L157

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre157 (n : Nat) (out opt p c1 c2 : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜∃ loc : UInt32, args = [.i32 out, .i32 opt, .i32 loc]⌝ ∗
    n ↦[i32][ opt.toNat ] p ∗ n ↦[i32][ opt.toNat + 4 ] c1 ∗ n ↦[i32][ opt.toNat + 8 ] c2 ∗
    n ↦[wms][ out.toNat ] ob)

def post157 (n : Nat) (out opt p c1 c2 : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ opt.toNat ] p ∗ n ↦[i32][ opt.toNat + 4 ] c1 ∗
    n ↦[i32][ opt.toNat + 8 ] c2 ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c1 ∗
    n ↦[i32][ out.toNat + 8 ] c2)

/-- **`Option::<Vec<u8>>::expect(msg)`** (157) on `Some((p, c1, c2))` (`p ≠ 0`): the `Vec`
copied to `out`. -/
theorem f157_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out opt p c1 c2 : UInt32) (ob : List UInt8)
    (hob : ob.length = 12) (hp : p ≠ 0) (hout : out.toNat + 12 ≤ 2 ^ 32) (hopt : opt.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f157 Cg (pre157 n out opt p c1 c2 ob)
        (fun _ => 16 * cfg.regularOpCost) (post157 n out opt p c1 c2) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre157 at HP
  icases HP with ⟨%⟨loc, hargs⟩, O0, O4, O8, Ho⟩
  subst hargs
  have ho0 : (ob.take 8).length = 8 := by simp; omega
  have ho8 : (ob.drop 8).length = 4 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  simp only [f157]
  mstep; mstep; mstep [O0]; mstep
  ihave O := KeyGet.join64 n opt.toNat p c1 $$ [O0 O4]
  · iframe O0 O4
  mstep; mstep; mstep [O]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [Ho0]
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [O8]; mstep [Ho8]
  mcredits R
  iframe Hc
  iunfold post157
  ihave O := KeyGet.split64 n opt.toNat p c1 $$ O
  icases O with ⟨O0, O4⟩
  ihave Ho0 := KeyGet.split64 n out.toNat p c1 $$ Ho0
  icases Ho0 with ⟨Ho0, Ho4⟩
  iframe O0 O4 O8 Ho0 Ho4 Ho8
  ipureintro; simp [htype]

end L157

/-! ## `SliceRead::new` (644) -/

section L644

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `SliceRead` `(ptr, len, index)` at `out`. -/
def sliceRead (n : Nat) (out ptr len idx : UInt32) : IProp GF :=
  iprop(n ↦[i32][ out.toNat ] ptr ∗ n ↦[i32][ out.toNat + 4 ] len ∗ n ↦[i32][ out.toNat + 8 ] idx)

/-- **`SliceRead::new(slice)`** (644): the slice `(ptr, len)` and the index 0 at `out`. -/
theorem f644_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out ptr len : UInt32) (ob : List UInt8)
    (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f644 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 len]⌝ ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 9 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ sliceRead n out ptr len 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  have ho4 : (ob.take 4).length = 4 := by simp; omega
  have ho8 : (ob.drop 4).length = 8 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  ihave Ho4 := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by omega) $$ Ho4
  icases Ho4 with ⟨Ho4, Ho8⟩
  have ha : out.toNat + 4 + 4 = out.toNat + 8 := by omega
  rw [ha]
  simp only [f644]
  mstep; mstep; mstep [Ho8]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep [Ho0]
  mcredits R
  iframe Hc
  iunfold sliceRead
  iframe Ho0 Ho4 Ho8

end L644

/-! ## `from_slice` (65), from a specification of 66 -/

section L65

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`serde_json::from_slice(out, ptr, len)`** (65) from any specification of
`from_trait(out, rd)` (66) on the `SliceRead` 644 builds at `rd = sp - 16`: its frame of 16
bytes below `sp` taken from the stack (`stk`), the rest of 66's pre- and postcondition `P`, `Q`
(which see `sp - 16` as the stack pointer). -/
theorem f65_of_66 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a66 a644 : Nat)
    (ha66 : mi.funcAddrs[66]? = some a66) (ha644 : mi.funcAddrs[644]? = some a644)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (sp out ptr len : UInt32)
    (hsp : 16 ≤ sp.toNat) (P : IProp GF) (K66 : Nat) (Q : List Value → IProp GF) :
    a644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ a66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ∗
      MFunSpec cfg lim (d + 1) types[14]! inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 (sp - 16)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          sliceRead n (sp - 16) ptr len 0 ∗ P))
        (fun _ => K66)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          (∃ a b c : UInt32, sliceRead n (sp - 16) a b c) ∗ Q rs))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ P))
        (fun _ => 45 * cfg.regularOpCost + K66)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 16) 16 ∗ Q [])) := by
  iintro ⟨#F644, #F66, #Hi, #S66⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HP⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have t31 : types[31]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  icases stk_split n (sp.toNat - 16) 12 4 $$ Hs with ⟨Hs, Hs12⟩
  iunfold stk at Hs
  icases Hs with ⟨%ob, %hob, Hs⟩
  simp only [f65]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall (f644_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 16) ptr len ob hob
      (by omega)) using [Hs]
  · ihave Hs := memBytes_addr (show sp.toNat - 16 = (sp - 16).toNat by omega) $$ Hs
    iframe Hs
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mstep; mstep
  mcall S66 using [Hg Hrd HP]
  · iframe Hg Hrd HP
  icases HQ with ⟨%hrs, Hg, ⟨%a, %b, %c, Hrd⟩, HQ⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  mcredits R
  iframe Hc
  iframe Hg HQ
  iunfold sliceRead at Hrd
  icases Hrd with ⟨R0, R4, R8⟩
  ihave R0 := stk_word n _ a $$ R0
  ihave R4 := stk_word n _ b $$ R4
  ihave R8 := stk_word n _ c $$ R8
  ihave R := stk_join n _ 4 4 $$ [R0 R4]
  · iframe R0 R4
  ihave R := stk_join n _ 8 4 $$ [R R8]
  · iframe R R8
  rw [h16]
  ihave R := stk_join n _ 12 4 $$ [R Hs12]
  · iframe R Hs12
  iexact R

end L65

end WNear.Binary.ArgsLeaves
