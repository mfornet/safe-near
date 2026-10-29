import Bridge.Functions.VecGrow

/-!
# `finish_grow` (845) of `format!`'s `String` on a nonempty buffer (M8)

`alloc::fmt::format` (846) writes through `<&mut String as fmt::Write>::write_str` (840), which
appends with `spec_extend` (841). Without room, 841 asks `finish_grow` (845, a monomorph distinct
from `VecGrow`'s 714) to reallocate:

```
845 finish_grow(out, c, 1, cur)   align 1 ≠ 0, c ≥ 0 (signed); cur = Some(ptr, cap), cap ≠ 0 ⇒
                                  p := __rust_realloc(ptr, cap, 1, c) (312); p ≠ 0 ⇒ out := (0, p, c)
```

`f845_spec` is `VecGrow.f714_spec` without a frame: the realloc (`VecGrow.f312_spec`) runs on the
caller's stack (16 bytes below `s`).

Left for the `String` sink (see `notes/todo/wnear_refinement_proof.md`, M8): 841 (`spec_extend`, with
room and through 845), 840 (`write_str`), and a sink predicate for a `String` that may be
reallocated several times while `format!` writes into it.
-/

namespace WNear.Binary.StrGrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.VecGrow (reallocCode reallocated preR postR post154 cost154 f312_spec)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre845 (n g : Nat) (gt : GlobalType) (s out c cur ptr cap : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c, .i32 1, .i32 cur]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[i32][ cur.toNat ] ptr ∗ n ↦[i32][ cur.toNat + 4 ] cap ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ out.toNat ] ob)

def post845 (n g : Nat) (gt : GlobalType) (s out c cur ptr cap : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
    vt n 1057464 idx ta a578 ∗ n ↦[i32][ cur.toNat ] ptr ∗ n ↦[i32][ cur.toNat + 4 ] cap ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
    reallocated n maxP hl live F ptr cap c p bs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur)`** (845) with the current memory `Some(ptr, cap)`, `cap ≠ 0`:
`__rust_realloc(ptr, cap, 1, c)` (312), `Ok((p, c))` at `out`. -/
theorem f845_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs ob : List UInt8) (hs : 16 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcc : cap.toNat < c.toNat)
    (hc : c.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat) (hlive : (ptr.toNat, cap.toNat) ∈ live)
    (hr : roomFor hl maxP c) :
    reallocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f845 Cg
        (pre845 n g gt s out c cur ptr cap idx ta (A 578) maxP hl live F bs ob)
        (fun _ => 100 * cfg.regularOpCost + cost154 cfg F cap c)
        (post845 n g gt s out c cur ptr cap idx ta (A 578) maxP hl live F bs) := by
  iintro #HR
  ihave #S312 := f312_spec (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt s
    ptr cap c idx maxP hl live F bs hs hcap hcc hc hbs hlive hr $$ HR
  iunfold reallocCode at HR
  icases HR with ⟨#H, -, -, -, -, #H312⟩
  iunfold AllocTwo.code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha312 := hm.funcs 312 (by decide)
  have t33 : types[33]!.params.length = 4 := by rfl
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s c 0) = 1 := by
    have h' : c.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
  generalize hK : cost154 cfg F cap c = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre845 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  ihave Ho4 := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho4
  icases Ho4 with ⟨Ho4, Ho8⟩
  simp only [f845]
  repeat mstep
  mstep [Hp]
  mstep
  mstep_taken with (simp; exact hptr)
  repeat mstep
  mstep [Hcap]
  mstep
  mstep_taken with (simp; exact hcap0)
  repeat mstep
  mcall S312 using [Hg Hs Hvt Hinv Hbs]
  · iunfold preR
    iframe Hg Hs Hvt Hinv Hbs
  iunfold post154 at HQ
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  iunfold postR at HQ
  icases HQ with ⟨Hg, Hs, Hvt, HA⟩
  iunfold reallocated at HA
  icases HA with ⟨%⟨hp0, hpb⟩, HA⟩
  mcredits (20 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Ho4]
  repeat mstep
  mstep [Ho0]
  repeat mstep
  mstep [Ho8]
  mcredits R
  iframe Hc
  iunfold post845
  isplitr
  · ipureintro; rfl
  iexists p
  iframe Hg Hs Hvt Hp Hcap Ho0 Ho4 Ho8
  iunfold reallocated
  iframe HA
  ipureintro; exact ⟨hp0, hpb⟩

end Spec

end WNear.Binary.StrGrow
