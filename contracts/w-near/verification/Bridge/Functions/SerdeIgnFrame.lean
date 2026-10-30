import Bridge.Functions.VecAppend
import Bridge.Functions.SerdeRead

/-!
# `ignore_value`'s frame stack when no frame is pushed (M6): 84 and 85

`ignore_value` (81) keeps the frames of nested `[`/`{` (all but the innermost) on the scratch
`Vec<u8>`. When the ignored value nests at most one bracket deep, nothing is ever pushed:

* `f84_none`: `spec_extend(vec, None, b)` (84) with the flag 0 reserves room for nothing (698, through
  `VecAppend.f698_room` with `k = 0`) and writes nothing;
* `f85_empty`: `pop(out, vec)` (85) on the empty scratch writes `None` (`[0, 0]`) at `out`.
-/

namespace WNear.Binary.SerdeIgnFrame

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)

section L85

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`Vec<u8>::pop(out, vec)`** (85) on an empty vector: `None` at `out`. -/
theorem f85_empty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec : UInt32) (b0 b1 : UInt8)
    (hout : out.toNat + 2 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f85 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 vec]⌝ ∗ n ↦[i32][ vec.toNat + 8 ] 0 ∗
          n ↦[wms][ out.toNat ] [b0] ∗ n ↦[wms][ out.toNat + 1 ] [b1]))
        (fun _ => 20 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ vec.toNat + 8 ] 0 ∗
          n ↦[wms][ out.toNat ] [0] ∗ n ↦[wms][ out.toNat + 1 ] [0])) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, H8, O0, O1⟩
  subst hargs
  simp only [f85]
  mstep; mstep; mstep; mstep [H8]; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep [O1]
  mstep; mstep; mstep [O0]
  mcredits R
  rw [show storeBytes (Value.i32 0) 1 = [0] by decide,
    show storeBytes (Value.i32 (UInt32.ofNat 0)) 1 = [0] by decide]
  iframe Hc H8
  isplitl [O0]
  · iexact O0
  · iexact O1

end L85

section L84

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`spec_extend(vec, None, b)`** (84) with the flag 0: nothing pushed, the vector unchanged. -/
theorem f84_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr len cap : UInt32) (b : UInt32) (hs : 16 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat ≤ cap.toNat) :
    VecAppend.appCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f84 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 0, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] len))
        (fun _ => 120 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len)) := by
  iintro #Hk
  ihave #S698 := VecAppend.f698_room (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec len 0 cap hs hvec (by simpa using hroom) $$ Hk
  iunfold VecAppend.appCode at Hk
  icases Hk with ⟨-, -, #H698, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha698 := hm.funcs 698 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, H0, H4, H8⟩
  subst hargs
  simp only [f84]
  mstep; mstep
  mcall S698 using [Hg Hs H4 H8]
  · iframe Hg Hs H4 H8
  icases HQ with ⟨%hrs, Hg, Hs, H4, H8⟩
  subst hrs
  mcredits (40 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep
  mstep; mstep [H8]; mstep
  mstep; mstep [H0]; mstep
  mstep
  mcredits (cfg.regularOpCost + (20 * cfg.regularOpCost + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 20 * cfg.regularOpCost + R)
    (I := fun X fr => iprop(⌜X = [] ∧ fr = ⟨#[.i32 vec, .i32 len, .i32 b, .i32 1, .i32 ptr], inst, mi⟩⌝ ∗
      credits Cg (20 * cfg.regularOpCost + R) ∗ n ↦[i32][ vec.toNat + 8 ] len ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%⟨hX, hfr⟩, Hc, H8, Hg, Hs, H0, H4⟩
    subst hX
    rw [hfr]
    mstep; mstep; mstep
    mstep_taken with decide
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    mstep; mstep
    mstep [H8]
    mcredits R
    iframe Hc Hg Hs H0 H4 H8
  · iframe Hc
    inext
    iintro Hc
    iframe Hc H8 Hg Hs H0 H4
    ipureintro; constructor
    · rfl
    · congr 1

end L84

end WNear.Binary.SerdeIgnFrame
