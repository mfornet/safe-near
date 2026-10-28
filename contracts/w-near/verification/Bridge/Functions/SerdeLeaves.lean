import Bridge.Functions.VecWithCap
import Bridge.Functions.DropVec
import Bridge.Functions.KeyGet
import Binary.Code.Part00
import Binary.Code.Part06
import Binary.Code.Part07
import Binary.Code.Part09
import NearLogic.Tactic.Control

/-!
# The leaves of `serde_json::to_vec::<U128>` (96) and `U128::serialize` (385) (M5)

```wat
;; 472 fmt::Argument::new(out, v, fi)   *(out + 4) = fi; *out = v
;; 365 Result<(), fmt::Error>::expect(r) frame 16; r = 0 ⇒ nothing (r ≠ 0 panics)
;; 321 drop_in_place::<String>(v)       778(v); 747(v)  (the body of 68)
;; 94  Vec::with_capacity_in(out, c)    frame 16; 767(sp + 8, c, 0); (ptr, c, 0) at out
;;                                      (the body of 373)
```

Costs (`regular_op_cost`s, activation excluded): 472 `6`; 365 (Ok) `12`; 321 `315`
(as 68); 94 `35 + 203` plus `costAlloc cfg false c` (as 373).
-/

namespace WNear.Binary.SerdeLeaves

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor heapAfter costAlloc
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.VecWithCap (okF vecCode2 pre767 post767 f767_spec pre373 post373)
open WNear.Binary.DropVec (dropCode pre747 post747 f747_spec f778_spec)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `fmt::Argument::new` (472) -/

/-- **`fmt::Argument::new(out, v, fi)`** (472): the `Argument` `(v, fi)` at `out`. -/
theorem f472_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out v fi : UInt32) (ob : List UInt8)
    (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f472 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 v, .i32 fi]⌝ ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 6 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] v ∗ n ↦[i32][ out.toNat + 4 ] fi)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  simp only [f472]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep [Ho0]
  mcredits R
  iframe Hc Ho0 Ho4

/-! ## `Result<(), fmt::Error>::expect` (365), `Ok` -/

/-- **`Result<(), fmt::Error>::expect(0)`** (365): the `Ok` path; the frame of 16 bytes is
reserved and released, untouched. -/
theorem f365_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (g : Nat)
    (hg : mi.globalAddrs[0]? = some g) (Cg : Nat) (gt : GlobalType) (s : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f365 Cg
        (fun args => iprop(⌜args = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩))
        (fun _ => 12 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg⟩
  subst hargs
  simp only [f365]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mstep_taken with (simp [Numeric.bool, Numeric.itestop32])
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc Hg

/-! ## `drop_in_place::<String>` (321) -/

/-- **`drop_in_place::<String>`** (321, the body of 68) of a `String` `(p, c, l)` with `c ≠ 0` and
`(p, c)` live: the buffer is freed. -/
theorem f321_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (v p c l : UInt32) (hc : c ≠ 0) (hv : v.toNat + 12 ≤ 2 ^ 32) :
    dropCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f321 Cg (pre747 n maxP len live F v p c l)
        (fun _ => 315 * cfg.regularOpCost) (post747 n maxP len live F v p c l) := by
  iintro #Hc
  ihave #S747 := f747_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len live F v p c l
    hc hv $$ Hc
  iunfold dropCode at Hc
  icases Hc with ⟨#Hi, -, -, -, -, -, -, -, -, #H747, #H778⟩
  have ha747 := hm.funcs 747 (by decide)
  have ha778 := hm.funcs 778 (by decide)
  have t0 : types[0]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre747 at HP
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f321]
  mstep
  mcall (f778_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi Cg v) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep
  mcall S747 using [HP]
  · iunfold pre747
    isplitr
    · ipureintro; rfl
    iexact HP
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post747
  iframe HQ
  ipureintro; simp [htype]

/-! ## `Vec::with_capacity_in` (94) -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`Vec::<u8>::with_capacity_in(out, c)`** (94, the body of 373): the `Vec` `(ptr, c, 0)` at
`out`, the allocation as `heapAfter` (for `c ≠ 0`: a live block of `c` bytes). -/
theorem f94_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (hs : 80 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c)
    (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f94 Cg
        (pre373 n g gt s out c idx ta (A 578) maxP len live F ob)
        (fun _ => 35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAlloc cfg false c))
        (post373 n g gt s out c idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H767 : A 767 ↪[wf] FuncInst.wasm types[31]! inst f767 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha767 := hm.funcs 767 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h16]; omega
  have hob0 : (ob.take 8).length = 8 := by simp; omega
  have hob4 : (ob.drop 8).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre373 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  icases stk_split n (s.toNat - 80) 64 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 80 + 64) 8 8 $$ Hs with ⟨Y, Z⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  simp only [f94]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mcall (f767_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) c false idx maxP len live zb hzb (by omega) hc28 hr (F := F) (hF := hF) (hFz := fun h => by cases h)) using [Hg X Hvt Hinv Z]
  · iunfold pre767
    ihave X := stk_addr (show s.toNat - 80 = (s - 16).toNat - 64 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 80 + 64 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post767 at HQ
  icases HQ with ⟨%hrs, %p, Hg, X, Hvt, Z0, Z4, HA⟩
  subst hrs
  mcredits (13 * cfg.regularOpCost + R)
  ihave Z := KeyGet.join64 n (s - 16 + 8).toNat p c $$ [Z0 Z4]
  · iframe Z0 Z4
  mstep; mstep [Z]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep [Ho8]
  mstep; mstep; mstep [Ho0]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post373
  isplitr
  · ipureintro; simp [htype]
  iexists p
  ihave Ho0 := KeyGet.split64 n out.toNat p c $$ Ho0
  icases Ho0 with ⟨Ho0, Ho4⟩
  iframe Hg Hvt Ho0 Ho4 Ho8 HA
  ihave X := stk_addr (show (s - 16).toNat - 64 = s.toNat - 80 by omega) $$ X
  ihave Z := KeyGet.split64 n _ p c $$ Z
  icases Z with ⟨Z0, Z4⟩
  ihave Z0 := stk_word n _ p $$ Z0
  ihave Z4 := stk_word n _ c $$ Z4
  ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
  · iframe Z0 Z4
  ihave Z := stk_addr (show (s - 16 + 8).toNat = s.toNat - 80 + 64 + 8 by omega) $$ Z
  ihave Y := stk_join n (s.toNat - 80 + 64) 8 8 $$ [Y Z]
  · iframe Y Z
  iapply stk_join n (s.toNat - 80) 64 16
  iframe X Y

end Spec

end WNear.Binary.SerdeLeaves
