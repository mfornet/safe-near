import Bridge.Functions.AllocDealloc
import Bridge.Functions.Interface
import NearLogic.Tactic.Control

/-!
# `drop_in_place::<Vec<u8>>` (68) and the deallocation below it

```wat
;; 68  drop_in_place<Vec<u8>> (v): 778(v) (Vec's Drop: no-op for u8); 747(v)
;; 747 <RawVec as Drop>::drop (v): cap := [v+4]; cap ≠ 0 → 777([v], cap, 1)
;; 777 Global::deallocate (p, size, align): size ≠ 0 → __rust_dealloc(p, size, align) (311)
```

* `f777_spec`, `f747_spec`, `f68_spec`: a `Vec` `(p, c, l)` with `c ≠ 0` whose buffer `(p, c)` is
  live: the block is freed (`heapInv … (live.erase (p, c)) (F + 1)`, `AllocDealloc.f311_spec`).
-/

namespace WNear.Binary.DropVec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code the drop runs (persistent). -/
def dropCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 237 ↪[wf] FuncInst.wasm types[31]! inst f237 ∗
    A 582 ↪[wf] FuncInst.wasm types[45]! inst f582 ∗ A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗
    A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗ A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗
    A 575 ↪[wf] FuncInst.wasm types[0]! inst f575 ∗ A 311 ↪[wf] FuncInst.wasm types[31]! inst f311 ∗
    A 777 ↪[wf] FuncInst.wasm types[31]! inst f777 ∗ A 747 ↪[wf] FuncInst.wasm types[0]! inst f747 ∗
    A 778 ↪[wf] FuncInst.wasm types[0]! inst f778)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (dropCode (GF := GF) inst mi A) := by
  unfold dropCode; infer_instance

/-- `__rust_dealloc` (311) from `dropCode`. -/
theorem f311_drop (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (ptr size align : UInt32) :
    dropCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f311 Cg
        (fun args => iprop(⌜args = [.i32 ptr, .i32 size, .i32 align]⌝ ∗
          ⌜(ptr.toNat, size.toNat) ∈ live⌝ ∗ heapInv n maxP len live F ∗ block n ptr.toNat size.toNat))
        (fun _ => 256 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ heapInv n maxP len (live.erase (ptr.toNat, size.toNat)) (F + 1))) := by
  iintro #Hc
  iunfold dropCode at Hc
  icases Hc with ⟨#Hi, #H237, #H582, #H570, #H568, #H576, #H575, -⟩
  iapply (AllocDealloc.f311_spec cfg lim d type htype inst mi n hm.mem (A 237) (A 582) (A 570) (A 568) (A 576)
    (A 575) (hm.funcs 237 (by decide)) (hm.funcs 582 (by decide)) (hm.funcs 570 (by decide))
    (hm.funcs 568 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 575 (by decide))
    types[31]! types[45]! types[32]! types[13]! types[32]! types[0]! rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hd Cg maxP len live F ptr size align)
  iframe H237 H582 H570 H568 H576 H575 Hi

/-- `<Vec<u8> as Drop>::drop` (778): no instruction. -/
theorem f778_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (v : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f778 Cg (fun args => iprop(⌜args = [.i32 v]⌝))
        (fun _ => 0) (fun _ rs => iprop(⌜rs = []⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f778]
  mstep
  mcredits R
  iframe Hc

def pre777 (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (p c : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p, .i32 c, .i32 1]⌝ ∗ ⌜(p.toNat, c.toNat) ∈ live⌝ ∗ heapInv n maxP len live F ∗
    block n p.toNat c.toNat)

def post777 (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (p c : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ heapInv n maxP len (live.erase (p.toNat, c.toNat)) (F + 1))

/-- `Global::deallocate` (777) of a live block, `c ≠ 0`. -/
theorem f777_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (p c : UInt32) (hc : c ≠ 0) :
    dropCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f777 Cg (pre777 n maxP len live F p c)
        (fun _ => 273 * cfg.regularOpCost) (post777 n maxP len live F p c) := by
  iintro #Hc
  ihave #S311 := f311_drop cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg maxP len live F p c 1 $$ Hc
  iunfold dropCode at Hc
  icases Hc with ⟨#Hi, -, -, -, -, -, -, #H311, -⟩
  have ha311 := hm.funcs 311 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre777 at HP
  icases HP with ⟨%hargs, %hl, Hinv, Hb⟩
  subst hargs
  simp only [f777]
  mstep; mstep; mstep; mstep with simp [hc]
  mstep; mstep; mstep
  mcall S311 using [Hinv Hb]
  · iframe Hinv Hb
    ipureintro; first | exact hl | exact ⟨rfl, hl⟩
  icases HQ with ⟨%hrs, Hinv⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post777
  iframe Hinv
  ipureintro; simp [htype]

def pre747 (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (v p c l : UInt32) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 4 ] c ∗ n ↦[i32][ v.toNat + 8 ] l ∗
    ⌜(p.toNat, c.toNat) ∈ live⌝ ∗ heapInv n maxP len live F ∗ block n p.toNat c.toNat)

def post747 (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (v p c l : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 4 ] c ∗ n ↦[i32][ v.toNat + 8 ] l ∗
    heapInv n maxP len (live.erase (p.toNat, c.toNat)) (F + 1))

/-- `<RawVec as Drop>::drop` (747) of a `Vec` `(p, c, l)` with `c ≠ 0` and `(p, c)` live. -/
theorem f747_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (v p c l : UInt32) (hc : c ≠ 0) (hv : v.toNat + 12 ≤ 2 ^ 32) :
    dropCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f747 Cg (pre747 n maxP len live F v p c l)
        (fun _ => 293 * cfg.regularOpCost) (post747 n maxP len live F v p c l) := by
  iintro #Hc
  ihave #S777 := f777_spec cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg maxP len live F p c hc
    $$ Hc
  iunfold dropCode at Hc
  icases Hc with ⟨#Hi, -, -, -, -, -, -, -, #H777, -⟩
  have hn := hm.mem
  have ha777 := hm.funcs 777 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre747 at HP
  icases HP with ⟨%hargs, V0, V4, V8, %hl, Hinv, Hb⟩
  subst hargs
  simp only [f747]
  mstep; mstep; mstep [V4]; mstep; mstep; mstep with simp [hc]
  mstep; mstep [V0]; mstep; mstep
  mcall S777 using [Hinv Hb]
  · iunfold pre777
    iframe Hinv Hb
    ipureintro; exact ⟨rfl, hl⟩
  iunfold post777 at HQ
  icases HQ with ⟨%hrs, Hinv⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post747
  iframe V0 V4 V8 Hinv
  ipureintro; simp [htype]

/-- **`drop_in_place::<Vec<u8>>`** (68) of a `Vec` `(p, c, l)` with `c ≠ 0` and `(p, c)` live: the
buffer is freed. -/
theorem f68_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (v p c l : UInt32) (hc : c ≠ 0) (hv : v.toNat + 12 ≤ 2 ^ 32) :
    dropCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg (pre747 n maxP len live F v p c l)
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
  simp only [f68]
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

end Spec

end WNear.Binary.DropVec
