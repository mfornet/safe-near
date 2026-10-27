import Binary.Code.Part05
import Binary.Code.Part06
import Binary.Code.Part11
import NearLogic.Tactic.Control

/-!
# `__rust_alloc` / `__rust_dealloc` down to wee_alloc, in the metered logic

The global-allocator shims of `contract.wasm`:

```wat
(func 310 (param size align) (result i32) (local r)   ;; __rust_alloc
  local.get 0  local.get 1  call 236  local.set 2  local.get 2  return)
(func 236 (param size align) (result i32)             ;; __rg_alloc
  i32.const 1074896  local.get 0  local.get 1  call 581)     ;; WeeAlloc::alloc(&ALLOC, ..)
(func 311 (param ptr size align)                      ;; __rust_dealloc
  local.get 0  local.get 1  local.get 2  call 237  return)
(func 237 (param ptr size align)                      ;; __rg_dealloc
  i32.const 1074896  local.get 0  local.get 1  local.get 2  call 582)
```

`1074896` is the static `ALLOC: WeeAlloc` (its one word, the free-list head;
`Harness.Builtins.freeListHead`).

The specs here are *parametric* in a specification of the allocator proper:
any `MFunSpec` `P K Q` of `WeeAlloc::alloc` (581) on
`[&ALLOC, size, align]` gives one of `__rust_alloc` (310) on `[size, align]`
with the same `P` and `Q` and cost `K + 30` `regular_op_cost`s (the
activations of 236 (9) and 581 (11), the two calls, 8 instructions and the
`return`); likewise `WeeAlloc::dealloc` (582) on `[&ALLOC, ptr, size, align]`
gives `__rust_dealloc` (311) for `K + 32` (activations of 237 (10) and 582
(12)). So whatever `HeapInv`-based spec 581/582 get (`AllocInv.lean`), the
entry points follow with no further work. Activations of 310/311 themselves
(9 and 10) are paid by their callers, as for every `MFunSpec`.
-/

namespace WNear.Binary.AllocWrap

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-- The address of the static `ALLOC: WeeAlloc` (the free-list head). -/
abbrev allocStatic : UInt32 := 1074896

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `__rg_alloc` (236) from any spec of `WeeAlloc::alloc` (581). -/
theorem f236_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (a581 : Nat)
    (ha : mi.funcAddrs[581]? = some a581) (ty581 : FuncType) (hty1 : ty581.params.length = 3)
    (hty2 : ty581.results.length = 1) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (P : List Value → IProp GF) (K : List Value → Nat) (Q : UInt32 → IProp GF)
    (size align : UInt32) :
    a581 ↪[wf] FuncInst.wasm ty581 inst f581 ∗ inst ↪[inst] mi ∗
      □ MFunSpec cfg lim (d + 1) ty581 inst mi f581 Cg P K (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ Q p))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f236 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 align]⌝ ∗
          P [.i32 1074896, .i32 size, .i32 align]))
        (fun _ => 15 * cfg.regularOpCost + K [.i32 1074896, .i32 size, .i32 align])
        (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ Q p)) := by
  iintro ⟨#Hf, #Hi, #Hs⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HP⟩ Hc
  subst hargs
  simp only [f236]
  mstep; mstep; mstep
  mcall Hs using [HP] with (simp [activationGas, entryLocals, f581, ValType.default]; omega)
  · iexact HP
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  rw [htype]
  mpay
  mcredits R
  iframe Hc
  iexists p
  iframe HQ
  ipureintro; rfl



/-- `__rust_alloc` (310) from a spec of `__rg_alloc` (236) of the shape
`f236_spec` gives. -/
theorem f310_of_f236 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (a236 : Nat)
    (ha : mi.funcAddrs[236]? = some a236) (ty236 : FuncType) (hty1 : ty236.params.length = 2)
    (hty2 : ty236.results.length = 1) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (P : IProp GF) (K : Nat) (Q : UInt32 → IProp GF) (size align : UInt32) :
    a236 ↪[wf] FuncInst.wasm ty236 inst f236 ∗ inst ↪[inst] mi ∗
      □ MFunSpec cfg lim (d + 1) ty236 inst mi f236 Cg
          (fun args => iprop(⌜args = [.i32 size, .i32 align]⌝ ∗ P)) (fun _ => K)
          (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ Q p))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 align]⌝ ∗ P))
        (fun _ => 15 * cfg.regularOpCost + K)
        (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ Q p)) := by
  iintro ⟨#Hf, #Hi, #Hs⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HP⟩ Hc
  subst hargs
  simp only [f310]
  mstep; mstep
  mcall Hs using [HP] with (simp [activationGas, entryLocals, f236, ValType.default]; omega)
  · iframe HP
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  mstep; mstep; mstep
  mcredits R
  iframe Hc
  iexists p
  iframe HQ
  ipureintro; simp [htype]

/-- `__rg_dealloc` (237) from any spec of `WeeAlloc::dealloc` (582). -/
theorem f237_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (a582 : Nat)
    (ha : mi.funcAddrs[582]? = some a582) (ty582 : FuncType) (hty1 : ty582.params.length = 4)
    (hty2 : ty582.results.length = 0) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (P : List Value → IProp GF) (K : List Value → Nat) (Q : IProp GF)
    (ptr size align : UInt32) :
    a582 ↪[wf] FuncInst.wasm ty582 inst f582 ∗ inst ↪[inst] mi ∗
      □ MFunSpec cfg lim (d + 1) ty582 inst mi f582 Cg P K (fun _ rs => iprop(⌜rs = []⌝ ∗ Q))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f237 Cg
        (fun args => iprop(⌜args = [.i32 ptr, .i32 size, .i32 align]⌝ ∗
          P [.i32 1074896, .i32 ptr, .i32 size, .i32 align]))
        (fun _ => 17 * cfg.regularOpCost + K [.i32 1074896, .i32 ptr, .i32 size, .i32 align])
        (fun _ rs => iprop(⌜rs = []⌝ ∗ Q)) := by
  iintro ⟨#Hf, #Hi, #Hs⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HP⟩ Hc
  subst hargs
  simp only [f237]
  mstep; mstep; mstep; mstep
  mcall Hs using [HP] with (simp [activationGas, entryLocals, f582, ValType.default]; omega)
  · iexact HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp

/-- `__rust_dealloc` (311) from a spec of `__rg_dealloc` (237) of the shape
`f237_spec` gives. -/
theorem f311_of_f237 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (a237 : Nat)
    (ha : mi.funcAddrs[237]? = some a237) (ty237 : FuncType) (hty1 : ty237.params.length = 3)
    (hty2 : ty237.results.length = 0) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (P : IProp GF) (K : Nat) (Q : IProp GF) (ptr size align : UInt32) :
    a237 ↪[wf] FuncInst.wasm ty237 inst f237 ∗ inst ↪[inst] mi ∗
      □ MFunSpec cfg lim (d + 1) ty237 inst mi f237 Cg
          (fun args => iprop(⌜args = [.i32 ptr, .i32 size, .i32 align]⌝ ∗ P)) (fun _ => K)
          (fun _ rs => iprop(⌜rs = []⌝ ∗ Q))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f311 Cg
        (fun args => iprop(⌜args = [.i32 ptr, .i32 size, .i32 align]⌝ ∗ P))
        (fun _ => 15 * cfg.regularOpCost + K)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ Q)) := by
  iintro ⟨#Hf, #Hi, #Hs⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HP⟩ Hc
  subst hargs
  simp only [f311]
  mstep; mstep; mstep
  mcall Hs using [HP] with (simp [activationGas, entryLocals, f237, ValType.default]; omega)
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mstep
  mcredits R
  iframe Hc HQ
end Spec

end WNear.Binary.AllocWrap
