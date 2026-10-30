import Bridge.Functions.PanicStr
import Model.Calls

/-!
# `near_deposit`'s panics through Rust's panic machinery, as parameters (M8)

Three of `near_deposit`'s panics go through `std::panicking` and near-sdk 3.1's panic hook, which
formats `panicked at '{payload}', {file}:{line}:{col}` and passes it to `panic_utf8`:

```
232:  begin_panic("Requires positive attached deposit" (1050492, 34), &Location (1050540))   664
232:  begin_panic("ERR_DEPOSIT_TOO_SMALL" (1050556, 21), &Location (1050580))               664
363:  expect_failed("Total supply overflow" (1053016, 21), &Location (1053040))             879
```

The locations in the data segment are `src/w_near.rs` (13 bytes at 1050526) `:15:9` and `:20:13`,
and `…/near-contract-standards-3.1.0/src/fungible_token/core_impl.rs` (119 bytes at 1052816)
`:108:55`: the model's `Panic.message` texts (`rustPanic`).

Their specifications are being proved elsewhere; `near_deposit`'s proof takes them as hypotheses
of the shape of `PanicStr.f156_spec` (`MFunSpecT`, no normal return, the trap postcondition
`panicked Cg h text`):

* `Spec664 … mp ml loc text`: `begin_panic(mp, ml, loc)` (664) from the resources `Pre sp h` the
  caller owns at the call (stack below `sp`, the hook's cells, the heap, the host `h`), at `K h`;
* `Spec879 … mp ml loc text`: `expect_failed(mp, ml, loc)` (879), the same shape.

`Pre`, `K` and the depth `D` are the specifications' own; the caller must produce `Pre sp h` from
what it owns.

The texts: `textPositive`, `textTooSmall`, `textSupply` (the UTF-8 of the model's messages,
`utf8String_textPositive` …), and the payloads' bytes in the data segment (`payloadPositive_data` …).
-/

namespace WNear.Binary.NearDepositPanics

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## The texts -/

/-- The text the hook passes to `panic_utf8` for each panic: the model's message in UTF-8. -/
def textPositive : List UInt8 := (WNear.Panic.message .requiresPositiveDeposit).toUTF8.toList
def textTooSmall : List UInt8 := (WNear.Panic.message .depositTooSmall).toUTF8.toList
def textSupply : List UInt8 := (WNear.Panic.message .totalSupplyOverflow).toUTF8.toList

theorem utf8String_textPositive :
    utf8String textPositive = WNear.Panic.message .requiresPositiveDeposit := by
  decide +kernel
theorem utf8String_textTooSmall :
    utf8String textTooSmall = WNear.Panic.message .depositTooSmall := by
  decide +kernel
theorem utf8String_textSupply :
    utf8String textSupply = WNear.Panic.message .totalSupplyOverflow := by
  decide +kernel

/-- The payloads in the data segment. -/
theorem payloadPositive_data :
    (List.range 34).map (fun k => wNearSource.read (159306 + (1050492 - 1048576) + k)) =
      "Requires positive attached deposit".toUTF8.toList := by decide +kernel

theorem payloadTooSmall_data :
    (List.range 21).map (fun k => wNearSource.read (159306 + (1050556 - 1048576) + k)) =
      "ERR_DEPOSIT_TOO_SMALL".toUTF8.toList := by decide +kernel

theorem payloadSupply_data :
    (List.range 21).map (fun k => wNearSource.read (159306 + (1053016 - 1048576) + k)) =
      "Total supply overflow".toUTF8.toList := by decide +kernel

/-- The locations' `(file, len, line, col)` words in the data segment. -/
theorem locPositive_data :
    (List.range 16).map (fun k => wNearSource.read (159306 + (1050540 - 1048576) + k)) =
      bytes32 1050526 ++ bytes32 13 ++ bytes32 15 ++ bytes32 9 := by decide +kernel

theorem locTooSmall_data :
    (List.range 16).map (fun k => wNearSource.read (159306 + (1050580 - 1048576) + k)) =
      bytes32 1050526 ++ bytes32 13 ++ bytes32 20 ++ bytes32 13 := by decide +kernel

theorem locSupply_data :
    (List.range 16).map (fun k => wNearSource.read (159306 + (1053040 - 1048576) + k)) =
      bytes32 1052816 ++ bytes32 119 ++ bytes32 108 ++ bytes32 55 := by decide +kernel

theorem file_w_near_data :
    (List.range 13).map (fun k => wNearSource.read (159306 + (1050526 - 1048576) + k)) =
      "src/w_near.rs".toUTF8.toList := by decide +kernel

/-! ## The specifications, as parameters -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **What `begin_panic` (664) must do** for `near_deposit`: called with the payload `(mp, ml)`
and the location `loc` from the resources `Pre sp h`, it traps with the host panicked with `text`,
at `K h`. -/
def Spec664 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (C : IProp GF)
    (Pre : UInt32 → NearState → IProp GF) (K : NearState → Nat) (D : Nat) (mp ml loc : UInt32)
    (text : List UInt8) : Prop :=
  ∀ (d Cg : Nat) (sp : UInt32) (h : NearState), d + D < lim.maxCallDepth →
    C ⊢ MFunSpecT cfg lim d types[31]! inst mi f664 Cg
      (fun args => iprop(⌜args = [.i32 mp, .i32 ml, .i32 loc]⌝ ∗ Pre sp h)) (fun _ => K h)
      (fun _ _ => iprop(False)) (fun _ => PanicStr.panicked Cg h text)

/-- **What `expect_failed` (879) must do** for `internal_deposit`'s supply overflow (through 363),
of the same shape. -/
def Spec879 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (C : IProp GF)
    (Pre : UInt32 → NearState → IProp GF) (K : NearState → Nat) (D : Nat) (mp ml loc : UInt32)
    (text : List UInt8) : Prop :=
  ∀ (d Cg : Nat) (sp : UInt32) (h : NearState), d + D < lim.maxCallDepth →
    C ⊢ MFunSpecT cfg lim d types[31]! inst mi f879 Cg
      (fun args => iprop(⌜args = [.i32 mp, .i32 ml, .i32 loc]⌝ ∗ Pre sp h)) (fun _ => K h)
      (fun _ _ => iprop(False)) (fun _ => PanicStr.panicked Cg h text)

/-- The three hypotheses `near_deposit` takes. -/
structure DepositPanicSpecs (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (C : IProp GF) (Pre : UInt32 → NearState → IProp GF) (K664 K879 : NearState → Nat) (D : Nat) : Prop where
  positive : Spec664 cfg lim inst mi C Pre K664 D 1050492 34 1050540 textPositive
  tooSmall : Spec664 cfg lim inst mi C Pre K664 D 1050556 21 1050580 textTooSmall
  supply : Spec879 cfg lim inst mi C Pre K879 D 1053016 21 1053040 textSupply

end Spec

end WNear.Binary.NearDepositPanics
