import Bridge.Functions.PanicWithHook
import Bridge.Functions.LookupMapOps
import Bridge.Functions.NewHost
import Bridge.Functions.FmtDigits

/-!
# What `near_deposit`'s panics through the Rust hook are asked (M8)

`near_deposit` panics through `std::panicking` and near-sdk 3.1's hook at three call sites:
`begin_panic` (664) twice in 232, `expect_failed` (879) once in 363 (from 406). Their
specifications are premises of the body's proofs, of the shape of
`NearDepositPanics.Spec664`/`Spec879`, with the resources the caller owns at the call made
concrete (`pPre`):

* the stack pointer and `SP` bytes of stack below it;
* the hook installed and the payloads' `get` slots (`hookRes`);
* the interface, `panic_utf8`'s slot, the heap and the allocator's vtable;
* `Dp`: the static data the hook's `to_string` reads (left abstract here);
* the host.

`PanicSpecD … f SP Dp D mp ml loc K text`: from any such resources with room on the heap
(`HeapRoomK 8`), `f(mp, ml, loc)` traps with the host panicked with `text`, at the cost
`K F (keep h)` (the free cells `F`, what the costs read of the host). `PanicSpecs.lean` (Methods)
proves them from `PanicBegin.f664_spec` and `PanicEntries.f879_full` given `to_string`'s
specification (`ToStr`) and the payload's `get` (`GetSpec`).
-/

namespace WNear.Binary.DepositPanicSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (iface)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.PanicStr (panicSlot panicked)
open WNear.Binary.PanicWithHook (hookInstalled)
open WNear.Binary.LookupMapOps (HeapRoomK)

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

instance MFunSpecT_persistent {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P : List Value → IProp GF} {K : List Value → Nat}
    {Q : List Value → List Value → IProp GF} {T : List Value → IProp GF} :
    Persistent (MFunSpecT cfg lim d type inst mi code Cg P K Q T) := by
  unfold MFunSpecT; infer_instance

/-- The hook installed and the `get` slots of the two payload vtables: `PanicPayload<&str>`
(1062968, table index 137) for 664, the formatted payload (1066360, table index 179) for 879. -/
def hookRes (n ta : Nat) (A : Nat → Nat) (lpc : UInt32) : IProp GF :=
  iprop(hookInstalled n ta A lpc ∗ n ↦[i32][ 1062968 + 16 ] 137 ∗ ta ↦[wt][ 137 ] Ref.func (A 679) ∗
    n ↦[i32][ 1066360 + 16 ] 179 ∗ ta ↦[wt][ 179 ] Ref.func (A 826))

/-- What a panic site owns at the call: the stack pointer `sp` and `SP` bytes below it, the hook,
the interface and `panic_utf8`'s slot, the heap and the allocator's vtable, the static data `Dp`,
the host, and the digit table `lut` (the location's line and column are formatted with it; the
success path's log reads it too, so it is not part of `Dp`). -/
def pPre (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (lpc : UInt32) (SP : Nat) (Dp : IProp GF)
    (sp : UInt32) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (idx : UInt32) (h : NearState) :
    IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - SP) SP ∗ hookRes n ta A lpc ∗ iface n ta A ∗
    panicSlot n ta A ∗ heapInv n maxP hl live F ∗ vt n 1057464 idx ta (A 578) ∗ Dp ∗
    n ↦[wms][ 1070974 ] FmtDigits.lut ∗ mhostPt h)

/-- **What a panic entry `f(mp, ml, loc)` is asked**: from the resources `pPre` with room on the
heap, it traps, the host panicked with `text`, at `K F (keep h)`. -/
def PanicSpecD (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (C : IProp GF)
    (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (lpc : UInt32) (maxP : Nat) (f : Func) (SP : Nat) (Dp : IProp GF)
    (D : Nat) (mp ml loc : UInt32) (K : Nat → NewBody.Keep → Nat) (text : List UInt8) : Prop :=
  ∀ (d Cg : Nat) (sp : UInt32) (h : NearState) (hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (idx : UInt32), d + D < lim.maxCallDepth → SP ≤ sp.toNat → sp.toNat % 8 = 0 → sp.toNat + 16 ≤ 2 ^ 32 → HeapRoomK 8 hl maxP →
    okG F → LogFits h text.length → h.extCosts.cost "read_memory_byte" * text.length < 2 ^ 64 →
    C ⊢ MFunSpecT cfg lim d types[31]! inst mi f Cg
      (fun args => iprop(⌜args = [.i32 mp, .i32 ml, .i32 loc]⌝ ∗
        pPre n g ta A gt lpc SP Dp sp maxP hl live F idx h))
      (fun _ => K F (NewBody.keep h)) (fun _ _ => iprop(False)) (fun _ => panicked Cg h text)

end Defs

end WNear.Binary.DepositPanicSpec
