import Bridge.Functions.VecFromElem

/-!
# The shape of a view getter's specification

A view method that returns a `u128` (`ft_total_supply`, `storage_minimum_balance`) calls a
getter `getter(out, contract)` that reads the deserialised contract at `contract` and writes 16
bytes to `out`, using a frame of `F` bytes below the stack pointer. `getterPre` and
`getterPost` are the pre- and postcondition such a getter is specified with; the generic body
of those methods (`U128View`) takes the getter's `MFunSpec` in this shape.
-/

namespace WNear.Binary.Getter

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk)

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of `getter(out, contract)`: the stack pointer `sp` in global `g`, `F`
bytes of stack below it, the 16 bytes at `out` and the contract's bytes `cb`. -/
def getterPre (n g : Nat) (gt : GlobalType) (sp out ft : UInt32) (F : Nat) (ob cb : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 ft]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - F) F ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ft.toNat ] cb)

/-- The postcondition: the getter's 16 bytes `vb` at `out`, the rest as it was (the stack's
contents aside). -/
def getterPost (n g : Nat) (gt : GlobalType) (sp out ft : UInt32) (F : Nat) (vb cb : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - F) F ∗
    n ↦[wms][ out.toNat ] vb ∗ n ↦[wms][ ft.toNat ] cb)

end WNear.Binary.Getter
