import CodeLib.RustStd.Region
import CodeLib.Host.UniversalStdIO
import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.Tactics

/-!
Adapted from Talos at 80644390de3ad4db3055445259a034413ae41577 (AGPL-3.0).
Only the shared byte ownership, call framing and stdio transfers needed by
compiled stream drivers are retained here.
-/

namespace Programs.ProofSupport.StreamMemory
open Wasm Iris Std
open Wasm.SepLogic Wasm.SmallStep

/-- Exclusive initialized ownership of one non-wrapping memory-0 byte range.
Physical in-bounds facts are obtained by combining this ownership with
`stateInterp`; they are not duplicated as an uncoupled pure assertion. -/
def ByteSlice {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (bytes : List UInt8) : IProp (WasmHeapGF host) :=
  iprop(⌜ptr.toNat + bytes.length < UInt32.size⌝ ∗
    pointsToBytes 0 ptr bytes)

/-- A non-wrapping logical byte offset has the expected natural-number
address. -/
theorem byteOffset_toNat (ptr : UInt32) (count : Nat)
    (h : ptr.toNat + count < UInt32.size) :
    (ptr + UInt32.ofNat count).toNat = ptr.toNat + count := by
  have hcount : count < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hcount]
  change (ptr.toNat + count) % 2 ^ 32 = ptr.toNat + count
  rw [Nat.mod_eq_of_lt]
  norm_num [UInt32.size] at h ⊢; exact h

/-- Split and recombine canonical byte ownership at a logical list boundary. -/
theorem ByteSlice_append {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (left right : List UInt8) :
    ByteSlice (host := host) ptr (left ++ right) ⊣⊢
      iprop(ByteSlice ptr left ∗
        ByteSlice (ptr + UInt32.ofNat left.length) right) := by
  unfold ByteSlice
  simp only [List.length_append]
  constructor
  · iintro ⟨%hnowrap, Hbytes⟩
    icases (pointsToBytes_append 0 ptr left right).mp $$ Hbytes with
      ⟨Hleft, Hright⟩
    have hleftNowrap :
        ptr.toNat + left.length < UInt32.size := by omega
    have hoffset := byteOffset_toNat ptr left.length hleftNowrap
    have hrightNowrap :
        (ptr + UInt32.ofNat left.length).toNat + right.length <
          UInt32.size := by omega
    isplitl [Hleft]
    · iframe Hleft
      ipureexact hleftNowrap
    · iframe Hright
      ipureexact hrightNowrap
  · iintro ⟨⟨%hleftNowrap, Hleft⟩,
        ⟨%hrightNowrap, Hright⟩⟩
    have hoffset := byteOffset_toNat ptr left.length hleftNowrap
    have hnowrap :
        ptr.toNat + (left.length + right.length) < UInt32.size := by
      rw [hoffset] at hrightNowrap; omega
    isplitl_pureexact hnowrap
    · iapply_frame (pointsToBytes_append 0 ptr left right).mpr


/-- Complete ownership of the Universal host state, existentially hiding the
unused random-host component while fixing both streams and the OOM marker. -/
def Streams [WasmHostStateGS Universal.State]
    (input output : List UInt8) (raised : Bool) :
    IProp (WasmHeapGF Universal.State) :=
  iprop(∃ random : Random.State,
    hostStateOwn
      ({ stdio := { input := input, output := output }
         random := random
         oom := { raised := raised } } : Universal.State))


/-- A call site with its top-of-stack operands already in machine order. -/
def callExpr (absoluteIndex : Nat) (operands : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Expr Universal.State :=
  .running
    ⟨{ callerLocals with values := operands ++ stack },
      .call absoluteIndex :: code, arity, remainder, controls, calls⟩

/-- The caller state after a normal return, with result operands in machine
top-of-stack order. -/
def resumeExpr (results : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Expr Universal.State :=
  .running
    ⟨{ callerLocals with values := results ++ stack },
      code, arity, remainder, controls, calls⟩


end Programs.ProofSupport.StreamMemory
