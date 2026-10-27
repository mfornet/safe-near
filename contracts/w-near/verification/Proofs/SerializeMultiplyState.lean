import Binary.SerializeMultiply
import NearVM.MeteredWordRules
import NearVM.MeteredScalarRules
import Proofs.StorePairCallerState

/-! Symbolic words and exact low-first memory effects of actual f954. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
structure Words where
  out : UInt32
  aLo : UInt64
  aHi : UInt64
  bLo : UInt64
  bHi : UInt64

def a0 (w : Words) := w.aLo &&& 4294967295
def a1 (w : Words) := w.aLo >>> (32 : UInt64)
def b0 (w : Words) := w.bLo &&& 4294967295
def b1 (w : Words) := w.bLo >>> (32 : UInt64)
def cross0 (w : Words) := b0 w*a1 w
def cross (w : Words) := cross0 w+b1 w*a0 w
def shifted (w : Words) := cross w <<< (32 : UInt64)
def lowWord (w : Words) := shifted w+b0 w*a0 w
def carry (x y : UInt64) : UInt64 := (Numeric.bool (Numeric.irelop64 .lt_u x y)).toUInt64
def highWord (w : Words) :=
  let upper := (carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64))
  upper+b1 w*a1 w+carry (lowWord w) (shifted w)+(w.bHi*w.aLo+w.bLo*w.aHi)
def teeFrame (frame : CallFrame) (index : Nat) (value : UInt64) := {frame with locals:=frame.locals.set! index (.i64 value)}
def frame1 (frame : CallFrame) (w : Words) := teeFrame frame 5 (b0 w)
def frame2 (frame : CallFrame) (w : Words) := teeFrame (frame1 frame w) 6 (a1 w)
def frame3 (frame : CallFrame) (w : Words) := teeFrame (frame2 frame w) 7 (cross0 w)
def frame4 (frame : CallFrame) (w : Words) := teeFrame (frame3 frame w) 8 (b1 w)
def frame5 (frame : CallFrame) (w : Words) := teeFrame (frame4 frame w) 9 (a0 w)
def frame6 (frame : CallFrame) (w : Words) := teeFrame (frame5 frame w) 10 (cross w)
def frame7 (frame : CallFrame) (w : Words) := teeFrame (frame6 frame w) 11 (shifted w)
def finalFrame (frame : CallFrame) (w : Words) := teeFrame (frame7 frame w) 5 (lowWord w)
def lowMemory (memory : Memory) (w : Words) := writeI64 memory w.out.toNat (lowWord w)
def finalMemory (memory : Memory) (w : Words) := writeI64 (lowMemory memory w) (w.out.toNat+8) (highWord w)
def lowStore (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :=
  storeI64 (paid s op 31) index w.out.toNat memory (lowWord w)
def after (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :=
  storeI64 (paid (lowStore s op index memory w) op 29) index (w.out.toNat+8) (lowMemory memory w) (highWord w)
end WNear.Proofs.SerializeMultiply
