import Wasm.Syntax

/-!
# Runtime values and traps

Values as the specification's "Runtime Structure" has them. Floats are
carried as their bit patterns, so that a value is a plain piece of data the
kernel can compare; `Wasm.Numeric` interprets them.
-/

namespace Wasm

/-- A reference: null of a given type, a function address in the store, or an
opaque host value. -/
inductive Ref where
  | null (t : RefType)
  | func (addr : Nat)
  | extern (id : Nat)
deriving Repr, DecidableEq, Inhabited

def Ref.type : Ref → RefType
  | .null t => t
  | .func _ => .funcref
  | .extern _ => .externref

inductive Value where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  /-- Bit pattern of an `f32`. -/
  | f32 (bits : UInt32)
  /-- Bit pattern of an `f64`. -/
  | f64 (bits : UInt64)
  | ref (r : Ref)
deriving Repr, DecidableEq, Inhabited

def Value.type : Value → ValType
  | .i32 _ => .i32
  | .i64 _ => .i64
  | .f32 _ => .f32
  | .f64 _ => .f64
  | .ref r => .ref r.type

/-- The default value of a type: zero, or null. -/
def ValType.default : ValType → Value
  | .num .i32 => .i32 0
  | .num .i64 => .i64 0
  | .num .f32 => .f32 0
  | .num .f64 => .f64 0
  | .ref t => .ref (.null t)

/-- Why execution stopped abnormally. The messages are the ones the spec
testsuite expects. -/
inductive Trap where
  | unreachable
  | integerOverflow
  | integerDivideByZero
  | invalidConversionToInteger
  | outOfBoundsMemoryAccess
  | outOfBoundsTableAccess
  | indirectCallTypeMismatch
  | uninitializedElement
  | undefinedElement
  | callStackExhausted
  /-- A host function trapped with its own message. -/
  | host (message : String)
deriving Repr, DecidableEq, Inhabited

def Trap.message : Trap → String
  | .unreachable => "unreachable"
  | .integerOverflow => "integer overflow"
  | .integerDivideByZero => "integer divide by zero"
  | .invalidConversionToInteger => "invalid conversion to integer"
  | .outOfBoundsMemoryAccess => "out of bounds memory access"
  | .outOfBoundsTableAccess => "out of bounds table access"
  | .indirectCallTypeMismatch => "indirect call type mismatch"
  | .uninitializedElement => "uninitialized element"
  | .undefinedElement => "undefined element"
  | .callStackExhausted => "call stack exhausted"
  | .host m => m

end Wasm
