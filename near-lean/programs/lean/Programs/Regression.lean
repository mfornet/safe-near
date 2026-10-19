import Programs.Harness
import Interpreter.Wasm.Decoder.Wat
import Programs.ByteEcho.Program
import Programs.GcdStdio.Program
import Programs.Mergesort.Program

/-! Boundary and exhaustive small-input checks against independent Lean results.
These executable regressions do not discharge the programs' correctness proofs. -/

namespace Programs.Regression

open Harness

private instance : BEq (Except Failure (List UInt8)) where
  beq
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | _, _ => false

def listsOfLength (alphabet : List UInt32) : Nat → List (List UInt32)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun x => (listsOfLength alphabet n).map (x :: ·)

def sortInputs : List (List UInt32) :=
  (List.range 5).flatMap (listsOfLength [0, 1, 0xFFFFFFFF]) ++
  [5, 8, 16, 31, 63, 64, 65].flatMap fun n =>
    let ascending := (List.range n).map UInt32.ofNat
    [ascending, ascending.reverse, ascending.map fun x => x % 3]

def checkFixture (name wat : String)
    (accept : Except Failure (List UInt8) → Bool) : IO Bool := do
  match Wasm.Decoder.Wat.decode wat with
  | .error error =>
    IO.println s!"FAIL {name}: fixture could not decode: {error}"
    return false
  | .ok m =>
    let result := run m "test" []
    if accept result then return true
    IO.println s!"FAIL {name}: {repr result}"
    return false

def main : IO UInt32 := do
  let mut total := 0
  let mut failed := 0
  for values in sortInputs do
    total := total + 1
    let expected := (values.mergeSort (· ≤ ·)).flatMap le32
    let actual := run Mergesort.«module» "mergesort" (values.flatMap le32)
    if actual != .ok expected then
      failed := failed + 1
      IO.println s!"FAIL mergesort {repr values}: {repr actual}"
  for length in [1, 2, 3, 5, 7, 255, 257, 259] do
    total := total + 1
    let actual := run Mergesort.«module» "mergesort" (List.replicate length 255)
    if actual != .ok [] then
      failed := failed + 1
      IO.println s!"FAIL malformed mergesort input length {length}: {repr actual}"
  for (a, b) in ([(0, 0), (0, 1), (1, 0), (0, 0xFFFFFFFFFFFFFFFF),
      (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF), (0xFFFFFFFFFFFFFFFF, 2),
      (144, 89), (48, 18)] : List (UInt64 × UInt64)) do
    total := total + 1
    let expected := le64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
    let actual := run GcdStdio.«module» "gcd" (le64 a ++ le64 b)
    if actual != .ok expected then
      failed := failed + 1
      IO.println s!"FAIL gcd {a} {b}: {repr actual}"
  for byte in [0, 1, 127, 128, 255] do
    total := total + 1
    let actual := run ByteEcho.«module» "byte_echo" [byte]
    if actual != .ok [byte] then
      failed := failed + 1
      IO.println s!"FAIL byte_echo {byte}: {repr actual}"
  total := total + 2
  if run Mergesort.«module» "mergesort" [] 0 != .error .outOfFuel then
    failed := failed + 1
    IO.println "FAIL zero fuel must be reported as outOfFuel"
  if run Mergesort.«module» "absent" [] != .error (.missingExport "absent") then
    failed := failed + 1
    IO.println "FAIL absent export must be reported as missingExport"
  total := total + 3
  unless ← checkFixture "trap remains distinct from empty output"
      "(module (func (export \"test\") unreachable))"
      (· == .error (.trapped .unreachable)) do
    failed := failed + 1
  unless ← checkFixture "unsupported imports are rejected"
      "(module (import \"missing\" \"host\" (func)) (func (export \"test\")))"
      (· == .error .unsupportedImports) do
    failed := failed + 1
  unless ← checkFixture "entry-point arguments are checked"
      "(module (func (export \"test\") (param i32)))"
      (fun result => match result with | .error (.initializationError _) => true | _ => false) do
    failed := failed + 1
  IO.println s!"{total - failed} passed, {failed} failed ({total} program regressions)"
  return if failed == 0 then 0 else 1

end Programs.Regression

def main : IO UInt32 := Programs.Regression.main
