import Programs.Harness
import Programs.ByteEcho.Program
import Programs.GcdStdio.Program
import Programs.Mergesort.Program

/-!
# `smoke` — run every program under the stdio host

Each program is a zero-argument export that reads its input from the `stdio`
host, computes, and writes its output back. This executable feeds each one a
small input through `Universal.envFor` (which also serves the allocator's
`talos.oom` import) and checks the output bytes. Exit code 1 on any mismatch.

    lake exe smoke
-/

namespace Programs.Smoke

open Wasm

/-- Run export `op` of `m` on `input` bytes and return what reached stdout,
or `none` if the export is missing, the run traps, or fuel runs out. -/
abbrev runBytes := Harness.runBytes

abbrev le32 := Harness.le32

abbrev le64 := Harness.le64

structure Case where
  name     : String
  «module» : Module
  export_  : String
  input    : List UInt8
  expected : List UInt8

def cases : List Case :=
  [ { name := "byte_echo: one byte", «module» := ByteEcho.«module»,
      export_ := "byte_echo", input := [7], expected := [7] }
  , { name := "byte_echo: empty input", «module» := ByteEcho.«module»,
      export_ := "byte_echo", input := [], expected := [] }
  , { name := "gcd(54, 24) = 6", «module» := GcdStdio.«module»,
      export_ := "gcd", input := le64 54 ++ le64 24, expected := le64 6 }
  , { name := "gcd: incomplete input produces no output", «module» := GcdStdio.«module»,
      export_ := "gcd", input := le64 54, expected := [] }
  , { name := "mergesort [3, 1, 2]", «module» := Mergesort.«module»,
      export_ := "mergesort",
      input := le32 3 ++ le32 1 ++ le32 2,
      expected := le32 1 ++ le32 2 ++ le32 3 }
  , { name := "mergesort [9, 1, max, 1, 4, 0]", «module» := Mergesort.«module»,
      export_ := "mergesort",
      input := [9, 1, 0xFFFFFFFF, 1, 4, 0].flatMap le32,
      expected := [0, 1, 1, 4, 9, 0xFFFFFFFF].flatMap le32 }
  ]

def main : IO UInt32 := do
  let mut failed := 0
  for c in cases do
    unless Universal.covers c.«module» do
      IO.println s!"FAIL: {c.name}: module imports something the universal host lacks"
      failed := failed + 1
      continue
    let got := runBytes c.«module» c.export_ c.input
    if got == some c.expected then
      IO.println s!"ok: {c.name}"
    else
      IO.println s!"FAIL: {c.name}\n  expected: {repr c.expected}\n  got:      {repr got}"
      failed := failed + 1
  if failed == 0 then
    IO.println s!"all {cases.length} cases passed"
    return 0
  else
    IO.println s!"{failed} of {cases.length} cases failed"
    return 1

end Programs.Smoke

def main : IO UInt32 := Programs.Smoke.main
