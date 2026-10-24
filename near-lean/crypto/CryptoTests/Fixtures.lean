import Lean.Data.Json
import NearCrypto.Bytes

/-!
# Fixture files and the test counters

Fixtures are JSON lines written by `tools/node-conformance` (`crypto-fixtures`). Every field
holding bytes is lowercase hex.
-/

namespace CryptoTests

open Lean NearCrypto

/-- Counts of checks and the failures found. -/
structure Tally where
  checks : Nat := 0
  failures : Array String := #[]

/-- Record one check: `none` passes, `some message` fails. -/
def Tally.record (t : Tally) (where_ : String) (r : Option String) : Tally :=
  match r with
  | none => { t with checks := t.checks + 1 }
  | some m => { checks := t.checks + 1, failures := t.failures.push s!"{where_}: {m}" }

/-- The parsed lines of a JSON-lines file. -/
def readJsonLines (path : System.FilePath) : IO (Array Json) := do
  let text ← IO.FS.readFile path
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty then
      continue
    match Json.parse line with
    | .ok j =>
      out := out.push j
    | .error e =>
      throw (IO.userError s!"{path}: {e}")
  pure out

/-- A string field. -/
def str (j : Json) (k : String) : Except String String :=
  j.getObjValAs? String k

/-- A hex-encoded byte field. -/
def bytes (j : Json) (k : String) : Except String ByteArray := do
  match ofHex (← str j k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

/-- An integer field. -/
def int (j : Json) (k : String) : Except String Int :=
  j.getObjValAs? Int k

/-- A boolean field. -/
def bool (j : Json) (k : String) : Except String Bool :=
  j.getObjValAs? Bool k

/-- Print the outcome and return the exit code. -/
def finish (name : String) (t : Tally) : IO UInt32 := do
  for f in t.failures do
    IO.eprintln s!"FAIL {f}"
  IO.println s!"{name}: {t.checks} checks, {t.failures.size} failures"
  pure (if t.failures.isEmpty then 0 else 1)

end CryptoTests
