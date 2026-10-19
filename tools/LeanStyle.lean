module
public meta import Mathlib.Tactic.Linter.TextBased
import all Mathlib.Tactic.Linter.TextBased

/-!
Run the text-based style linters from the repository's pinned Mathlib.
`--fix` applies Mathlib's formatting fixes and then checks the result again.
This is source-style formatting, not a full Lean pretty-printer.
-/

open Mathlib.Linter.TextBased

public meta def main (args : List String) : IO UInt32 := do
  let fix := args.head? == some "--fix"
  let files := if fix then args.drop 1 else args
  if files.isEmpty then
    IO.eprintln "Usage: LeanStyle.lean [--fix] FILE.lean ..."
    return 2
  -- Mathlib's semicolon check also matches semicolons inside WAT strings and
  -- comments. Those are meaningful test data, so omit that text-only rule.
  let opts : Lean.Linter.LinterOptions := {
    toOptions := ({} : Lean.Options).setBool `linter.whitespaceBeforeSemicolon false
    linterSets := {} }
  let mut failed := false
  for file in files do
    let path : System.FilePath := file
    let (errors, changed) ← lintFile opts path #[]
    if fix then
      if let some lines := changed then
        IO.FS.writeFile path ("\n".intercalate lines.toList)
      let (remaining, _) ← lintFile opts path #[]
      formatErrors remaining .github
      failed := failed || !remaining.isEmpty
    else
      formatErrors errors .github
      failed := failed || !errors.isEmpty
  return if failed then 1 else 0
