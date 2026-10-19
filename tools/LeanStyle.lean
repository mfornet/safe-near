module
public meta import Mathlib.Tactic.Linter.TextBased
import all Mathlib.Tactic.Linter.TextBased

/-!
Run the text-based style linters from the repository's pinned Mathlib.
`--fix` applies Mathlib's formatting fixes and then checks the result again.
This is source-style formatting, not a full Lean pretty-printer.
-/

open Mathlib.Linter.TextBased

private meta inductive LiteralMode where
  | code | lineComment | blockComment (depth : Nat)
  | string (escaped : Bool) | rawString (hashes : Nat)

/-- Mask literal contents for code-point style checks, preserving line numbers.
Comments remain visible to the style checker; their quotation marks do not
start strings. Raw strings and nested block comments have distinct boundaries. -/
private meta def maskLiterals (source : String) : String := Id.run do
  let chars := source.toList.toArray
  let mut masked := chars
  let mut mode := LiteralMode.code
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    match mode with
    | .code =>
      if c == '-' && chars[i + 1]? == some '-' then
        mode := .lineComment
        i := i + 2
      else if c == '/' && chars[i + 1]? == some '-' then
        mode := .blockComment 1
        i := i + 2
      else if c == 'r' then
        let mut j := i + 1
        while chars[j]? == some '#' do j := j + 1
        if chars[j]? == some '"' then
          mode := .rawString (j - i - 1)
          i := j + 1
        else i := i + 1
      else if c == '"' then
        mode := .string false
        i := i + 1
      else if c == '\'' && chars[i + 2]? == some '\'' then
        masked := masked.set! (i + 1) ' '
        i := i + 3
      else i := i + 1
    | .lineComment =>
      if c == '\n' then mode := .code
      i := i + 1
    | .blockComment depth =>
      if c == '/' && chars[i + 1]? == some '-' then
        mode := .blockComment (depth + 1)
        i := i + 2
      else if c == '-' && chars[i + 1]? == some '/' then
        mode := if depth == 1 then .code else .blockComment (depth - 1)
        i := i + 2
      else i := i + 1
    | .string escaped =>
      if c == '"' && !escaped then mode := .code
      else
        if c != '\n' then masked := masked.set! i ' '
        mode := .string (c == '\\' && !escaped)
      i := i + 1
    | .rawString hashes =>
      if c == '"' && (List.range hashes).all (fun n => chars[i + 1 + n]? == some '#') then
        mode := .code
        i := i + 1 + hashes
      else
        if c != '\n' then masked := masked.set! i ' '
        i := i + 1
  return String.ofList masked.toList

private meta def codePointErrors (opts : Lean.Linter.LinterOptions)
    (path : System.FilePath) : IO (Array ErrorContext) := do
  let source ← IO.FS.readFile path
  let (errors, _) := unicodeLinter opts ((maskLiterals source).splitOn "\n").toArray
  return errors.map fun (error, line) => ⟨error, line, path⟩

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
  -- The Mathlib allowlist is for source notation, not arbitrary contract data.
  -- Check Unicode separately with literals masked, and never auto-replace it.
  let textOpts := { opts with toOptions := opts.toOptions.setBool `linter.unicodeLinter false }
  let mut failed := false
  for file in files do
    let path : System.FilePath := file
    let (errors, changed) ← lintFile textOpts path #[]
    if fix then
      if let some lines := changed then
        IO.FS.writeFile path ("\n".intercalate lines.toList)
      let (remaining, _) ← lintFile textOpts path #[]
      let remaining := remaining ++ (← codePointErrors opts path)
      formatErrors remaining .github
      failed := failed || !remaining.isEmpty
    else
      let errors := errors ++ (← codePointErrors opts path)
      formatErrors errors .github
      failed := failed || !errors.isEmpty
  return if failed then 1 else 0
