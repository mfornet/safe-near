import Testsuite.Exec

/-!
# `testsuite`: run the WebAssembly spec testsuite

    lake exe testsuite [--report] [--dir DIR] [PATTERN]

Runs the top-level `.wast` files of the testsuite directory (`vendor/testsuite`
unless `--dir` or `$WASM_TESTSUITE` says otherwise), or only those whose name
contains `PATTERN`. The default output is one summary line per file followed
by every bug; `--report` instead prints the coverage report CI diffs: one
`file:line kind outcome` line per command, sorted by file and line.

Exit status: 1 when any command is a bug, 3 when the run could not start,
0 otherwise; `--report` is always 0, since the diff of the report is the gate.
-/

namespace Wasm.Testsuite

structure Options where
  pattern : Option String := none
  report : Bool := false
  dir : Option String := none
  help : Bool := false

def help : String :=
"Usage: lake exe testsuite [--report] [--dir DIR] [PATTERN]
  PATTERN   run only the .wast files whose name contains it
  --report  print the coverage report instead of the summary
  --dir DIR the testsuite directory (default vendor/testsuite or $WASM_TESTSUITE)
  --help    this text"

/-- Parse the command line; `none` on a bad flag or a second pattern. -/
def options (argv : List String) : Except String Options := go argv {}
where
  go : List String → Options → Except String Options
    | [], o => .ok o
    | "--report" :: rest, o => go rest { o with report := true }
    | "--dir" :: d :: rest, o => go rest { o with dir := some d }
    | ["--dir"], _ => .error "--dir needs a directory"
    | "--help" :: _, o | "-h" :: _, o => .ok { o with help := true }
    | arg :: rest, o =>
      if arg.startsWith "-" then .error s!"unknown option {arg}"
      else match o.pattern with
        | some _ => .error "only one PATTERN is allowed"
        | none => go rest { o with pattern := some arg }

/-- The `.wast` files to run, sorted. -/
def selectFiles (dir : System.FilePath) (pattern : Option String) : IO (Array String) := do
  let entries ← dir.readDir
  let wanted := entries.filterMap fun entry =>
    let name : String := entry.fileName
    let chosen := name.endsWith ".wast" &&
      (match pattern with
        | some p => !(name.splitOn p).length.ble 1
        | none => true)
    if chosen then some (dir / name).toString else none
  return wanted.qsort (· < ·)

/-- Counts of each outcome kind in one file. -/
structure Summary where
  pass : Nat := 0
  bugs : Nat := 0
  skipped : Nat := 0
  outOfScope : Nat := 0
  unavailable : Nat := 0

def Summary.add (s : Summary) : Outcome → Summary
  | .pass => { s with pass := s.pass + 1 }
  | .fail _ | .decodeError _ | .invalidError _ => { s with bugs := s.bugs + 1 }
  | .skipped _ => { s with skipped := s.skipped + 1 }
  | .outOfScope _ => { s with outOfScope := s.outOfScope + 1 }
  | .moduleUnavailable => { s with unavailable := s.unavailable + 1 }

def Summary.merge (a b : Summary) : Summary :=
  { pass := a.pass + b.pass, bugs := a.bugs + b.bugs, skipped := a.skipped + b.skipped,
    outOfScope := a.outOfScope + b.outOfScope, unavailable := a.unavailable + b.unavailable }

def Summary.of (results : Array CmdResult) : Summary :=
  results.foldl (fun s r => s.add r.outcome) {}

def Summary.line (s : Summary) : String :=
  s!"{s.pass} pass, {s.bugs} bugs, {s.skipped} skipped, {s.outOfScope} out of scope, " ++
  s!"{s.unavailable} unavailable"

def fileName (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- The human-readable account of one file: its summary and each bug. -/
def account (file : FileResult) : String :=
  let name := fileName file.path
  match file.fileError with
  | some error => s!"{name}: could not run: {error}\n"
  | none =>
    let bugs := file.results.filter (·.outcome.isFailure)
    let lines := bugs.map fun r =>
      let detail := r.outcome.detail.getD ""
      s!"    line {r.line} {r.kind}: {r.outcome.tag} {detail}\n"
    s!"{name}: {(Summary.of file.results).line}\n" ++ String.join lines.toList

/-- The coverage report lines, sorted by file name then line number. -/
def coverage (files : Array FileResult) : List String :=
  let rows := files.toList.flatMap fun file =>
    let name := fileName file.path
    match file.fileError with
    | some error => [(name, 0, s!"{name}:0 file error {error}")]
    | none => file.results.toList.map fun r =>
      (name, r.line, s!"{name}:{r.line} {r.kind} {r.outcome.tag}")
  let ordered := rows.toArray.qsort fun (n, l, _) (n', l', _) => n < n' || (n == n' && l < l')
  ordered.toList.map (·.2.2)

def main (argv : List String) : IO UInt32 := do
  let opts ← match options argv with
    | .ok o => pure o
    | .error e => IO.eprintln s!"{e}\n{help}"; return 3
  if opts.help then IO.println help; return 0
  let fallback := (← IO.getEnv "WASM_TESTSUITE").getD "vendor/testsuite"
  let dir : System.FilePath := opts.dir.getD fallback
  unless ← dir.isDir do IO.eprintln s!"not a directory: {dir}"; return 3
  let files ← selectFiles dir opts.pattern
  if files.isEmpty then IO.eprintln "no .wast file matched"; return 3
  let scratch ← IO.FS.createTempDir
  let skipList ← outOfScopeFiles
  let mut done : Array FileResult := #[]
  for path in files do
    let result ← runFile scratch skipList path
    unless opts.report do IO.print (account result)
    done := done.push result
  IO.FS.removeDirAll scratch
  if opts.report then
    for line in coverage done do IO.println line
    return 0
  let total : Summary := done.foldl (fun s f => s.merge (Summary.of f.results)) {}
  IO.println s!"\n{files.size} files: {total.line}"
  let broken := done.any fun f => f.fileError.isSome || f.results.any (·.outcome.isFailure)
  return if broken then 1 else 0

end Wasm.Testsuite

def main := Wasm.Testsuite.main
