import Testsuite.Script

/-!
# `testsuite`: run the WebAssembly spec testsuite

    lake exe testsuite [--report] [--dir DIR] [NAME]

Runs every `.wast` script at the top of the testsuite directory (default
`vendor/testsuite`, or `$WASM_TESTSUITE`), or only those whose file name
contains `NAME`. By default it prints one line per script and one per bug;
with `--report` it prints the coverage report instead, one
`script:line kind tag` line per command in file and line order, which CI
compares with the committed `testsuite_report.txt`.

Exit status: 1 when any command is a bug, 2 on a setup problem, else 0. The
report form always exits 0: the diff is the gate there.
-/

namespace Wasm.Testsuite

structure Options where
  filter : Option String := none
  report : Bool := false
  dir : Option String := none

def help : String :=
"usage: lake exe testsuite [--report] [--dir DIR] [NAME]
  NAME       run only the scripts whose file name contains NAME
  --report   print the coverage report (one line per command)
  --dir DIR  the testsuite directory (default vendor/testsuite, or $WASM_TESTSUITE)"

def options : List String → Except String Options
  | [] => .ok {}
  | "--report" :: rest => (options rest).map fun o => { o with report := true }
  | "--dir" :: dir :: rest => (options rest).map fun o => { o with dir := some dir }
  | ["--dir"] => .error "--dir needs a directory"
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown option {arg}"
    else (options rest).bind fun o =>
      if o.filter.isSome then .error "at most one NAME" else .ok { o with filter := some arg }

/-- Whether `needle` occurs in `hay`. -/
def mentions (hay needle : String) : Bool :=
  needle.isEmpty || (hay.replace needle "").length < hay.length

def scripts (dir : System.FilePath) (filter : Option String) : IO (List String) := do
  let mut found := #[]
  for entry in ← dir.readDir do
    let file := entry.fileName
    if file.endsWith ".wast" && mentions file (filter.getD "") then
      found := found.push (dir / file).toString
  return (found.qsort (· < ·)).toList

/-- Totals of one script. -/
structure Stats where
  ok : Nat := 0
  bugs : Nat := 0
  outOfScope : Nat := 0
  unavailable : Nat := 0
  unimplemented : Nat := 0

def Stats.add (t : Stats) : Verdict → Stats
  | .ok => { t with ok := t.ok + 1 }
  | .outOfScope _ => { t with outOfScope := t.outOfScope + 1 }
  | .unavailable => { t with unavailable := t.unavailable + 1 }
  | .unimplemented _ => { t with unimplemented := t.unimplemented + 1 }
  | _ => { t with bugs := t.bugs + 1 }

def Stats.plus (a b : Stats) : Stats :=
  { ok := a.ok + b.ok, bugs := a.bugs + b.bugs, outOfScope := a.outOfScope + b.outOfScope,
    unavailable := a.unavailable + b.unavailable, unimplemented := a.unimplemented + b.unimplemented }

def ScriptRun.stats (r : ScriptRun) : Stats := r.rows.foldl (fun t row => t.add row.verdict) {}

def ScriptRun.name (r : ScriptRun) : String := (System.FilePath.mk r.script).fileName.getD r.script

def column (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - s.length) ' ')

/-- The human-readable lines for one script. -/
def describe (r : ScriptRun) : List String :=
  match r.broken with
  | some why => [s!"{column r.name 34} broken: {why}"]
  | none =>
    let t := r.stats
    let head := s!"{column r.name 34} {column (toString t.ok) 6} ok   {column (toString t.bugs) 4} bugs   " ++
      s!"{column (toString t.outOfScope) 5} out of scope   {t.unavailable} unavailable"
    let bugs := r.rows.toList.filterMap fun row =>
      if row.verdict.isBug then
        some s!"    line {row.line}, {row.kind}: {row.verdict.tag}  {row.verdict.explanation}"
      else none
    head :: bugs

/-- The report lines of one script, in line order (the rows already are). -/
def reportLines (r : ScriptRun) : List String :=
  match r.broken with
  | some why => [s!"{r.name}:0 file error {why}"]
  | none => r.rows.toList.map fun row => s!"{r.name}:{row.line} {row.kind} {row.verdict.tag}"

def main (argv : List String) : IO UInt32 := do
  let opts ← match options argv with
    | .ok o => pure o
    | .error why => IO.eprintln s!"{why}\n{help}"; return 2
  let dir : System.FilePath := opts.dir.getD ((← IO.getEnv "WASM_TESTSUITE").getD "vendor/testsuite")
  if !(← dir.isDir) then IO.eprintln s!"no testsuite directory at {dir}"; return 2
  let files ← scripts dir opts.filter
  if files.isEmpty then IO.eprintln "no scripts match"; return 2
  let excluded ← outOfScopeScripts
  let scratch ← IO.FS.createTempDir
  let mut runs : List ScriptRun := []
  for file in files do
    let run ← runScript scratch excluded file
    if !opts.report then
      for line in describe run do IO.println line
    runs := runs ++ [run]
  IO.FS.removeDirAll scratch
  if opts.report then
    -- Scripts come sorted by name; rows come in line order.
    for run in runs do
      for line in reportLines run do IO.println line
    return 0
  let total : Stats := runs.foldl (fun t r => t.plus r.stats) {}
  IO.println (s!"\n{files.length} scripts: {total.ok} ok, {total.bugs} bugs, " ++
    s!"{total.outOfScope} out of scope, {total.unimplemented} unimplemented, {total.unavailable} unavailable")
  return if runs.any (fun r => r.broken.isSome || r.stats.bugs > 0) then 1 else 0

end Wasm.Testsuite

def main := Wasm.Testsuite.main
