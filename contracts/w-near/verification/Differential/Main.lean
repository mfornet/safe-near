import Differential.WNear

/-!
# `wnear-scenarios`: run scenario files against the binary and the model

```
lake exe wnear-scenarios [-v] [path ...]
```

Each path is a scenario file or a directory of them (default `scenarios/`;
`scenarios/slow/` and `scenarios/open/` run only when named). `--only text` runs the scenarios whose
name contains `text`; `-v` prints every receipt.
A file holds one scenario object or an array of them. Exits nonzero when a
scenario finds a discrepancy or is itself broken.
-/

open Lean Scenario WNear WNear.Scenarios

def configDir : System.FilePath := "../../../near-lean/vm/configs"

/-- The scenario files under `p`. Subdirectories named `slow` (megabyte
inputs) and `open` (open findings, which fail by design) are skipped unless
named explicitly. -/
partial def scenarioFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let entries ← p.readDir
    let mut out := #[]
    for e in entries.qsort (·.fileName < ·.fileName) do
      if e.fileName == "slow" || e.fileName == "open" then continue
      out := out ++ (← scenarioFiles e.path)
    pure out
  else if p.extension == some "json" then pure #[p]
  else pure #[]

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  -- `--only text`: run only scenarios whose name contains `text`.
  let only := match args.dropWhile (· != "--only") with
    | _ :: text :: _ => some text
    | _ => none
  let args := match args.dropWhile (· != "--only") with
    | _ :: text :: _ => args.filter (fun a => a != "--only" && a != text)
    | _ => args
  let paths := (args.filter (· != "-v")).map System.FilePath.mk
  let paths := if paths.isEmpty then [System.FilePath.mk "scenarios"] else paths
  let contractBytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode contractBytes with
    | .ok m => pure m
    | .error error => throw (IO.userError error.message)
  let code : Near.Boundary.Code :=
    { code := { module, size := contractBytes.size, hash := "" }, codeOf := fun _ => default }
  let mut failed := 0
  let mut total := 0
  for path in paths do
    for file in ← scenarioFiles path do
      let text ← IO.FS.readFile file
      let json ← match Json.parse text with
        | .ok j => pure j
        | .error e => throw (IO.userError s!"{file}: {e}")
      let scenarios := match json with
        | .arr a => a.toList
        | j => [j]
      for j in scenarios do
        let name := (strD j "name" "").toOption.getD ""
        if let some text := only then
          unless (name.splitOn text).length > 1 do continue
        let start ← IO.monoMsNow
        let version := ((natD j "protocolVersion" Wasm.Near.RuntimeConfig.latestVersion).toOption).getD
          Wasm.Near.RuntimeConfig.latestVersion
        let protocol ← Wasm.Near.RuntimeConfig.load configDir version
        let env : Scenario.Env :=
          { protocol, code, contract := WNear.AccountId.toNear ⟨"wrap.near", by decide⟩, verbose }
        let s ← runScenario (model protocol) env j
        total := total + 1
        match s.error with
        | none =>
          IO.println s!"PASS {file.fileName.getD ""} :: {s.name} ({s.receipts} receipts, {(← IO.monoMsNow) - start} ms)"
        | some e =>
          failed := failed + 1
          let kind := if e.scenario then "BROKEN" else "FAIL"
          IO.println s!"{kind} {file.fileName.getD ""} :: {s.name}"
          for l in e.lines do IO.println s!"  {l}"
        (← IO.getStdout).flush
  IO.println s!"{total - failed}/{total} scenarios pass"
  pure (if failed == 0 then 0 else 1)
