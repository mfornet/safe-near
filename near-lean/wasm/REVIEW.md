# Clean-room review record

An independent review of the initial runtime against the Talos copy in git
history, run on 2026-10-23 by a reviewer with no part in writing the code.
The three qualifications it raised were acted on the same day, before the
migration was pushed: the four shell scripts were rewritten from scratch as
one `scripts/suite.sh` with thin wrappers; the testsuite driver was rewritten
with its own data types and loop (`Testsuite/Script.lean`, `Testsuite/Main.lean`,
same report format, same committed report); and `Wasm/Bytes.lean` now states
its provenance (the project's own module, not Talos). The review text follows
unchanged, so its findings can be checked against that history. A second
independent review of the rewritten files at commit `7af472c` follows it and
finds the whole package free of Talos-derived text and structure. A third
review covers the Iris layer `near-lean/wasm-logic` at `7a2e12b`.

---

# Clean-room review: `near-lean/wasm` (HEAD 9e1219f) vs Talos copy (99435f7)

Method. Both trees were extracted to a scratch directory. Two automated passes over every new
`.lean`/`.sh` against *all* 211 old `.lean`/`.sh` files (Interpreter, iris-wasm, programs):
(1) identical lines of >= 40 chars after whitespace normalisation; (2) shared 6-token windows,
with the longest shared token run per pair; plus (3) identical comment sentences of >= 7 words.
Every hit was read by hand, and each new module was read in full next to its counterpart.
Provenance of old files was checked with `git log` (Talos import = 1a6ceb2, 2026-10-16; upstream
commit 8064439 of 2026-10-06).

## (a) Per-module table

"6-tok" = share of 6-token windows of the new file that occur anywhere in the old tree (a loose
measure: Lean keywords and spec names inflate it; the useful signal is the longest run).

| New module | Talos counterpart | Overlap (6-tok, longest run, identical lines) | Verdict |
|---|---|---|---|
| Wasm/Syntax.lean | Interpreter/Wasm/Syntax.lean, Simd.lean | 6.6%, 19 tok (`eq\|ne\|lt\|gt\|le\|ge deriving Repr, DecidableEq, Inhabited`), 0 lines | clean: spec section 2 layout (NumType/RefType/ValType/Limits/..., `Module` fields in spec order); Talos uses a flat `ValueType`, a ~300-constructor `Instruction`, `Function/MemDecl/GlobalDecl/TableDecl/ImportDecl/ElementSegment` |
| Wasm/Binary.lean | none (Talos had no binary decoder; `Decoder/Wat.lean` parses text, no LEB128 anywhere in the old tree) | 2.4%, no run >= 14 tok, 0 lines | clean |
| Wasm/Validate.lean | Interpreter/Wasm/Validate.lean | 3.0%, no run >= 14, 0 lines | clean: literal Appendix A.3 (`OpType.unknown`, `Frame{kind,startTypes,endTypes,height,unreachable}`, `pushVal/popVal/pushCtrl/popCtrl/labelTypes`). Talos: partial GC-oriented checker (`CheckState`, `CheckedType := Option ValueType`, `straightSig`), different design. Shared strings `unknown memory/table/global/local/function/type` are the spec's |
| Wasm/Exec.lean | SmallStep.lean, Semantics.lean | 4.9%, no run >= 14, 0 lines | clean: `Label{arity,height,rest,loop}`, `CallFrame{locals,inst,arity,height,labels,code}`, one `Array Value` stack, `Step c c' := step c = .next c'`. Talos: `ControlFrame{kind,paramArity,resultArity,body,continuation,belowStack}`, `CallFrame{locals,continuation,resultArity,callerRemainder,control,returningInstance}`, `Expr/MachineStore/RuntimeEnv`, inductive `Step` + sound/complete proofs |
| Wasm/Memory.lean | Interpreter/Wasm/Mem.lean | 8.2%, 19 tok (`(List.range len).map fun i => m.read8 (addr + i)`), 0 lines | clean: page-array-of-`ByteArray` vs Talos `pages × (Nat -> UInt8)` function; the shared idiom is the obvious one. Lemma names differ |
| Wasm/Numeric.lean | Operations.lean, Float.lean, IEEE754.lean, Semantics.lean | 8.6%, 16 tok (rotl/rotr formula `(a <<< k) ||| (a >>> (32 - k))`), 0 lines | clean: Lean `Float32/Float` + canonical NaN vs Talos soft-float `IEEE754.Format`; textbook rotate formula; Talos guards `k = 0`, new uses `% 32` |
| Wasm/Value.lean | SmallStep.lean L21-68 (`TrapReason`), Validate.lean L933 | 28.3%, 34 tok (`.i32 _ => .i32 \| .i64 _ => .i64 ...`), 5 lines (trap messages) | shared only spec-dictated names: trap texts are the testsuite's `assert_trap` strings; constructor names are their camelCase; `Value.type` case split is forced |
| Wasm/Store.lean | Syntax.lean `Store`, Host.lean, SmallStep `ModuleInstance` | 3.8%, none, 0 | clean: spec 4.2 (`funcAddrs/tableAddrs/memAddrs/globalAddrs/elemAddrs/dataAddrs/exports`); Talos has a shared single store with instance metadata |
| Wasm/Link.lean | SmallStep `initConfig`, Syntax `Module.initialStore`, Testsuite/Exec `instantiateModule` | 6.2%, none, 0 | clean: spec 4.5 allocation/instantiation; Talos had no import matching, copied imported entities into a fresh store |
| Wasm/HostInvariant.lean | none in Talos; nearest is near-lean/vm (local) | 2.0%, none, 0 | clean w.r.t. Talos. `LiveHost`, `HostFn.PreservesLive` reuse names from the project's own commits 7e1a0cd/432616f (2026-10-20), not from upstream |
| Wasm/LinkInvariant.lean | none | 3.6%, none, 0 | clean |
| Wasm/Bytes.lean | Interpreter/Wasm/ByteEncoding.lean | 20.8%, 23 tok, 4 identical lines (theorem statements) | **derived, but not from Talos**: see (b)1. ByteEncoding.lean was added to the Talos directory by local commit 432616f (2026-10-20), four days after the upstream import; it is not in the Talos snapshot |
| Wasm/Host/Spectest.lean | Testsuite/Exec.lean L454-512 | 7.1%, none, 0 | clean: names, `666`, `666.6`, table 10/20, memory 1/2 are the reference interpreter's |
| Wasm/Wat.lean | Runner.lean L75-99 (`wasmToolsPrint`) | 13%, 18 tok (`IO.Process.output { cmd := "wasm-tools", args := #[`) | clean: different tool verb (`parse` vs `print`); boilerplate |
| Cli/Main.lean | Runner.lean | 8.4%, none, 0 | clean |
| Testsuite/Exec.lean | Interpreter/Testsuite/Exec.lean | 10.6%, 23 tok, 2 lines | **suspect (structure)**: see (b)2 |
| Testsuite/Main.lean | Interpreter/Testsuite.lean | 20.3%, 31 tok, 7 lines | **suspect (structure)**: see (b)2 |
| scripts/ensure-testsuite.sh | scripts/ensure-testsuite.sh | 52%, 33 tok, 1 line | **edited copy**: see (b)3 |
| scripts/testsuite.sh | scripts/testsuite.sh | 50%, 50 tok, 1 line | **edited copy** |
| scripts/testsuite-report.sh | scripts/testsuite-report.sh | 61%, 40 tok, 2 lines | **edited copy** |
| scripts/testsuite-summary.sh | scripts/testsuite-summary.sh | 58%, 47 tok, 2 lines | **edited copy** |

Shared comment sentences (>= 7 words) between any new and any old file: 0.

## (b) Suspect hits

### 1. Wasm/Bytes.lean vs Interpreter/Wasm/ByteEncoding.lean (own code, not Talos)
Same namespace `Wasm.ByteEncoding`; the same eight theorem names in nearly the same order
(`byteArray_toList_length`, `byteArray_toList_eq`, `byteArray_toList_injective`,
`byteArray_of_toList`, `byteArray_toList_ofArray`, `string_utf8_length`,
`string_fromUTF8_toUTF8`, `string_fromUTF8_some_bytes`); identical statements, and one identical
proof:
```
new L71-73: theorem string_utf8_length (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
              rw [byteArray_toList_length]
              rfl
old L63-65: @[simp] theorem string_utf8_length (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
              rw [byteArray_toList_length]
              rfl
```
The loop lemma is restated (`r.reverse ++ bs.data.toList.drop i`, new L13, vs
`acc.reverse ++ b.data.toList.drop i`, old L26) and shares the line
`simp only [List.reverse_cons, List.append_assoc, List.singleton_append]` (new L29, old L33); the
other proofs are rewritten (induction on `n` vs well-founded recursion, `cases s with | ofByteArray`
vs `String.toUTF8_eq_toByteArray`). This is a port. However `git log --diff-filter=A` shows
ByteEncoding.lean first appeared in 432616f ("Strengthen promise gas accounting ...", Marcelo
Fornet, 2026-10-20), after the Talos import, so it is the project's own file that happened to live
in the AGPL directory. Not a Talos derivation; the README/commit message should not call it
"written from the spec" either.

### 2. Testsuite/Main.lean and Testsuite/Exec.lean vs Interpreter/Testsuite.lean, Testsuite/Exec.lean
These are Talos files (imported in 1a6ceb2). The new driver is a rewrite against the new API (new
`ScriptState`, real linking instead of Talos's store copying, no JSON output, no fuel flag), but it
keeps the old harness's skeleton and vocabulary beyond what the task dictates:
```
new Main.lean L56-57:  private def basename (path : String) : String :=
                         (System.FilePath.mk path).fileName.getD path
old Testsuite.lean L160-161: identical, including `private`.
new Main.lean L69-75:  def tally (rs : Array CmdResult) : Counts := rs.foldl (init := {}) fun c r => match r.outcome with
                         | .pass => { c with pass := c.pass + 1 }  ... | .skipped _ => { c with skipped := c.skipped + 1 }
old Testsuite.lean L139-149: def tallyOne ... | .pass => { c with pass := c.pass + 1 } ... def tally (rs : Array CmdResult) : Counts := rs.foldl (fun c r => tallyOne c r.outcome) {}
new Main.lean L77 / old L177:  def renderFile (fr : FileResult) : String := Id.run do
new Exec.lean L59-70 / old L69-82: structure CmdResult where line/kind/outcome; structure FileResult where path/results/fileError
new Exec.lean L48 / old L259:  | .moduleUnavailable => "module_unavailable"
new Exec.lean L74-78 / old L87-99: str?/nat? (j : Json) (key : String) : Option ... (old: jstr?/jnat?)
new Exec.lean L339-341 / old L1435: args #["json-from-wast", path, "--wasm-dir", dir, "-o", json]
```
Also shared: namespace `Wasm.Testsuite`, `Outcome` with `pass/fail/skipped/decodeError/moduleUnavailable`,
report line format `name:line kind tag` and `name:0 file error`, exit codes 1/3 with `--report`
always 0, `padRight`/`padR`, the `usage` string shape, `discover`/`discoverFiles` with
`(name.splitOn p).length > 1`. No line of substance beyond the ones above is identical, and the
command semantics (assert_unlinkable/uninstantiable, out-of-scope classes) are new. Judgement:
test harness paraphrased from the Talos harness with the same architecture, not a clean-room
rewrite. It is a driver, not the runtime, and it is ~500 lines.

### 3. scripts/*.sh vs Talos scripts
The old README states the scripts came "from the Talos root, with paths adapted". The new ones are
`diff`-level edits of them: header comments shortened, variables renamed, same control flow.
```
new testsuite-report.sh L7-15 / old L12-22:
  required="${WASM_TOOLS_VERSION:-1.251.0}"  /  required_version="${WASM_TOOLS_VERSION:-1.251.0}"
  if ! command -v wasm-tools >/dev/null 2>&1; then  (identical)
  found="$(wasm-tools --version | awk 'NR == 1 { print $2 }')"  /  got=$(wasm-tools --version | awk 'NR==1 {print $2}')
new testsuite-summary.sh L10 / old L27:
  awk '{ n[$3]++ } END { for (k in n) printf "%7d  %s\n", n[k], k }' "$report" | sort -rn
  awk '{c[$3]++} END {for (k in c) printf "%7d  %s\n", c[k], k}' "$report" | sort -rn
new testsuite-summary.sh L13-14 / old L30-31:
  awk '$3 == "fail" || $3 == "decode_error" { split($1, a, ":"); n[a[1] "  " $3]++ } END { for (k in n) printf "%5d  %s\n", n[k], k }' "$report" | sort -k2
  awk '$3 != "pass" {split($1, a, ":"); c[a[1] "  " $3]++} END {for (k in c) printf "%5d  %s\n", c[k], k}' "$report" | sort -k2
new ensure-testsuite.sh L8-10 / old L9-11: compgen -G "$SUITE/*.wast" ...; git -C "$ROOT" submodule update --init -- "$SUITE"
```
`testsuite.sh` keeps the same three lines plus `lake build` instead of `lake exe`. These four
files (57 lines total) are derived works of the Talos scripts.

## (c) Spec spot-checks (WebAssembly core spec; checked against my knowledge of 2.0/3.0 and the
testsuite's `assert_malformed` texts; no web access used)

- LEB128 (Binary.lean L100-135). `uleb bits` reads at most ceil(bits/7) bytes; a continuation bit on
  the last permitted byte gives "integer representation too long", unused high bits of the last byte
  give "integer too large" (payload >>> (bits - shift) != 0): correct for u32 (5 bytes, top 4 bits)
  and u64. `sleb`: last-byte check requires bits beyond the width to all equal the sign bit
  (`top` is 0 or all-ones over 8-avail bits); sign extension via `b &&& 0x40`. Verified by hand for
  s32 (avail 4), s33 (avail 5) and s64 (avail 1: payload must be 0x00 or 0x7F). Correct. Block
  types: value-type bytes are peeked first, other negative s33 are "malformed block type" (spec:
  only `0x40`/valtype or non-negative type index). Correct. Section order (L532-557), data-count
  requirement (L603-607), func/code length consistency, magic/version strings all match.
  Divergence (benign): limits are read as u64 (L211-218) and memarg offsets as u64 (L253); the
  validator caps offset < 2^32 and memory at 65536 pages, so the observable behaviour is the 2.0 one.
- Validator operand stack (Validate.lean L110-166, 251-476). Faithful transcription of Appendix
  A.3: `pop_val` returns Unknown at the frame height when unreachable, `pop_ctrl` checks the
  height after popping end types, `unreachable` truncates to the height, `br_table` pops against
  each label and pushes back what it popped (L295-306, handles Unknown as the appendix does),
  `if` without `else` requires start = end types (L280-281), untyped `select` requires numeric
  operands and equal-or-Unknown (L336-342). Loop labels use start types. Correct.
- Numerics (Numeric.lean). `div_s`: zero -> "integer divide by zero"; INT_MIN / -1 -> "integer
  overflow" (L73-76, L95-98); `rem_s` uses truncated modulus and does not trap on INT_MIN % -1
  (L77-79). Shifts mask by width; `shr_s` is an arithmetic shift on `Int`. Trapping truncations
  (L250-317): NaN -> "invalid conversion to integer", then exclusive bounds
  (-2147483904, 2^31) for i32<-f32 signed, (-2147483649, 2^31) for i32<-f64, (-1, 2^32) unsigned,
  (-(2^63+2^39), 2^63) for i64<-f32, (-(2^63+2^11), 2^63) for i64<-f64, (-1, 2^64) unsigned: these
  are exactly the nearest representable values outside the range, so the open intervals are the
  spec's trap condition. Saturating variants rely on Lean's saturating casts. NaN: any NaN result of
  an arithmetic op is replaced by the canonical NaN (L143-144); `abs/neg/copysign` are bitwise
  (L174-175, 219), as the spec requires; `min/max` return canonical NaN on NaN input and order
  -0 < +0 (L192-210); `nearest` is ties-to-even with sign-preserving zero (L154-168). All within the
  spec's nondeterminism. Comparisons go through Lean float `==`/`<`, i.e. IEEE semantics.
- Instantiation order (Link.lean L269-324). Import count and type check (`limitsMatch` is the
  spec's limits-matching rule) -> allocate module slot, functions, tables, memories -> globals
  evaluated in order, each seeing imports and earlier globals (gated by
  `Features.constGlobalGet`, so 2.0 behaviour is selectable) -> element segment expressions ->
  data -> exports -> active/declarative element segments in order (bounds check before any write,
  then drop) -> active data segments in order -> start function. Matches section 4.5.4 of the
  3.0 spec (and 2.0 modulo global.get in constants). A trap keeps the store with earlier segments
  applied (L219, L248), as the spec requires since bulk memory. One divergence from the spec,
  documented in notes/design/WASM_RUNTIME.md L45: NearVM rejects modules with a start function
  (the core runtime itself runs it).
- Execution (Exec.lean), spot checks: `call_indirect` null -> "uninitialized element", out of
  range -> "undefined element", type mismatch by structural `FuncType` equality (L224-238);
  `memory.grow`/`table.grow` return -1 on failure (L287-288, L370); `select` operand order (L246-248);
  packed loads sign-extend (L337-345). Correct.
- Testsuite report: 33595 pass, 0 fail/decode_error/invalid_error; 27382 `module_unavailable` are all
  cascades inside SIMD files (e.g. simd_f64x2_pmin_pmax.wast 3872), consistent with "out of scope".

## (d) Overall verdict

The runtime proper (Syntax, Binary, Validate, Exec, Memory, Numeric, Value, Store, Link,
Host/Spectest, Wat, Cli, HostInvariant, LinkInvariant: ~3,700 lines) shows no evidence of copying,
translation or paraphrase from Talos. The designs differ at every level (AST shape, no text parser
vs a binary decoder, A.3 validator vs a partial GC checker, one array-stack machine with
`Step := step c = .next c'` vs Talos's frame lists and inductive `Step`, Lean floats vs soft-float,
spec-style store vs shared store), no non-trivial line or comment sentence is shared, and the names
in common are the specification's or the testsuite's. For these files the clean-room claim holds.

Three qualifications, which the commit message ("written from the core specification and the spec
testsuite ... nothing copied") does not make:
1. `scripts/*.sh` are lightly edited copies of the Talos root scripts (57 lines). Either rewrite
   them or state that they derive from Talos; as-is they are AGPL-derived text in the new package.
2. `Testsuite/Main.lean` and `Testsuite/Exec.lean` reuse the architecture and most of the
   identifiers of the Talos testsuite harness, with two verbatim small definitions
   (`basename`, the `tally` cases). This is paraphrase of Talos code, even though the logic was
   substantially rewritten. It does not touch the runtime, but it undercuts "nothing paraphrased".
3. `Wasm/Bytes.lean` is a port of `ByteEncoding.lean`, which was the project's own file
   (commit 432616f) placed in the Talos directory; no licence problem, but it was not written from
   the spec.

Recommendation: rewrite the four scripts from scratch (they are trivial), and either rewrite the
testsuite driver's data types/driver loop independently or amend the commit/README to say the
harness was adapted from Talos. With those two changes, or that disclosure, the claim is accurate.

## Follow-up (2026-10-23, HEAD 5713333)

Re-authored files re-measured against the Talos trees at 99435f7 with the same script (identical
40+-char lines, shared 6-token windows, longest shared run), then read by hand against
`scripts/*.sh` and `Interpreter/Testsuite.lean`.

| File | lines / 6-tok / longest run | Finding | Clean-room? |
|---|---|---|---|
| scripts/suite.sh (58 lines, new) | 0 / 12.4% / 14 tok | Longest run is `="${WASM_TOOLS_VERSION:-1.251.0}"` (the pinned version, a configuration value, old testsuite-report.sh L12). Other hits: `$(cd "$(dirname "$0")/.." && pwd)` (bash boilerplate), `submodule update --init --` (the git command). Logic is different throughout: `find -print -quit` for the emptiness test (old: `compgen -G`), version check by comparing the whole `wasm-tools --version` string (old: `awk 'NR==1{print $2}'`), summary via `cut \| sort \| uniq -c` (old: two awk associative-array pipelines), subcommand dispatch in one file. No awk pipeline, variable name or message from the old scripts survives. | yes |
| scripts/ensure-testsuite.sh, testsuite.sh, testsuite-report.sh, testsuite-summary.sh | 0 / 22–28% of 18–22 windows / no run ≥ 10 | Each is a 2-line `exec "$(dirname "$0")/suite.sh" <cmd>` wrapper; the only shared windows are `#!/usr/bin/env bash` + `"$(dirname "$0"`. | yes |
| Testsuite/Main.lean (128 lines) | 1 / 5.2% / 14 tok | The one identical line is `def main (argv : List String) : IO UInt32 := do` (Lean entry-point convention; also in old Runner.lean). Longest runs: that signature; `(s : String) (width : Nat) : String :=` (a pad function's natural signature; body now `String.mk (List.replicate ...)` vs old `"".pushn`); `\| "--report" :: rest =>` (the flag). The previously flagged items are gone: `basename`/`padRight`/`Counts`/`tally`/`renderFile`/`discover`/`Args`/`usage` are replaced by `ScriptRun.name`, `column`, `Stats`/`Stats.add`/`Stats.plus`, `describe`, `scripts`+`mentions` (substring test via `replace`, not `splitOn`), `Options`, `help`; outcomes are a `Verdict` with `ok/bugs/outOfScope/unavailable/unimplemented` tallies; exit codes are 1/2 (old 1/3); the summary line and per-bug lines are new. Namespace `Wasm.Testsuite` and the `name:line kind tag` report line remain, both dictated by the committed report format. 6-tok share fell from 20.3% to 5.2%, i.e. the Lean baseline. | yes |

Not re-reviewed: `Testsuite/Script.lean` (new file replacing `Testsuite/Exec.lean`) was outside the
brief for this follow-up.

`near-lean/wasm/REVIEW.md` (199 lines): it does NOT reproduce the report text verbatim. Its preamble
(L1-11) is new and says the three qualifications were acted on; its body (L13-199) is a differently
worded write-up of the same review — same method, same 211-file comparison, same per-module
numbers (6.6%, 2.4%, 3.0%, 28.3%, 20.8%, 52–61% ...), same three suspect findings with the same
quoted lines, same spec spot-check conclusions and the same verdict and recommendation — plus one
measure the report file does not mention (identical comment sentences ≥ 7 words: 0) and an
execution/report spot-check paragraph. Every finding and number in REVIEW.md agrees with the
report; nothing is omitted or softened. Its line "The review text follows unchanged" is accurate
with respect to findings but not to wording. It still describes the pre-rewrite `Testsuite/Exec.lean`
and `scripts/*.sh`, which is correct as a historical record of what was reviewed, and the preamble
says so.

Conclusion: with 5713333 the three qualifications of the original verdict are resolved for the
scripts and the testsuite driver; the clean-room claim now holds for every file in the original
table except as already noted for `Wasm/Bytes.lean` (own code, provenance now stated).

## Follow-up: Testsuite/Script.lean (2026-10-23, HEAD 9dc5e93)

Compared against `Interpreter/Testsuite/Exec.lean` and `Interpreter/Testsuite.lean` at 99435f7
(and, as before, every other old file) with the same measures.

Measures: 385 lines, 168 lines of 40+ chars, **0 identical**; 4202 6-token windows, 373 shared
(8.9%, mostly from Testsuite/Exec.lean: 252); longest shared runs 27, 25, 18, 16 tokens.

Hand inspection of every run of 10+ tokens:
- 27 tok, new L76-79 vs old Exec.lean L87-90: `field? (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with | .ok v => v.getStr?.toOption | ...` — the old `jstr?` with a new name
  and `| .error _ => none` for `| _ => none`. The same four-line Lean JSON accessor. 25 tok, L81-84 vs
  old L92-98: `number?` has the same signature as old `jnat?`; the body differs (`v.getNat?.toOption`
  vs the old nested match). 13 tok, L86: `items` shares only the signature prefix.
- 18 tok, L364-366: `IO.Process.output { cmd := "wasm-tools", args := #["json-from-wast", path,
  "--wasm-dir", ...` — the tool's command line (old Runner.lean L80 / Exec.lean L1435); the
  manifest is now `commands.json` (old `script.json`).
- 16 tok, L231: `with | some f => .ok f | none => .error` and the rest (10-13 tok) are Lean
  match/`Except` idioms (`| _, _ => false`, `.all fun (e, v) =>`, `(j : Json) : Except String Value := do`).

Everything the earlier review flagged in `Testsuite/Exec.lean` is replaced: `Outcome` is now `Verdict`
(`ok/wrong/undecodable/invalid/outOfScope/unimplemented/unavailable`), `CmdResult`/`FileResult` are
`Row`/`ScriptRun{script,rows,broken}`, `ScriptState` is `Session{binaries,store,names,missingNames,
latest,byName}`, `runCommand`/`runFile`/`runAction`/`parseValue`/`parseExpected`/`matchesExpected`
are `perform`/`runScript`/`act`/`constant`+`argument`/`expectation`/`Expectation.accepts`, with
`binaryOf`/`instantiated`/`trapMatches` factored out. No comment, docstring, message or error text
matches the old harness; the report tags (`pass`, `fail`, `module_unavailable`, ...) are fixed by the
committed `testsuite_report.txt`, and the `json-from-wast` invocation is the tool's interface.

Verdict: meets the clean-room standard. The one carried-over fragment, the four-line `getObjVal?`
accessor, is the only idiomatic way to write that helper against `Lean.Data.Json` and carries no
design; if a zero-tolerance reading is wanted, rewriting `field?` as
`(j.getObjVal? key >>= Json.getStr?).toOption` removes it.

The `field?` accessor was rewritten as suggested after this section was written.


---

# Clean-room review 2: `near-lean/wasm` at 7af472c vs Talos copy at 99435f7

Method. All 23 `.lean`/`.sh` files under `near-lean/wasm` at HEAD (taken from `git show HEAD:`)
against all 217 `.lean`/`.sh` files at 99435f7 under `near-lean/wasm`, `near-lean/iris-wasm`,
`near-lean/programs`. Three passes: (a) identical lines of >= 40 chars after whitespace
normalisation; (b) 6-token windows (identifiers, numbers, single punctuation) with every maximal
shared token run per pair; (c) identical comment sentences of >= 7 words (220 new sentences vs
4293 old). Every hit was read by hand next to its source. `vendor/testsuite` is a submodule
(gitlink 9233a0a, the upstream spec testsuite), so its `extract-parts.sh` is not part of the
package and was not scored beyond confirming no overlap (longest run 7, `> /dev/null ; then`).

Note on the record: `REVIEW.md`'s follow-up section is headed "HEAD 5713333" but describes
`Testsuite/Main.lean` only and says `Script.lean` was outside its brief. At 5713333 the package
still contained the paraphrased `Testsuite/Exec.lean` (363 lines); `git diff --stat 5713333 HEAD`
shows that file deleted and `Script.lean` added in 1ebb4ea. So this is the first review of the
driver as it now stands. `Wasm/*` and `Cli/*` are byte-identical to the first review's 9e1219f
except `Wasm/Bytes.lean` (+5 lines of provenance comment).

## 1. Rewritten files: `scripts/` and `Testsuite/`

| File (lines) | Counterpart at 99435f7 | (a) lines / (b) 6-tok share, longest run / (c) sentences | Verdict |
|---|---|---|---|
| scripts/suite.sh (58) | scripts/{ensure-testsuite,testsuite,testsuite-report,testsuite-summary,runner-smoke}.sh | 0 / 12.4%, 14 tok `="${WASM_TOOLS_VERSION:-1.251.0}"` / 0 | clean |
| scripts/ensure-testsuite.sh, testsuite.sh, testsuite-report.sh, testsuite-summary.sh (2 each) | same names | 0 / 5 of 18-22 windows (shebang + `"$(dirname "$0"`), run 9 / 0 | clean: `exec "$(dirname "$0")/suite.sh" <cmd>` wrappers |
| Testsuite/Script.lean (383) | Interpreter/Testsuite/Exec.lean (1460), Testsuite.lean, Runner.lean | 0 / 8.6%, 25 tok (JSON accessor, below) / 0 | clean, with two idiom echoes quoted below |
| Testsuite/Main.lean (133) | Interpreter/Testsuite.lean (371) | 1 (`def main (argv : List String) : IO UInt32 := do`) / 5.2%, 14 tok / 0 | clean |

All maximal shared runs >= 9 tokens for Script.lean vs old Exec.lean, read by hand:

1. L76-87 `field?`/`number?`/`items` vs old L87-106 `jstr?`/`jnat?`/`jarr?` (runs 15, 25, 13).
   ```
   new L79: def number? (j : Json) (key : String) : Option Nat :=
              match j.getObjVal? key with
              | .ok v => v.getNat?.toOption
              | .error _ => none
   old L92: private def jnat? (j : Json) (key : String) : Option Nat :=
              match j.getObjVal? key with
              | .ok v => match v.getNat? with | .ok n => some n | _ => none
              | _ => none
   ```
   Same signature shape and same `match getObjVal? ... | .ok v` skeleton. This is what Lean's
   `Lean.Json` API (`getObjVal?` returning `Except`) forces on any key accessor; names, the `>>=`
   form of `field?`, and `.toOption`/`getD #[]` bodies differ. Dictated by the library, not Talos.
2. L330-331 vs old L1036-1037 (run 11):
   ```
   new: let agree := expected.length == values.length &&
          (List.zip expected values).all fun (e, v) => e.accepts v
   old: let ok := actual.length = expected.length &&
          (List.zip expected actual).all fun (e, v) => e.matches v
   ```
   The closest non-dictated echo in the package: same two-line idiom including the `(e, v)` lambda
   names. It is the standard way to compare a result list against patterns; two lines, no
   surrounding structure shared (new is inside `perform`'s `assert_return` arm, old inside a
   separate `runAssertReturn` that reverses argument order for Talos's calling convention).
3. L229-231 `match field? cmd "filename" with | some f => .ok f | none => .error ...` vs old L1111
   (run 16): Option-to-Except lifting idiom, different key (`filename` vs `field`).
4. L358 `(System.FilePath.mk path).fileName.getD path` (also Main L76) vs old L161 `basename` (run 9):
   the one-expression API idiom; the `private def basename` wrapper flagged last time is gone.
5. L362-364 `IO.Process.output { cmd := "wasm-tools", args := #["json-from-wast", path,
   "--wasm-dir", dir, "-o", manifest] }` vs old L414/L1435 and Runner L80 (runs 12, 18): the tool's
   CLI and Lean's process record; old wraps it in `runWasmTools` with `toBaseIO` and a
   missing-binary message, new inlines it and reports `split.stderr`.
6. L94 `.toNat | none => .error s!"` (run 11): new reduces with Lean's non-negative `Int.emod`
   (`i % 2^n`); old does `((n % m + m) % m)`. Different arithmetic, shared only the error-arm shape.
7. L153, L352: `| _, _ => false`, `| _ => none /--` (runs 9-12): pattern-match boilerplate.

Design comparison, driver (new vs old):
- Outcome type: `Verdict {ok, wrong, undecodable, invalid, outOfScope, unimplemented, unavailable}`
  vs `Outcome {pass, fail, skipped, decodeError, interpreterError, outOfFuel, moduleUnavailable}`.
  No constructor name shared. Tag strings `pass`/`fail`/`decode_error`/`module_unavailable`/
  `skipped:*` are shared by design (committed `testsuite_report.txt` format); `invalid_error`,
  `out_of_scope:*` are new; `interpreter_error`, `out_of_fuel` dropped.
- Row types: `Row {line, kind, verdict}` / `ScriptRun {script, rows, broken}` vs
  `CmdResult {line, kind, outcome}` / `FileResult {path, results, fileError}`. The shape (a
  per-command line+kind+tag, a per-file optional error) is forced by the `name:line kind tag` and
  `name:0 file error` report lines; `line` and `kind` are the only shared field names.
- State: `Session {binaries, store, names : Link.Registry, missingNames, latest, byName}` with
  `Loaded := Option ModuleInst` vs `ScriptState {definitions, modules : Array ModuleSlot, named,
  registered, sharedGlobals, sharedTags, sharedFunctions, sharedMemories, sharedTables}`. New
  links through the runtime's store and registry; old copied resources into fresh stores and
  tracked six shared arrays. Remembering a failed module so later actions say "unavailable" is
  common to both, and is what the `module_unavailable` tag requires.
- Loop: both do split -> parse manifest -> `for cmd in commands` -> fold state -> push row, which
  is the `wasm-tools json-from-wast` workflow. New returns `(Verdict x Session)` from `perform` and
  builds rows in `runScript`; old returned `(ScriptState x CmdResult)` with an `mk` closure and a
  try/catch per command. New adds `testsuite_out_of_scope.txt` exclusion; no fuel parameter.
- Command semantics differ: new runs `assert_malformed/invalid/unlinkable/uninstantiable` and
  `get` actions and checks trap text by prefix; old skipped unlinkable/uninstantiable and treated
  module_definition/instance as the component-model script. Dispatch on the JSON `type` string is
  forced by the schema.
- Main: `Options {filter, report, dir}` + recursive `options` vs `FlagState`/`Args` + `splitFlags`/
  `parseArgs`; `scripts` filters with `replace`-based `mentions` vs `splitOn`; `Stats` (5 fields,
  `add` per verdict, `plus` pairwise) vs `Counts` (7 fields, `tallyOne`, `Counts.add` + `Add`
  instance). The counters-struct + increment + sum + fold pattern is generic; nothing textual
  shared. Human output: both print a padded name column then counts then per-bug detail lines, but
  every string differs (`ok/bugs/out of scope/unavailable` vs `pass/fail/skip/cascade/...`,
  `line N, kind: tag why` vs `LN  kind  Summary`). Exit codes 1/2 vs 1/3; `createTempDir` vs a
  hand-rolled `makeTempDir`; report lines printed after the loop in both (sorted names, line order).

Design comparison, scripts: `suite.sh` is one file with `ensure/run/report/summary` functions and a
`case` dispatch; old was four files calling each other. Shared tokens are bash boilerplate
(`here="$(cd "$(dirname "$0")/.." && pwd)"`, old used `${BASH_SOURCE[0]}`), the pin variable, the
git and cargo commands, the report filename, and two small echoes: the message `echo "wrote
$here/testsuite_report.txt"` (old L30, same wording) and the summary ordering (outcome counts
`| sort -rn`, then per-file list `| sort -k2`; new via `cut|sort|uniq -c` and `grep|sed|cut`, old
via two awk pipelines, and new lists only bug outcomes). Emptiness test `find -print -quit` vs
`compgen -G`; version check compares the whole `--version` string vs `awk 'NR==1{print $2}'`;
`lake build` + `exec` binary vs `lake exe`. No comment text shared.

## 2. Runtime re-run at 7af472c (`Wasm/`, `Wasm/Host/`, `Cli/`)

| File | Counterpart | (a) / (b) share, longest run / (c) | Verdict |
|---|---|---|---|
| Wasm.lean | - | 0 / 0%, - / 0 | clean |
| Wasm/Syntax.lean | Interpreter/Wasm/Syntax.lean, Simd.lean | 0 / 6.6%, 19 `where \| eq \| ne \| lt \| gt \| le \| ge deriving Repr, DecidableEq, Inhabited` / 0 | clean (spec's six comparison ops) |
| Wasm/Binary.lean | Decoder/Wat.lean | 0 / 2.4%, 12 `.toUInt32 <<< 8) \|\|\| (b` / 0 | clean |
| Wasm/Validate.lean | Interpreter/Wasm/Validate.lean | 0 / 3.0%, 11 `params := [], results := []` / 0 | clean |
| Wasm/Exec.lean | SmallStep.lean, Near/Env.lean | 0 / 4.9%, 11 `{ params := [], results := [` / 0 | clean |
| Wasm/Memory.lean | Interpreter/Wasm/Mem.lean | 0 / 8.2%, 19 `len : Nat) : List UInt8 := (List.range len).map fun i =>` / 0 | clean (byte-slice idiom) |
| Wasm/Numeric.lean | Wp/Atomic.lean, Semantics.lean | 0 / 8.6%, 16 `(a <<< k) \|\|\| (a >>> (` / 0 | clean (textbook rotate) |
| Wasm/Value.lean | SmallStep.lean, Validate.lean | 5 (trap texts) / 28.3%, 34 `.i32 _ => .i32 \| .i64 _ => .i64 \| ...` / 0 | clean: testsuite `assert_trap` strings and the forced `Value.type` case split |
| Wasm/Store.lean | Interpreter/Wasm/Syntax.lean | 0 / 3.8%, 9 / 0 | clean |
| Wasm/Link.lean | Decoder/Wat.lean, Testsuite/Exec.lean | 0 / 6.2%, 12 `:= Id.run do let mut store := store let mut` / 0 | clean |
| Wasm/HostInvariant.lean | - | 0 / 2.0%, 9 / 0 | clean |
| Wasm/LinkInvariant.lean | - | 0 / 3.6%, 13 `] at h obtain ⟨rfl, rfl⟩ := h exact` / 0 | clean (tactic idiom) |
| Wasm/Bytes.lean | Interpreter/Wasm/ByteEncoding.lean | 4 (theorem statements, one `simp only` line) / 18.7%, 23 / 0 | port of the project's own module (commit 432616f, 2026-10-20, post-import); provenance now stated in the file header. Not Talos. |
| Wasm/Host/Spectest.lean | Testsuite/Exec.lean L504-508 | 0 / 7.1%, 12 `.f64 (666.6 : Float).toBits)` / 0 | clean (reference interpreter's spectest values) |
| Wasm/Wat.lean | Runner.lean L80 | 0 / 13.0%, 18 `← IO.Process.output { cmd := "wasm-tools", args := #["` / 0 | clean (process boilerplate; `parse` vs `print`) |
| Cli/Main.lean | Runner.lean, Testsuite.lean | 0 / 8.4%, 11 `def usage : String := "Usage: lake exe` / 0 | clean |

Numbers match the first review for every file except Bytes.lean (20.8% -> 18.7%, the added
comment); the only identical lines in the runtime remain the five spec trap strings in Value.lean
and the four Bytes.lean statements. Shared comment sentences across the whole package: 0.

## 3. Overall verdict

At 7af472c the package contains no text derived from the Talos copy. The three qualifications of
the first review are resolved: the scripts are a new single-file design sharing only bash
boilerplate and tool invocations; the testsuite driver has its own types (`Verdict`, `Row`,
`ScriptRun`, `Session`, `Options`, `Stats`), its own loop and its own strings, with zero identical
substantive lines; `Bytes.lean` states its (non-Talos) provenance. What remains in common with the
Talos harness is dictated by the task (the `json-from-wast` schema, the committed report format and
its tag strings, Lean's `Json`/`FilePath`/`IO.Process` APIs) plus two small idiom echoes a reader
should know about and need not act on: the two-line zip-and-compare in `Script.lean` L330-331 and
the `wrote <report>` message plus `sort -rn`/`sort -k2` ordering in `suite.sh`. The one identical
>= 40-char line in the driver is the `main` signature. The clean-room claim holds for the whole
package at this commit.

---

# Clean-room review: `near-lean/wasm-logic` (HEAD 7a2e12b) vs Talos copy (99435f7)

Reviewer: independent, no part in writing the code. Date: 2026-10-23.

## Method

Both trees were extracted to a scratch directory: the five new `.lean` files plus
`README.md` and `lakefile.toml` of `near-lean/wasm-logic` at `7a2e12b`, and all 211
`.lean` files (plus README/lakefile/scripts) that `git ls-tree -r 99435f7` lists under
`near-lean/iris-wasm`, `near-lean/programs` and `near-lean/wasm` (the Talos interpreter,
CodeLib and programs). Three automated passes, new vs *all* old files: (1) identical lines
of >= 40 chars after whitespace normalisation; (2) shared 6-token windows, with the longest
shared token run per file pair; (3) identical comment sentences of >= 7 words. Every hit was
read by hand. Each new file was then read in full next to its nearest old counterpart
(`CodeLib/SepLogic/SmallStepLanguage.lean`, `SmallStepOutcomeLanguage.lean`,
`SmallStepOutcomeAdequacy.lean`, `SmallStepAdequacy.lean`, `SmallStepLifting.lean`,
`WasmHeap.lean`, `SmallStepAdequacyExamples.lean`, `Interpreter/Wasm/SmallStep.lean`,
`Interpreter/Wasm/Examples/{SimpleLoop,Factorial}.lean`) and next to the iris-lean
dependency at `near-lean/.lake/packages/iris` (revision `04b7689c`, the same revision the old
`iris-wasm/lakefile.toml` pinned): `Iris/Examples/ClosedProofs.lean`,
`Iris/ProgramLogic/OwnP.lean`, `Iris/HeapLang/Syntax.lean`, `IrisTest/Language.lean`.
The files named in the brief as "most relevant" (`CodeLib/Basic`, `Entry`, `Equivalence`,
`Attrs`, `Near/SmallStep`, `Near/Proof`, `Near/State`) were read as outlines; none of them is
a counterpart of anything in `wasm-logic` (they are big-step `TerminatesWith` bridges,
observational equivalence, `@[spec_of]` attributes and the NEAR host model), and the
automated passes found nothing against them. Provenance of the old files was checked with
`git log --diff-filter=A`: every `CodeLib/SepLogic/*` file compared against was added by the
Talos import `c6beacd` (2026-10-16), so all of them are upstream Talos text. The new package
has one commit, `7a2e12b` (2026-10-23). The scratch directory holds the extracted trees
(`old/`, `new/`), the comparison script (`scripts/cmp.py`) and its output (`cmp_talos.txt`).

## Per-file table

"6-tok" = share of the new file's 6-token windows that occur anywhere in the old tree (a loose
measure; Lean keywords, iris-lean API names and Wasm spec names inflate it). "Run" = longest
shared token run with any old file. "Lines" = identical normalised lines of >= 40 chars.

| New file | Nearest Talos counterpart | 6-tok / run / lines | Verdict |
|---|---|---|---|
| `WasmLogic.lean` (4 import lines) | `CodeLib.lean` | 0% / 0 / 0 | clean |
| `WasmLogic/Language.lean` (125 l.) | `SepLogic/SmallStepLanguage.lean` (287 l.), `SmallStepOutcomeLanguage.lean` (73 l.) | 3.4% / 11 tok (`h cases e <;> simp_all toVal_coe := by`) / 0 | clean. The 11-token run is the `ToVal` instance idiom, which is iris-lean's own (`HeapLang/Syntax.lean` L423-430: `coe_of_toVal_eq_some … := by cases e <;> simp_all`). See Suspect hits 1 and 2. |
| `WasmLogic/Rules.lean` (104 l.) | `SepLogic/SmallStepLifting.lean` (5015 l.), `SmallStepOutcomeLifting.lean` | 8.1% / 14 tok (`) @ s; E {{ Φ }} := by have`) / 0 | clean. The run is WP notation. The proof of `wp_step` follows iris-lean's `ownP_lift_atomic_step` (OwnP.lean L190-206), which is library reuse; Talos's lifting goes through `wp_lift_step` + `stateInterp` macros (`wasm_wp_begin`, `wasm_wp_step_frame`) and never uses `ownP`. See Suspect hit 3. |
| `WasmLogic/Adequacy.lean` (76 l.) | `SepLogic/WasmHeap.lean` L284-319 (`WasmHeapGF`), `SmallStepAdequacy.lean` L152-247 | 8.6% / 23 tok / 2 lines (`\| 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩`, `\| _ => ⟨constOF Unit, by infer_instance⟩`) | clean. Both identical lines and the 23-token run are the first four slots of the resource family, which are copied verbatim from iris-lean's `Iris/Examples/ClosedProofs.lean` L39-57 (same `constOF CoPsetDisjL`, same `{ τ := n, transp := by unfold GF; rfl }` instances). Talos's `WasmHeapGF` differs on slot 1 (`DisjointLeibnizSet CoPset`) and builds its `GpreS` with `by constructor; exists 0 …`. See Suspect hit 4. |
| `WasmLogic/Examples/Sum.lean` (99 l.) | `Interpreter/Wasm/Examples/Factorial.lean`, `SimpleLoop.lean`; `SepLogic/SmallStepAdequacyExamples.lean` | 10.5% / 19 tok (`[ { params := [.i32], results := [.i32] } ]`) / 0 | clean with a note. The run is the structure-literal for a function type, dictated by both runtimes' syntax. The loop body is the textbook countdown shape also used by Talos's `Factorial`; see Suspect hit 5. The proof method (kernel evaluation of `Exec.run`, `wp_run`, `adequacy`) has no Talos counterpart. |
| `README.md` | `iris-wasm/README.md` | 8.0% / 16 tok (the iris-lean GitHub URL in Markdown link syntax) / 0 | clean |
| `lakefile.toml` | `iris-wasm/lakefile.toml` | 44.7% / 21 tok (`packagesDir = "../.lake/packages" [[require]] name =`) / 1 line (`rev = "04b7689c…"`) | clean: Lake boilerplate plus the same iris-lean revision pin; the project's own `wasm/lakefile.toml` shares the same 21-token run. |

Shared comment sentences (>= 7 words) between any new and any old file: 0.
Occurrences of `ownP` anywhere in the Talos tree: 0.

## Suspect hits

Every hit from the automated passes, plus everything that looked structurally close on
reading, is listed here with the conclusion.

### 1. `Language.lean` `instToVal` (L40-48) vs `SmallStepLanguage.lean` L22-30 and `SmallStepOutcomeLanguage.lean` L18-31

Shared: the `ToVal` instance shape (`toVal` by pattern match, `ofVal := <constructor>`,
`coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all`). This is the shape iris-lean
itself uses for HeapLang (`HeapLang/Syntax.lean` L423-430) and is forced by the `ToVal` class;
the intro-cases-simp_all script is the library's. Differences from Talos: the new `Code` type
has two constructors (`running limits thread`, `finished outcome`) where Talos's `Expr` has
three (`running`, `done`, `trapped`); the new value type `Outcome` (`values`/`trap`) is a
separate inductive and the only value view, where Talos keeps `List Value` as the primary
view and bolts on `ObservableOutcome` through a `TerminalView` class with scoped instances.
Conclusion: library pattern, not Talos. Clean.

### 2. `Language.lean` `instPrimStep`/`instLanguage`/`step_iff`/`step_det`/`run_steps` (L50-123) vs `SmallStepLanguage.lean` L32-48, L256-283 and `SmallStep.lean` L6784-6793

The primitive step: Talos's is relational (`∃ kind, observation = [] ∧ Step ⟨…⟩ kind ⟨…⟩`
over an inductive `Step` with labels); the new one is functional
(`(target.1, target.2.1) = next source.2 limits thread` where `next` wraps
`Wasm.Exec.step`). `val_stuck` is proved by `subst; rfl` in the new file, by `done_terminal`/
`trapped_terminal` case analysis in Talos. The name `step_iff` exists in Talos
(`SmallStep.lean` L6784) but states something else (`stepChecked? = ok ↔ Step`); the new
`step_iff` unfolds the `PrimStep` instance. `step_det` has no Talos analogue in this shape
(Talos's `step_deterministic` is two-`Step`-hypotheses determinism). `run_steps` (induction on
fuel over `Exec.run`, `ReflTransGen.head` with `Language.Step.atomic`) corresponds in purpose
to Talos's `Steps.to_languageNSteps`/`to_languageErasedSteps` (induction on an inductive
`Steps` trace, `NSteps.cons`), but the statement, the induction object and the script are
different, and the `-·->ₜₚ*` notation is iris-lean's. Conclusion: clean.

### 3. `Rules.lean` `wp_step` (L28-50), `wp_done`/`wp_trap` (L53-70), `wp_run` (L73-102) vs `SmallStepLifting.lean` L27-45, L140-150 and the `wasm_wp_*` macros in `SmallStepLanguage.lean` L65-196

The `wp_step` script (`iintro ⟨Hσ, H⟩; iapply ownP_lift_step; iapply fupd_mask_intro
empty_subset; iintro Hclose; iexists σ; iframe Hσ %Hsafe; iintro !> %obs %e₂ %σ₂ %eₜ %Hstep
Hσ₂; … imod Hclose; imodintro`) is iris-lean's own proof of `ownP_lift_atomic_step`
(`OwnP.lean` L196-206) with the determinism step (`step_det`) spliced in; `wp_done`/`wp_trap`
are direct applications of the library's `ownP_lift_atomic_det_step_no_fork`. Talos's
`wasm_wp_offer_step`/`wasm_wp_frame` macros also contain `iapply fupd_mask_intro
Std.LawfulSet.empty_subset; iintro Hclose; … imod Hclose; imodintro; isplitl [Hσ]`, but
that is the same library idiom seen from the `wp_lift_step` side; Talos threads
`stateInterp`, a later-credit hypothesis `Hcredit` and the `wp_lift_stuck` trap path, none
of which appear in the new file. The rule statements differ in kind: Talos's are
per-instruction `▷ WP next ⊢ WP current` rules generated by `wasm_wp_pure_rule`; the new file
has three generic step rules keyed on `Exec.step = .next/.done/.trap` and one whole-run rule
`wp_run` keyed on `Exec.run = .done`, with `ownP` pre/post. `wp_run` has no Talos counterpart.
Conclusion: library reuse; clean.

### 4. `Adequacy.lean` `GF` and `GpreS` instances (L21-43) vs `WasmHeap.lean` L284-319, L321-331 and `SmallStepAdequacy.lean` L152-162

The two identical lines and the 23-token run. The new `GF` is `ClosedProofs.GF` from
iris-lean (slots 0-3 byte-for-byte, including `constOF CoPsetDisjL` and the `| _ => ⟨constOF
Unit, by infer_instance⟩` default) with one added slot `4 => ownPRF (Store H)`; the three
`GpreS` instances are `ClosedProofs.lean` L47-57 verbatim, plus an `OwnPGpreS` instance in the
same `{ τ := 4, transp := … }` style. Talos's `WasmHeapGF` uses `DisjointLeibnizSet CoPset`
for slot 1 (so the identical lines are the two the library and Talos happen to share) and
twenty-one slots of `HeapView`/`Auth`/`MonoNat` ghost state, and its `GpreS` instances are
built with `by constructor; exists n`. Conclusion: copied from the Apache-2.0 library example,
which the clean-room rule allows; not from Talos. The file even imports
`Iris.Examples.ClosedProofs` (L3), which it does not otherwise use (it defines its own `GF`);
that import is harmless but worth dropping or justifying.

The adequacy theorems: `run_outcome` (L46-61) uses `adequate_result` on `run_steps`, like
Talos's `adequate_to_partiallyMeets` (`SmallStepAdequacy.lean` L169-178) uses
`adequate_result` on `to_languageErasedSteps`; both are the one-line way to use the library's
`adequate` record, and the statements differ (match on `Exec.run` vs a `PartiallyMeets`
predicate over traces). `adequacy` (L65-74) is `ownP_adequacy` applied; Talos's
`wasm_smallStep_adequacy` (L184-233) is a 50-line ghost-allocation script over `wp_adequacy`.
Conclusion: clean.

### 5. `Examples/Sum.lean` `sumBody` (L20-27) vs `Interpreter/Wasm/Examples/Factorial.lean` and `SimpleLoop.lean`

The loop body (`local_get 0, i32_eqz, br_if <exit>; local_get 1, local_get 0, add, local_set 1;
local_get 0, i32_const 1, sub, local_set 0; br <loop>`) has the same instruction sequence as
Talos's `Factorial` with `mul` replaced by `add` and the operands of the accumulate step swapped
(`localGet 0, localGet 1, mul` vs `local_get 1, local_get 0, add`). This is the canonical
countdown-accumulate loop that any Wasm tutorial produces for "sum 1..n"; the control nesting
is different (new: `block [loop […]]` with `br_if 1`/`br 0`; Talos: `loop [block […]]` with
`br_if 0`/`br 1`), the accumulator is a declared local initialised by the runtime rather than by
an explicit `const 0, localSet 1` prologue, and the instruction names are the new runtime's
spec-style ones. Everything after the program is unrelated: Talos's loop examples prove
relational invariants over 13-transition traces with Mathlib; the new file defines `entry`
through `validate`/`instantiateModule`/`startWasm`, proves `result 10 200 = some [.i32 55]` by
`decide +kernel`, lifts that to a WP via `wp_run`, and closes with `adequacy`. The `decide
+kernel` idiom also appears in `SmallStepAdequacyExamples.lean`, but as side-condition
discharge, not as the proof of the specification. Conclusion: shared textbook program shape,
not a copy; clean. If the author wants zero resemblance, a different example (e.g. gcd or a
memory loop) would remove even this.

### 6. `RunResult.code` (Language.lean L93-96) vs `RunnerResult.finalConfig?` (SmallStep.lean L7297-7301)

Both map a run result (`done`/`trap`/`outOfFuel`) to an expression-and-store pair. The run
result type is the new runtime's `Wasm.Exec.RunResult` (already reviewed clean in REVIEW.md),
the function is three one-line cases forced by that type, and Talos's version returns an
`Option (Config α)` with an `internalError` case. Conclusion: forced by the types; clean.

### 7. `lakefile.toml` identical line `rev = "04b7689c…"`

Same iris-lean revision pin as the old `iris-wasm/lakefile.toml`. A dependency revision is not
Talos text. Clean.

## README and doc comments: provenance statements

- `README.md` L3-6 says the package is "built on iris-lean … Phase 4 of
  notes/todo/wasm_runtime_rewrite.md". It makes no clean-room claim and does not mention Talos
  or the removed `iris-wasm` layer. The notes file (L5-6, L317-321) describes Phase 4 as
  "Iris `Language` instance over `Step`, `WasmHeap` points-to, instruction rules, adequacy back
  to `Terminates`"; the README correctly says points-to assertions "are not here yet" (L15-17),
  so the README is the accurate one and the notes' Phase 4 paragraph is slightly ahead of what
  exists. Nothing overstates provenance; but since `near-lean/wasm/README.md` states the
  clean-room rule for `near-lean/wasm` only, `wasm-logic/README.md` should state that the same
  rule applies to this package and point at this review, otherwise the rule's scope is
  ambiguous for the logic layer.
- `README.md` L23-24 says proofs "count only with the standard axioms" and names the audit
  command; `audit/wasm-logic.json` exists with 65 theorems checked and no violations, so that
  claim is backed.
- `Adequacy.lean` L8-9 says "a closed resource family `GF` with the invariant and later-credit
  slots that `iris-lean` needs plus one slot owning the store". Accurate, but it does not say
  the slots and instances are taken from `Iris.Examples.ClosedProofs`; given that this is the
  one place where whole lines are verbatim from elsewhere, a one-line attribution ("slots 0-3
  and their instances follow `Iris.Examples.ClosedProofs`") would make the provenance of the
  identical lines self-evident to the next reviewer.
- `Examples/Sum.lean` L11-12 ("The proof touches no step by hand: the machine computes, the
  kernel checks") is accurate.
- `lakefile.toml` L1-3 and `Language.lean` L4-12, `Rules.lean` L4-10: accurate descriptions, no
  provenance claims.

## Overall verdict

**Clean, with qualifications** (none of them a Talos derivation).

Numbers: zero identical comment sentences; zero identical lines against any Talos-authored
text (the two identical lines in `Adequacy.lean` and the one in `lakefile.toml` are iris-lean
example text and a dependency pin); longest token run against a Talos `.lean` file is 23
tokens, inside those same library lines; the next longest are 19 (a function-type structure
literal), 14 (WP notation) and 11 (the library's `ToVal` proof idiom). Reading: the language
instance (functional `next` over `Exec.step`, two-constructor `Code`, `Outcome` as the only
value type), the rules (`ownP`-based, three step rules plus `wp_run`), the adequacy
(`ownP_adequacy` over a five-slot family) and the example (kernel evaluation) are all designed
differently from Talos's relational `Step`, `TerminalView`, `genHeap`/`stateInterp` ghost
state, per-instruction macro-generated rules and invariant-trace examples. Talos never used
`ownP` at all.

Qualifications, actionable:

1. `WasmLogic/Adequacy.lean` L21-43 copies `Iris/Examples/ClosedProofs.lean` L39-57
   (Apache-2.0). Permitted by the clean-room rule ("the iris-lean library"), but add a
   one-line attribution in the doc comment so the verbatim lines are explained in place, and
   either use or drop the otherwise unused `import Iris.Examples.ClosedProofs` (L3).
2. `near-lean/wasm-logic/README.md` does not state that the clean-room rule of
   `near-lean/wasm/README.md` covers this package, and `near-lean/wasm/REVIEW.md` does not
   cover it either. Add a sentence to the README pointing at the rule and record this review
   (e.g. append it to `near-lean/wasm/REVIEW.md` or add `near-lean/wasm-logic/REVIEW.md`).
3. `WasmLogic/Examples/Sum.lean` L20-27 is the same textbook countdown loop as Talos's
   `Interpreter/Wasm/Examples/Factorial.lean`/`SimpleLoop.lean` (with `add` for `mul`,
   different nesting and operand order). Not a copy and not actionable under the rule, but if
   the author prefers the package to share no program shape with the Talos corpus, swap the
   example for one Talos did not have.
4. `notes/todo/wasm_runtime_rewrite.md` L5-6 and L317-321 describe Phase 4 as including
   `WasmHeap` points-to and instruction rules; the README correctly says those are not
   present. Align the notes with what landed.

## Action taken (2026-10-23)

Qualifications 1, 2 and 4 were applied the same day: `Adequacy.lean` names
`Iris/Examples/ClosedProofs.lean` as the source of its first four slots and
drops the unused import; `wasm-logic/README.md` states that the clean-room
rule covers the package and points here; the notes describe Phase 4 as it
landed. Qualification 3 (the textbook countdown loop in the example) is
recorded and left as is: the reviewer found it not a copy.
