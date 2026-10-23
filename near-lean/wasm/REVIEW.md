# Clean-room review of the initial runtime

An independent reviewer compared the new package, at the commit that deleted
the Talos copy, against every Lean and shell file of the Talos packages kept in
git history at `99435f7`, and spot-checked the semantics against the
specification. The report follows verbatim.

## Remediation after the review

- The four `scripts/*.sh` and `Testsuite/Main.lean`, which the review found to
  be condensed from the Talos harness, were re-authored from scratch with a
  different structure. The coverage report they produce is byte-identical.
- `Testsuite/Exec.lean` keeps the vocabulary of `wasm-tools json-from-wast`
  (command kinds, module files) and the report's outcome tags, which are the
  CI contract; its execution logic is new, as the review states.
- `Wasm/Bytes.lean` carries over lemmas this project wrote on 2026-10-20 inside
  the Talos directory; they are our own, not Talos's.

## Report

# Clean-room review: `near-lean/wasm` (commit 9e1219f) vs the Talos copy (commit 99435f7)

Method. Every `.lean`/`.sh` under the new `near-lean/wasm` (22 files, 4486 lines) was compared
against every `.lean`/`.sh` of the old `near-lean/wasm`, `near-lean/iris-wasm` and
`near-lean/programs` trees at 99435f7 (211 files) with two measures: (a) identical
whitespace-normalised lines of 40+ characters, (b) shared 6-token windows, plus the longest
shared token run per file. Every line hit and every run of 14+ tokens was inspected by hand;
the modules were then read side by side with their Talos counterparts.

## (a) Per-module table

"6-tok" = share of the new file's 6-token windows that occur anywhere in the old trees
(a Lean baseline of 2–5% is unavoidable: `deriving Repr, DecidableEq, Inhabited`, `match ... with`,
`IO.Process.output { cmd := ...`). "lines" = identical 40+-char lines.

| New module | Talos counterpart | lines / 6-tok | Verdict |
|---|---|---|---|
| Wasm/Syntax.lean | Interpreter/Wasm/Syntax.lean, Simd.lean | 0 / 6.6% | clean. Spec section-2 layout (NumType/RefType/ValType, FuncType, Limits, Instr grouped as in the spec, Module with spec field names). Talos has a flat 300-constructor `Instruction`, `Function/MemDecl/GlobalDecl/TableDecl/ImportDecl`. Shared runs are `\| eq \| ne \| lt \| gt \| le \| ge deriving ...` (spec operator names) and `(m : Module) (name : String) : Option Nat` signatures. |
| Wasm/Binary.lean | none (Talos had no binary decoder; Decoder/Wat.lean parses text, Decoder/ProofEval.lean evaluates it) | 0 / 2.4% | clean. Error strings are the testsuite's `assert_malformed` messages. |
| Wasm/Validate.lean | Interpreter/Wasm/Validate.lean | 0 / 3.0% | clean. New = spec Appendix A.3 verbatim in structure (`OpType.known/unknown`, `Frame{kind,startTypes,endTypes,height,unreachable}`, `pushVal/popVal/pushCtrl/popCtrl/labelTypes`). Talos is a partial GC-oriented checker (`CheckState`, `CheckedType := Option ValueType`, `straightSig`). Shared text: spec diagnostics `unknown memory/table/global/function/type`. |
| Wasm/Value.lean | SmallStep.lean (TrapReason), Validate.lean (`Value.toValueType`) | 5 / 28.3% | shared only spec-dictated names. The 5 lines are `\| .integerOverflow => "integer overflow"` etc.: the trap strings the testsuite asserts, constructor names are their camelCase. The 34-token run is the `.i32 _ => .i32 \| .i64 _ => .i64 ...` type-of-value match, the only way to write it. Talos has 6 extra GC/exception traps and `uninitializedElement (index : Nat)`; new has none. |
| Wasm/Numeric.lean | Operations.lean, Float.lean, IEEE754.lean, Semantics.lean | 0 / 8.6% | clean. Talos implements a pure soft-float (`IEEE754.Format`, `encodeRatio`, `roundRatio`); new uses Lean `Float32`/`Float` with canonical-NaN replacement. Shared runs are `(a <<< k) \|\|\| (a >>> (` — the textbook rotate, and Talos guards `k = 0` where new uses `% 32`. Canonical NaN constants are IEEE values. |
| Wasm/Memory.lean | Mem.lean | 0 / 8.2% | clean. Talos `Mem` = `pages × (Nat → UInt8)`; new = `Array ByteArray` with lazily materialised pages. Shared 19-token run is `(List.range len).map fun i => m.read8 (addr + i)`, the obvious idiom (`readList` vs `Mem.readBytes`). |
| Wasm/Store.lean | Syntax.lean (`Store`), Host.lean | 0 / 3.8% | clean. Spec 4.2 store (funcs/tables/mems/globals/elems/datas, `ModuleInst` with `*Addrs`). Talos has one shared store with per-instance metadata and `HostEnv` positional resolvers. |
| Wasm/Exec.lean | SmallStep.lean, Semantics.lean, Continuation.lean | 0 / 4.9% | clean. New: one `Array Value` stack, `Label{arity,height,rest,loop}`, `CallFrame{locals,inst,arity,height,labels,code}`, `Step c c' := step c = .next c'`. Talos: `ControlFrame{kind,paramArity,resultArity,body,continuation,belowStack}`, `CallFrame{...,callerRemainder,control,returningInstance}`, a 3000-line inductive `Step` with separate soundness/completeness. No shared comment, proof or constant. |
| Wasm/Link.lean | Syntax.lean `Module.initialStore`, Testsuite/Exec.lean `instantiateModule`, Host/Registry.lean | 0 / 6.2% | clean. Spec 4.5 allocation as folds; `Registry` is a name→instance list. Talos had no spec instantiation (shared store, `assignResourceIds`, `hydrateStore`). Shared windows are generic `match ... with \| .error e => .error e`. |
| Wasm/HostInvariant.lean | none (Talos `Host.lean` `HostContract`/`HostSpec` are a different idea) | 0 / 2.0% | clean. |
| Wasm/LinkInvariant.lean | none | 0 / 3.6% | clean. |
| Wasm/Bytes.lean | Interpreter/Wasm/ByteEncoding.lean | 4 / 20.8% | derived from the old file, but that file is NOT Talos: see (b). |
| Wasm/Host/Spectest.lean | Testsuite/Exec.lean `spectestGlobal?`, `spectestPrintNames` | 0 / 7.1% | clean. Contents (666, 666.6, table 10/20, memory 1/2, print names) are the reference interpreter's `spectest`. |
| Wasm/Wat.lean | Runner.lean `wasmToolsPrint`, Decoder/Wat.lean | 0 / 13.0% | clean. 18-token run is `IO.Process.output { cmd := "wasm-tools", args := #["` (Lean API + tool name). Talos ran `wasm-tools print` and parsed WAT; new runs `wasm-tools parse` and decodes binary. |
| Wasm.lean | Interpreter.lean | 0 / 0% | clean (import list). |
| Testsuite/Exec.lean | Interpreter/Testsuite/Exec.lean | 2 / 10.6% | suspect-light: same harness design and names, no copied bodies. See (b). |
| Testsuite/Main.lean | Interpreter/Testsuite.lean | 7 / 20.3% | suspect: rewritten, but several helpers reproduced near-verbatim. See (b). |
| Cli/Main.lean | Runner.lean | 0 / 8.4% | clean (decode/validate commands only; Talos runner executed modules). |
| scripts/ensure-testsuite.sh | scripts/ensure-testsuite.sh | 1 / 52.1% | suspect: edited copy. See (b). |
| scripts/testsuite.sh | scripts/testsuite.sh | 1 / 50.4% | suspect: edited copy. |
| scripts/testsuite-report.sh | scripts/testsuite-report.sh | 2 / 61.4% | suspect: edited copy. |
| scripts/testsuite-summary.sh | scripts/testsuite-summary.sh | 2 / 58.3% | suspect: edited copy. |

## (b) Suspect hits, quoted

1. Shell scripts (all four). The old scripts were imported in 1a6ceb2 "from the Talos root, with
   paths adapted" (old README). The new ones are `diff`-small edits of them: header comments
   shortened, variable `required_version` renamed `required`, `lake exe testsuite` replaced by
   `lake build testsuite; exec ./.lake/build/bin/testsuite`. Retained verbatim (new:old lines):
   - every script: `ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"` (boilerplate, but identical).
   - ensure-testsuite.sh 8-10 : 9-11: `if ! compgen -G "$SUITE/*.wast" >/dev/null; then` /
     `git -C "$ROOT" submodule update --init -- "$SUITE"` (old: `"$ROOT/vendor/testsuite"`).
   - testsuite-report.sh 7-13 : 12-19: `"${WASM_TOOLS_VERSION:-1.251.0}"`, `if ! command -v wasm-tools
     >/dev/null 2>&1; then`, `$(wasm-tools --version | awk 'NR == 1 { print $2 }')`.
   - testsuite-summary.sh 7,10,13-14 : 14,27,30-31: `report="${1:-$ROOT/testsuite_report.txt}"`;
     `awk '{ n[$3]++ } END { for (k in n) printf "%7d  %s\n", n[k], k }' "$report" | sort -rn`
     (old: `awk '{c[$3]++} END {for (k in c) printf "%7d  %s\n", c[k], k}' "$report" | sort -rn`);
     `split($1, a, ":"); n[a[1] "  " $3]++ } END { for (k in n) printf "%5d  %s\n", n[k], k }' "$report" | sort -k2`
     (old identical with `c` for `n`).
   These are ~50 lines total and trivial, but they are modified Talos files, not clean-room.

2. Testsuite/Main.lean vs Interpreter/Testsuite.lean. Same namespace `Wasm.Testsuite`, same
   `Args`/`Counts`/`tally`/`renderFile`/`basename`/`usage`/`parseArgs`/`discover` decomposition,
   same exit-code contract (1 fail / 3 setup / `--report` always 0) and report line format
   `{name}:{line} {kind} {tag}`. Reproduced lines (new : old):
   - 56-57 : 160-161 `private def basename (path : String) : String :=` /
     `(System.FilePath.mk path).fileName.getD path`
   - 62-65 : 117-120 `structure Counts where pass : Nat := 0 fail : Nat := 0 skipped : Nat := 0`
   - 69-73 : 139-149 `def tally (rs : Array CmdResult) : Counts :=` ... `| .pass => { c with pass := c.pass + 1 }`
     `| .skipped _ => { c with skipped := c.skipped + 1 }`
   - 77 : 177 `def renderFile (fr : FileResult) : String := Id.run do`
   - 103 : 362 `def main (argv : List String) : IO UInt32 := do`
   - 48-54 : 104-113 the `.wast` discovery loop (`name.endsWith ".wast"`, `(name.splitOn p).length > 1`,
     `out.qsort (· < ·)`).
   The file is not a copy (old 371 lines with JSON output, fuel, Windows temp dirs; new 137), but
   the author plainly had the old harness in view: this is a condensation, not an independent
   rewrite.

3. Testsuite/Exec.lean vs Interpreter/Testsuite/Exec.lean. Shared skeleton: `Outcome`
   (`pass/fail/skipped/decodeError/moduleUnavailable`), `CmdResult{line,kind,outcome}`,
   `FileResult{path,results,fileError}`, `ScriptState`, `runCommand`, `runFile`, the
   `json-from-wast ... --wasm-dir ... -o script.json` flow, `(j : Json) (key : String) : Option String`
   helpers (`str?` vs `jstr?`), `let named := match name? with | some n => (n, ...) :: s.named`,
   `let mut results : Array CmdResult := #[]`, `.moduleUnavailable => "module_unavailable"`.
   The command execution itself is new (Talos had `ModuleSlot`, shared-resource hydration,
   SIMD lane parsing, no spec instantiation). Verdict: derived harness structure, new logic.

4. Wasm/Bytes.lean vs Interpreter/Wasm/ByteEncoding.lean. Same namespace `Wasm.ByteEncoding`,
   same eight theorem names in near-identical order (`byteArray_toList_length`,
   `byteArray_toList_eq`, `byteArray_toList_injective`, `byteArray_of_toList`,
   `byteArray_toList_ofArray`, `string_utf8_length`, `string_fromUTF8_toUTF8`,
   `string_fromUTF8_some_bytes`), identical statements, one identical proof
   (`string_utf8_length`: `rw [byteArray_toList_length]; rfl`), identical simp line
   `simp only [List.reverse_cons, List.append_assoc, List.singleton_append]`, loop lemma with the
   same shape `acc.reverse ++ b.data.toList.drop i`. Other proofs are restructured (induction on
   `n` vs `termination_by`). However `git log` shows ByteEncoding.lean was added by Marcelo
   Fornet in 432616f (2026-10-20), after the Talos import (1a6ceb2, snapshot of Talos
   8064439 dated 2026-10-06), and `git log --all --diff-filter=A` finds no earlier copy. It is
   the project's own code that happened to live inside the AGPL directory. Not a Talos
   derivation; the lineage should simply be acknowledged.

No comment or doc string of any runtime module (Syntax, Binary, Validate, Value, Numeric,
Memory, Store, Exec, Link, invariants) matches Talos text; no proof script, tactic sequence,
unusual constant or error message is shared beyond spec/testsuite-mandated strings.

## (c) Spec spot-checks

- LEB128 (Binary.lean 100-145). `uleb bits` allows ceil(bits/7) bytes; a continuation bit on the
  last allowed byte gives "integer representation too long", unused high payload bits on the last
  byte give "integer too large" (`payload >>> (bits - shift) != 0`). `sleb` requires the bits
  above the value width to all equal the sign bit (`top` must be 0 or all-ones for `8 - avail`
  bits); checked for 32 (avail 4), 33 (avail 5) and 64 (avail 1: payload must be 0x00 or 0x7F).
  Sign extension `value - (1 <<< (shift+7))` when bit 6 of the last byte is set. All match
  spec 5.2.2 and the `binary.wast`/`binary-leb128.wast` expectations. Block types read `sleb 33`
  and reject negatives: correct. Note: memarg offset and limits are read as `uleb 64` (memory64
  grammar); the validator restricts the offset to `< 2^32` and limits to 65536 / 2^32-1, so the
  observable behaviour is the 2.0/3.0 spec's for 32-bit memories.
- Validation (Validate.lean 110-166, 253-476) is Appendix A.3 line for line: `popVal` returns
  `unknown` only at frame height with `unreachable` set; `popCtrl` pops `endTypes` then checks
  height; `if` without else requires `startTypes == endTypes`; `br_table` checks arity per label
  and re-pushes what it popped (so `unknown` survives); untyped `select` requires numeric
  operands and `t1 == t2 || unknown`; `markUnreachable` truncates to height. Constant expressions
  (489-511) accept `global.get` of immutable globals, imported-only unless `constGlobalGet`.
  Divergence: `.i32_binop .add/.sub/.mul` in a const expr is reported `unsupported "extended-const"`
  rather than invalid, which is intentional feature gating.
- Numeric (Numeric.lean). `div_s` traps on divisor 0 and on `INT_MIN / -1`; `rem_s` uses
  `Int.tmod` (sign of dividend, `INT_MIN rem -1 = 0`, no trap); shifts mask by width; `shr_s`
  is arithmetic via `Int`. Trapping truncation bounds (250-294) are exclusive and are the exact
  float neighbours of the integer range: `i32_trunc_f32_s` in (-2147483904, 2147483648),
  `i32_trunc_f64_s` in (-2147483649, 2147483648), unsigned in (-1, 2^32), `i64_trunc_f32_s` in
  (-9223373136366403584, 2^63), `i64_trunc_f64_s` in (-9223372036854777856, 2^63), unsigned in
  (-1, 2^64); NaN gives `invalidConversionToInteger`, otherwise `integerOverflow`. Correct.
  NaN: arithmetic results are canonicalised (`canon32/64`), which is one of the spec-permitted
  nondeterministic outcomes and satisfies `nan:canonical`/`nan:arithmetic` assertions; `abs`,
  `neg`, `copysign`, reinterpret and loads/stores are bitwise and preserve payloads. `fmin/fmax`
  follow the -0/+0 and NaN rules; `nearest` is ties-to-even with sign of zero preserved.
  Divergence worth noting: `f32_demote_f64`/`f64_promote_f32` of a NaN return the canonical NaN
  (spec allows any arithmetic NaN; fine), and `Float32` arithmetic depends on the C library,
  which the module docstring states.
- Instantiation (Link.lean 269-324). Order: import count and type check (`limitsMatch` per spec
  2.3.8 with current table/memory size as `min`); allocate module slot, funcs, tables, mems;
  globals evaluated in order seeing imports and earlier globals; element refs evaluated;
  datas allocated; exports built; active/declarative element segments applied in order (each
  bounds-checked before writing, dropped after); then active data segments; then the start
  function (`instantiate`/`runStart`). This is spec 4.5.4 (elems before datas, start last, a
  trap keeping the effects of earlier segments). The validator's `Features.nearcore` rejects
  start functions as a model gap, documented in notes/design/WASM_RUNTIME.md.

## (d) Overall verdict

The runtime proper — Syntax, Binary, Validate, Value, Numeric, Memory, Store, Exec, Link,
HostInvariant, LinkInvariant, Host/Spectest, Wat, Cli — is a genuine clean-room implementation
written from the specification. Its data structures track the spec's own sections (2, 3/A.3,
4.2, 4.4, 4.5, 5), its designs differ from Talos at every level (binary decoder where Talos had
a WAT parser; A.3 operand stack where Talos had a partial checker; native floats where Talos had
soft-float; a single-stack machine with `Step := step c = .next c'` where Talos had a 6000-line
inductive relation; a spec store where Talos shared one store across instances), and the only
shared text is spec/testsuite-mandated strings and standard Lean idioms.

The claim does not hold without qualification for three peripheral pieces:
1. `scripts/*.sh` are lightly edited copies of the scripts the old README attributes to the Talos
   root. They should be rewritten from scratch or their provenance acknowledged (they are
   ~50 lines of bash and carry no runtime semantics, but AGPL applies to them as written).
2. `Testsuite/Main.lean` and, to a lesser degree, `Testsuite/Exec.lean` are condensations of the
   Talos testsuite harness: same decomposition, type names, outcome tags, report format and
   several helper definitions character-for-character (`basename`, `Counts`, `tally`, the `.wast`
   discovery loop). The execution logic is new, but "nothing paraphrased" is not true of these files.
3. `Wasm/Bytes.lean` is derived from `Interpreter/Wasm/ByteEncoding.lean`, which is the
   project's own 2026-10-20 code, not Talos code; it is clean with respect to Talos but the
   commit message's "written from the spec" framing does not describe it.

Recommended wording: "the runtime is clean-room; the testsuite driver and scripts were rewritten
with the previous harness as a reference, and Bytes.lean carries over our own earlier lemmas."
If a strict no-derivation standard is required, re-author the four scripts and Testsuite/Main.lean
(an hour's work) and keep the rest as is.
