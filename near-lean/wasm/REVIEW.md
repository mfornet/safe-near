# Clean-room review record

An independent review of the initial runtime against the Talos copy in git
history, run on 2026-10-23 by a reviewer with no part in writing the code.
The three qualifications it raised were acted on the same day, before the
migration was pushed: the four shell scripts were rewritten from scratch as
one `scripts/suite.sh` with thin wrappers; the testsuite driver was rewritten
with its own data types and loop (`Testsuite/Script.lean`, `Testsuite/Main.lean`,
same report format, same committed report); and `Wasm/Bytes.lean` now states
its provenance (the project's own module, not Talos). The review text follows
unchanged, so its findings can be checked against that history.

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
