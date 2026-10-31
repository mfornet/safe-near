# wNEAR refinement: status and how to resume

Campaign status on 2026-10-31; proof continuation is active in `codex/wnear-blueprint-refinement`. The prior receipt-domain checkpoint was wound down and pushed as `9988a700`. Details are in `wnear_refinement_proof.md`: M3 for the first method, M6 for JSON arguments (the parser map is `wnear_m6_parser_map.md`), and M8 for the other methods.

The exported refinement is now a checked dispatch over six completed method clauses and eight open full-method obligations and a checked `ft_balance_of` assembly over Conditional general execution-safety and accepted-call compositions and Open rejected-input rollback, with five separately named protocol-instantiation obligations. The global refinement and its withdrawal corollary remain conditional on those leaves. Completed results use only `propext`, `Classical.choice` and `Quot.sound`; never use `bv_decide` or `native_decide`.

The three feasibility gates and their evidence, next checks and failure consequences are tracked in [wnear_feasibility_risks.md](wnear_feasibility_risks.md). The asynchronous gate has passing concrete created-receipt/callback traces, including zero-gas rollback probes; the full asynchronous method proofs remain open.

The user explicitly approved restricting incoming arguments to the receipt-valid
argument-length domain on 2026-10-30. `Context.WF.arguments_length` now requires
`args.length ≤ protocol.wasm.limits.maxArgumentsLength`. No gas, proof-budget,
rollback or accepted-call observation clause changed. This narrows the quantified
domain: the historical 104,858,651-byte input is excluded by the 4 MiB pinned
receipt limit and is now reported as an invalid context before execution.

`Near.validateActions_functionCall_arguments` proves that runtime action-list
validation supplies this exact premise for each member function call. This is
not a proof that receipt delivery establishes every WF field: `applyAttempt`
explicitly leaves incoming-receipt validation unmodeled. Closing that seam
remains a foundation obligation. The pinned nearcore source confirms existing
incoming and delayed receipts call `validate_receipt(...ExistingReceipt)`
before execution (`runtime/runtime/src/lib.rs`, lines 2499–2505, 2565–2574 at
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`). Both modes reach the same
function-call argument check (`action_validation.rs`, lines 131–141, 255–279).
That source review supports the environment restriction; it is not a formal
cross-language correctness proof. `wf_input_fits_register` and
`no_mismatch_witness` exclude the oversized-register witness under the explicit
`InputLimitsOrdered` relation (`maxArgumentsLength ≤ maxRegisterSize`), now
a named open frontier obligation. Executable pinned checks cover
that relation and the argument boundary; kernel instantiation from the pinned
JSON remains open. The old `wf_arguments_unbounded` theorem was removed because
it is false for the reviewed domain; its historical statement is recorded in
the misstatement log. The historical generic host trap and contradiction lemmas
remain checked, but witness existence is no longer a frontier obligation.

## Continuation on 2026-10-31: object case reaches full receipt refinement

`object_absent_refines_init` proves the full receipt result for initialized
represented state, an unregistered account, escape-free object input up to
**4 MiB**, shallow ignored values and trailing whitespace only. It proves
execution safety, sufficient-resource Matches with the **unchanged model gas
allowance**, and arbitrary-resource Matches or resource failure with rollback
and a log prefix. This is additional to the completed valid-array case.

The actual 78/66/65 wrappers restore their frames, retain the owned account and
carry the empty scratch through the real drop. A named `ParserCallContract`
connects this concrete provider to the existing balance execution/cleanup
suffix; the general contract stays Open, and its generic consumer and concrete
contract-instance result remain visibly Conditional where their types contain
a named interface. The closed method case supplies those interfaces concretely.

The initial memory is carved once to retain key/identifier bytes together with
the existing frame and statics; every ignored-reader function address/body is
checked against instantiated code. Input/setup, full body, entry-thread adequacy
and metered activation are composed from these actual resources. No ownership
is recovered from a discarded slice. Context.WF and represented storage supply
the existing host/trie/proof-budget and model-agreement instances.

Gas uses the existing 470-operations-per-byte object-loop bound, a sharper proved
host byte bound and the explicit 4 MiB case limit. Loading, activation, input,
parser, allocator, trie and return charges all fit the original model budget.
The size bound is an explicit case premise, consistent with the pinned deployed
input domain; it is not inferred silently from the weaker `WProtocol` interface.
Escapes, non-shallow ignored values, larger-object contexts, registered accounts,
uninitialized state, general rejected-input rollback and protocol instantiation
remain unresolved.

`object_case_accepted` and `object_case_no_issue` are Proven and Integrated into
the old outside-array assemblies, whose original statement pins are preserved.
Their new admitted leaves exclude both completed array and object cases. The
full balance method and global refinement remain Conditional. General
`IgnoreHyp`, `KeyConditions` and `ValueConditions` remain Open. No allowlist or
model observation/gas statement is relaxed.

The complete strict audit and fresh actual-dependency/readiness gate passed at
2026-10-31T03:53:30+00:00 for proof source `532cf8cf79a681d9fc6ea1e5906f5ffa6ff72ec2cb8ae3c1138e498936160291`. Every prior statement
pin is byte-identical; new interfaces and resource/cost/case definitions are
pinned additively. Frontier policy regressions, Lean style and toolchain checks
passed. Publication requires a matching served revision, statuses, dependencies
and audit evidence.


## Continuation on 2026-10-31: concrete escape-free object-loop instances

`SerdeObjectNoEsc.f228_obj_initial_room` proves the actual function-228 loop
on escape-free object inputs whose ignored fields are accepted by `ign1R`.
The concrete key and account-value bounds, and the existing shallow-ignore
proof, are **Integrated** into this loop. Keys preserve empty scratch before
and after the retained account allocation; the value allocates at most one
page, preserves the exact account bytes and bounds the free list by `max F0 1`.
The existing K646/K169 and ignored-reader charges are retained.

`initial_room` derives the 132-page reserve from actual 1024/2048-page memory
limits after either input-allocation outcome, for input below 2^24 bytes.
The closed loop is **Proven**, using only the standard Lean axioms. The generic
loop and the individual verification-condition instances remain visibly
**Conditional** where their types contain named room or reader contracts.
This does not discharge general `IgnoreHyp`, `KeyConditions` or
`ValueConditions`: those remain **Open**, as do escaped object inputs and
ignored values outside the shallow reader's domain.

This is **not yet Integrated into the method receipt result**. The remaining
work is to extract the object key/identifier static bytes and ignored-reader
code from the actual initial store, carry the result through functions
78/66/65, and fund that whole method path with the unchanged model gas bound.
The completed array receipt case is unchanged. The exact outside-array
accepted/safety leaves, rejected rollback, full balance method and global
refinement retain their previous statuses and premises.

No admission, allowlist scope or existing statement changes. The full strict
audit and fresh actual-dependency/readiness check passed at 2026-10-31T03:06:15+00:00 for proof
source `4f888d6f5fe5c66b662f5a1d3fa89fc65d6b23c9f36c2ffb8a8693fa71551212`. All previous statement pins are unchanged; additions are
pinned. Frontier policy regressions, Lean style and toolchain checks passed.
Publication requires the served revision and dependencies to match this evidence.


## Continuation on 2026-10-31: both valid array string paths reach receipt refinement

`array_absent_refines_init` proves the full receipt result for initialized
represented state, an unregistered account and the exact valid account-id array
grammar with input length below 2^24. This now covers **borrowed and copied**
strings. Execution safety, sufficient-resource Matches and the original model
gas bound, and arbitrary-resource Matches or rollback are proved under the
reviewed runtime/cost/limit premises. Registered accounts, uninitialized state,
object arguments, rejected arguments and other contexts remain unresolved.

The existing `SerdeValueReuse.spec169_model` supplies both string-reader paths.
New scratch cleanup retains the concrete free-list and parser/copy growth
bounds, including empty scratch. The actual 228/78/66/65 wrappers restore their
frames and pass that owned account result into balance execution. The shared
reader charge is bounded by the existing copied-reader charge, so loading,
activation, body, host and trie charges still fit the **unchanged model gas
allowance**. Error-box room comes from the existing growth-plus-six allowance;
no additional unresolved entry-room contract is assumed by the completed case.
Context.WF and represented storage concretely instantiate the same host/trie,
proof-budget and model-agreement interfaces as before.

The shared Wasm proofs now establish the broader statements once. Every existing
copied-only interface is retained as a checked specialization with its original
statement pin unchanged. `copied_case_is_array_case` checks coverage of the old
case by the broader predicate. `array_case_accepted` and `array_case_no_issue`
are **Proven and Integrated** into the existing remaining-case assemblies.
Their original statements are preserved, and their new admitted leaves are the
precise complements of the entire initialized valid-array/absent-account case.
Both old remaining-case results, the full method and global refinement remain
**Conditional**. Rejected-input rollback and the general parser/resource
contracts, including `IgnoreHyp`, `KeyConditions` and `ValueConditions`, remain
Open. No allowlist scope or model observation statement is relaxed.

Next extend the remaining parser/state cases while keeping the full receipt
composition connected. The full strict audit and fresh actual-dependency and
readiness gate passed at 2026-10-31T02:29:19+00:00 for proof source `48b871c4542d61f2f34a41fe3d4a4ba6fdde8e8f71a6269bd19b22582bdf1af3`.
All earlier statement pins are unchanged; new pins are additive. Publication
requires the served revision, statuses and dependencies to match this evidence.


## Continuation on 2026-10-31: copied absent case reaches receipt refinement

The initialized copied-string array branch for an unregistered account now has
full receipt-boundary refinement, not only ending-run adequacy.
`copied_array_absent_refines_init` proves execution safety, Matches and the
original model gas bound with sufficient gas/proof room, and Matches or resource
failure with rollback and log prefix for arbitrary resources. Its domain is the
exact copied-array grammar, initialized represented state, an absent account and
input length below 2^24, under the reviewed runtime/cost/limit environment.

The exact parser cost is bounded using actual Unicode/escape consumption and
valid account length. The initialized body includes input, parser, state read,
lookup, return and cleanup. Loading, eleven activation operations, the body,
host charges and both trie reads all fit the existing model gas allowance.
The standard MethodRunsR contract connects the actual initialized execution to
the boundary theorem. Context.WF and represented storage concretely supply the
host/trie/proof-budget entry interfaces; both actual read postconditions supply
model agreement, including receipt storage-stake failure.

`copied_case_accepted` is **Proven and Integrated** into
`ftBalanceOf_accepted_obligation`. That theorem preserves its original statement
and now performs a checked case split. Its remaining admission is the precise
complement `ftBalanceOf_other_accepted_obligation`, rather than re-admitting the
completed case. Borrowed/object input, registered accounts, uninitialized state
and other accepted cases remain Open. The accepted-call composition, full
ft_balance_of clause and global refinement remain **Conditional** through that
leaf, the complementary execution-safety obligation, rejected-input rollback and the other
method/protocol obligations. No allowlist scope or old statement was relaxed.
`IgnoreHyp`, `KeyConditions`, `ValueConditions` and uniform parser/storage/runtime
contracts remain visible unresolved dependencies; the specific completed case
uses concrete instances rather than assuming these general contracts.

The execution-safety conjunct is also **Proven and Integrated** through
`copied_case_no_issue`. The original `ftBalanceOf_no_issue_obligation` statement
now performs a checked case split and depends only on the precise remaining
safety complement `ftBalanceOf_other_no_issue_obligation`. Both general safety
and accepted-call assembly remain Conditional; their completed case is excluded
from both admitted leaves. Rejected-input rollback remains Open. Next extend
the accepted parser/state cases while preserving these checked compositions.

LSP diagnostics and kernel axiom checks passed for the completed branch. The
published checkpoint requires the strict audit and fresh actual-dependency gate
for proof source `d49fdc130e26f0b982e7778b6e7614d381fed68e5cb5a331a0e112952b66fca8` to pass before commit/publication.

## Continuation on 2026-10-31: initial-store resources and ending-run adequacy

`Statics297` selects the initial table entries once, including input entry 44,
and carves the actual memory image into the parser/UTF-8 tables, static words,
formatter data, empty allocator state and the exact 752-byte frame region.
`startRes297` assembles all of these with code, instance, global, host and gas
ownership from the whole instantiated store. No additional linear entry-resource
availability hypothesis is assumed by this extraction.

`copied_array_absent_body_initial_resources` instantiates the decoded body with
those concrete frame and static resources. `copied_array_absent_body_initial_store`
composes their extraction and funds credits from the store's own gas cell under
an explicit numerical budget and gas-limit premises. It does not assume an
additional, overlapping gas cell alongside whole-store ownership.

`copied_array_absent_adequate` connects the resource construction to the entry
thread through the checked adequacy rule. `copied_array_absent_adequate_host`
uses the actual `startW` thread and extracts both storage-read postconditions,
the final host returning quoted zero and the used-gas bound. These are
**MaybeStuck adequacy** results: they constrain runs that end. They do not prove
termination, fuel sufficiency, general execution safety or arbitrary-resource
rollback. The exact copied-array input, absent key, host/trie correspondence,
proof budget, runtime register/key/return limits and body gas bound remain explicit.

The actual entry frame and its separate activation charge of **11 regular
operations** are checked. Activation and the body budget still need to be
connected to the model's sufficient-gas premise and receipt-boundary run. The
resource and ending-observation results are Proven and Integrated through the
checked entry composition. The full accepted-call edge is still planned; the
accepted, rejected and execution-safety clauses remain Open and the full method
and global refinement remain Conditional. `IgnoreHyp`, `KeyConditions`,
`ValueConditions`, the uniform parser/resource contracts and protocol premises
remain unresolved. No admitted leaf, allowlist entry or old statement is changed.

LSP diagnostics and the host-observation axiom check passed. The live frontier
records the strict audit and fresh dependency-check evidence for proof source
`fe8f3e016693e567eb6638b6affe93b92fbece00f085dd08a000179e0048da6d`; publication requires both gates to pass.

## Continuation on 2026-10-31: code from the instantiated store

`Code297` extracts all input, parser, lookup, return and interface code resources
from `InitialState.funcCells` and assembles `code297_of`. `startCode297` composes
this with the actual instantiated-store ownership split, retaining the raw table,
memory, host, gas and global resources for entry setup. These results are Proven;
component extraction is Integrated into `code297_of`, and that assembly is
Integrated into the checked body proof and initial-store extraction.

`copied_array_absent_body_store_code` consumes the actual persistent function
cells, module instance and memory limit, derives the code, and instantiates
`wInst_ifaceMod` in the complete copied-array absent-account body. The previous
room instantiation is retained. No code availability or module-interface
verification obligation remains in this body instance. Table/static/frame/heap
ownership, host/trie correspondence and proof budget, exact input and absent key,
limits and gas remain explicit. The whole-store extraction is not yet composed
with the body's linear entry resources; its edge to the external accepted clause
is planned, not Integrated. All other input shapes and outcome clauses remain open.

The next entry obligation is to carve the required table entries (including input
entry 44), static data and the 752-byte initial stack without duplicating linear
ownership, then connect initial host/trie and credit resources to this body. The
full method and global refinement remain Conditional. `IgnoreHyp`,
`KeyConditions`, `ValueConditions`, general parser room, protocol premises and
all named admitted leaves remain unresolved. Existing statements and the strict
admission allowance are unchanged. LSP diagnostics and axiom checks passed for
the new body and whole-store extraction. The live frontier records the full
strict audit and dependency-check evidence for proof source digest
`0ae2355f3e37bdd878101d577465b8676d10c397e8c964afe180fc74e97dde72`; publication requires both gates to pass.

## Continuation on 2026-10-31: parser room at the instantiated memory

`ParseStrRoom.roomRun_short` proves every reserve required by the all-outcome
`roomRun` contract of a successful string with at most 64 decoded bytes. It covers
scratch growth, error-box room before and after each append, and every memory
length allowed by `hlAfter`; valid escapes are unrestricted. The model-accepted
string adapter instantiates it with 131 pages of initial allowance.

`copied_parser_pages_le` additionally applies the existing concrete append trace:
a valid account uses at most five scratch growth pages and one owned String page.
`input_pages_le` checks the actual allocator formula and bounds input growth by
257 pages under the existing `< 2^24` input premise. `initial_memory_room` derives
the input-plus-131 allowance at the shared instantiated `InitialState.memLen`
(1024 pages, with a 2048-page limit). `initial_parser_and_body_room` supplies the
parser contract at either post-input memory size and the downstream body budget.

`copied_array_absent_body_initial_memory` composes those facts with the complete
decoded function-297 proof. It has no `roomRun`, `RegOk`, `roomFor` or `HeapRoomK`
hypothesis. Its exact copied-array input, absent account, code/frame ownership,
trie link and proof budget, host/register/return limits and gas credits remain
explicit. It proves that particular decoded body path; constructing its initial
resources from the runtime entry and establishing the full external method
clauses remain open. The older generalized body/model-agreement theorems retain
their original interfaces and room hypotheses.

This instantiates the room obligations for the short-account path, not the
uniform accepting/rejecting parser contract. General `roomRun`, `IgnoreHyp`,
`KeyConditions`, `ValueConditions`, protocol instantiation and the named method
leaves remain unresolved. The exact admission frontier and module allowance are
unchanged. Targeted LSP diagnostics, axiom checks and the full strict axiom
audit passed for proof source digest `008feff4ebf70e1b24cf51f503d868a52e42cb331c1dda50b90fe5c209502cf7`.
The generated statement pins contain additions only. The live frontier records
the final dependency-check and publication freshness for this exact proof source.

## Validated global-composition checkpoint

The proof changes in `39b25d76` passed the complete merged checkpoint on
2026-10-30 at 22:55:48 UTC, for proof source digest
`e75b58b3528d193af0fb4c1019981b37a581e60fe1155c07af31f142d4f6c02d`.
The complete build, strict NearLogic audit, exact named wNEAR admission audit,
unchanged statement pins, fresh LeanArchitect dependency export, seven frontier
policy tests, Lean style and toolchain/isolation checks passed. The audit module
allowance and exact incomplete frontier were not expanded.

Integrated: `refines_wnear_of_clauses` into the existing global theorem;
`all_clauses` and `refines_wnear_with_obligations` connect the reviewed environment
and named remaining methods to that global composition. The new composition
proofs use only the standard three axioms. No remaining method, protocol premise,
uniform parser contract or deployment parse witness was instantiated or discharged.
The new interface stays Open and its assembly and global consumers stay Conditional.

The continuous publisher now runs from the active `8197` worktree through the
existing HTTP/Tailscale endpoint. The verified release for the proof commit was
built at 22:57:24 UTC; the served page displays the current revision and build time
when later notes or metadata updates are published. Served JSON was compared with
the actual Lean export and audit digest, including all fifteen methods, the global
composition's caller edges, and Open `IgnoreHyp`, `KeyConditions` and
`ValueConditions`. Publication health reported no failure.

## Prior receipt-domain wind-down checkpoint

- Full strict validation passed on 2026-10-30 at 22:43 UTC for proof source
  digest `32909647a605d71443b933733287d2dad49bcec02cf45a6244c2e9998098fb74`.
  `tools/wnear_validate.py --update-statements` completed; the generated statement
  changes and frontier hashes were reviewed. Existing admissions remain tracked;
  the deployed refinement is still Conditional.
- Native runtime adapter tests, all 61 default scenarios, and all six frontier
  policy tests passed. The saved oversized-input fixture deliberately exits 1
  with the precise incoming-argument-limit hypothesis violation before execution.
- Warm checkpoint timings: wNEAR compilation 97.2 s, strict wNEAR audit 376.3 s,
  frontier check 95.0 s (export 79.2 s: traversal 72.6 s, estimated imports/startup
  6.6 s). Full audits still run without an audit cache.
- The prior `5885` worktree was wound down and its watcher stopped. The current
  continuation reuses the static HTTP/Tailscale endpoint and transfers continuous
  publishing to the active `8197` worktree; the prior worktree remains preserved.

## Continuation checkpoint

- Latest full-audit baseline before this domain correction: `efd5c8a`; the
  live frontier states the current revision and whether its exact source digest
  has a full audit. The active integration owner is `codex/wnear-blueprint-refinement` in the
  `8197` worktree; no proof agents are assigned.
- Checked end-to-end *decoded body* path: `ft_balance_of`, copied-string array,
  absent account, zero return. It is paired with the model zero-balance result
  in `copied_array_absent_body_model_agreement`. This is not yet an external
  method refinement. It requires the specific JSON shape, `roomRun` parser room,
  initial combined heap budget, well-formed represented state and no storage
  deficit, canonical trie and shared read-proof budget, host and frame ownership,
  and sufficient gas.
- The resource-sufficient accepted-call gas premise now supplies the copied
  body's `< 2^24` input-length premise when the model input equals the binary
  input and the named `BurnLimitV86` holds. The burn-limit upper bound is
  observed in the runtime test but remains unproved for the pinned protocol;
  low-gas calls do not obtain this input bound from the gas premise.
- Next foundation obligation: instantiate pinned argument/register bounds and
  link delivered action validation to the boundary (incoming receipt processing
  is currently unmodeled). The copied-array short-account path now derives parser `roomRun` from the
  instantiated memory; connect its initial resources and return bytes to the
  accepted-call method contract, and discharge room for other parser paths. Extend to
  other inputs and failure outcomes; preserve the named open contracts.
- Development: use the warm Lean LSP and targeted checks. At integration, run
  `just wnear-audit` for the full strict audit; it coordinates with the watcher.
  Build dependencies under the shared lock before opening a proof file whose
  imports became stale: LSP `lake setup-file` can otherwise launch an automatic
  build outside the watcher lock. Build and audit evidence applies only to its exact source digest. The watcher
  coalesces edits, reuses matching frontier exports and refreshes Git metadata
  without rebuilding the book. Timing records are in ignored build output at
  `.lake/build/blueprint/timings.jsonl`; strict audits never use an audit cache.
- Shared-boundary domain correction triggered a broad dependency rebuild:
  unchanged `ParseEscape.lean` alone exceeded 13 minutes of compilation.
  A one-second process sample saw `Lean.Meta` unfolding/weak-head reduction;
  this is a compilation observation, not an axiom-audit timing or proof failure.
  Keep these costs distinct and profile the touched proof before considering
  any incremental refactor. Do not lower proof checks to shorten the rebuild.
- First measured workflow run on 2026-10-30: wNEAR audit 335 s; strict
  frontier export 74 s (68 s traversal, 6 s estimated startup/import); import
  artifact fingerprint about 5–6 s. Split audit groups each spent roughly
  22–25 s rendering pinned statements. These timings motivate investigating
  group-aware pin rendering and dependency-aware caches, but checkpoint and CI
  audits must remain full and strict. No audit results are cached today. Any
  future audit cache must bind exact imported artifacts, toolchain and audit
  configuration, preserve complete coverage and invalidate on changes.
- Before delegation agree on theorem interfaces, ownership, allocator/growth,
  framing, gas and output guarantees. Use separate worktrees/build artifacts;
  hand off commit, declarations, checks and limitations to one integration owner.

## Checked composition and live frontier

`WNear.Binary.Exported.all_methods` composes all 15 exported method clauses. Six
method proofs are complete under the named reviewed environment and size premises;
eight other full method clauses remain admitted; `ft_balance_of` is assembled from three separately admitted execution-safety, accepted-call and rejected-input clauses. The exported
refinement also names five protocol premise admissions. The global statement is
unchanged and remains conditional on these leaves. `PinnedProtocolAvailable` is
a separate open contract: deployment still needs a witness that the pinned JSON
actually parses. The embedded binary size is kernel-checked.

The live proof frontier (endpoint configured locally)
shows the source revision, build time, actual checked dependencies and audit
freshness. `IgnoreHyp`, `KeyConditions`, `ValueConditions` and the named heap-room
contracts remain unresolved; the recent parser loop and scalar results prove
individual transitions, not the whole ignored-value reader. The strict audit and
frontier manifest track the exact admitted leaves and protect statement shapes.

## General free-list bound in state deserialization

The decoded Borsh chain for functions 374, 316, 315, 425, 162 and 161 now has checked variants that preserve an arbitrary supported free-list bound and charge the corresponding allocator cost. These are conditional on allocation room and the stated execution resources. The decoded state reader and its model-state specialization now also accept an arbitrary supported bound F, returning F + 1 after releasing the temporary state buffer. The general-bound state reader is now composed with the actual 82-instruction absent-account path through return and cleanup, with a shared two-read proof budget, exact post-read lookup gas, and a single six-growth room condition. The final heap bound tracks the incoming F. Deriving the entry resources and supported bound from the parser, and integrating this path into the full accepted-call refinement, remain open.

## Parser success handoff to balance cleanup

The actual function 297 success branch, descriptor copies and input-vector drop are checked and composed with the generalized state-read-through-cleanup path: the resulting 114-instruction slice uses a supported arbitrary heap bound after the drop. Separately, the public `okAt` parser result implies the owned account bytes, capacity bounds, address bounds and live-list order needed for that handoff. The public `okAt` parser result is now composed with the 114-instruction theorem by exposing its actual heap witnesses. This composition assumes the named `ParserPostBudget` resource condition, which must establish six-growth room and sufficient gas for those witnesses while preserving the parser result; input-vector ownership, frame resources and the full accepted-call refinement also remain open.

## Copied-array parser call through cleanup

For the specific copied-string array path, the actual function 65 parser call is now composed with the 114-instruction balance suffix, giving a 115-instruction decoded path from the prepared parser-call arguments through absent-account return and cleanup. The parser's recorded growth and free-list bound yield downstream six-growth room from a single initial parser-growth-plus-six allowance; gas uses the actual recorded bound. Parser room and allocation premises, input ownership, host and frame resources, other input forms, and integration into the full accepted-call refinement remain open. The general `ParserPostBudget` obligation remains open for the public parser result.

## Complete decoded body for copied-array absent-account path

The actual function 297 body is now composed for the copied-string array and absent-account case, from its 160-byte frame and interface setup through input, parser, state and balance reads, return and cleanup. The checked path assumes initial input/parser growth room, parser-specific room and allocation conditions, exact input shape, canonical trie, shared proof budget, host/gas and initial frame/static resources. It is a specific conditional path, not the full accepted-call or rejected-input refinement; relating these resources and host conditions to the external method environment remains open.

## Continuation on 2026-10-29: integration with main

Work continues on `codex/wnear-proof-continuation`, starting from PR head `1ea4077` and merging
`main` through `0457bcd` (#46). The harness and dependency-manifest merge conflicts are resolved. The
continuation is published to PR #40 after its validation gates pass.

- #44 moves the recorded-proof check after the value dereference. The repaired
  `NearLogic.prepareStorageCallAux_read` and its callers in `StorageRead.lean` require
  `readProofCost` (lookup plus value bytes) instead of only `lookupProofBound`.
- `lake build NearLogic` passes. The strict axiom audit (`audit/near-logic.json`) checks 56 modules,
  4619 declarations and 3467 theorems with zero violations. LSP also verifies
  `StorageReadWrap.f548_spec_host` with only standard axioms.
- The recipes, wNEAR CI workflow, runtime workflow and periodic checker now build `Bridge`;
  they also explicitly build and strictly audit `NearLogic`. The 16 targeted audit/periodic-check
  regression tests pass, including the new coverage test.
- State-read wrappers, `StateRead*` and initialized `ft_total_supply` are repaired and validated.
  `read_le_proofBound` accounts for the 29-byte state value using the existing model bound.
  `ftTotalSupply_refines_init` passes the LSP axiom check with only the standard three axioms.
  Absent-state reads and `storage_has_key` still need only lookup room.
- The repaired balance lookups and all four view proof files pass LSP diagnostics. The all-state
  theorems for `storage_minimum_balance`, `storage_balance_bounds` and `ft_metadata` pass LSP
  axiom verification with only standard axioms. The combined view build passed (1473 jobs),
  recorded in `/tmp/pr40-view-refinements-build.log`.
- The deposit read-budget integration build passed (1558 jobs): `InternalDeposit`,
  `InternalDepositOverflow`, `DepositBody234`, `NearDepositRuns`, and `NearDepositUninit`.
  The log is `/tmp/pr40-deposit-integration-build.log`.
- **New model agreement groundwork:** `NearDepositModel.lean` exposes every initialized deposit
  path through `nearDeposit_zero`, `nearDeposit_too_small`, `nearDeposit_registered`, and
  `nearDeposit_unregistered`. `nearDeposit_after_registration` separates the fee from minting;
  `deposit_registered_cases` exposes the balance-before-supply checks. The file builds, and
  `nearDeposit_unregistered` passes LSP axiom verification with only standard axioms.
  Keep storageMin symbolic: unfolding its multiplication by 10^19 during broad simplification
  caused excessive kernel work; the separate helper declarations avoid that.
- **Initialized deposit's functional frontier is now closed.** `NearDepositCases` connects
  all five pure classifier outcomes to the model. `NearDepositWords` connects the actual
  host's decoded deposit, predecessor balance, minimum and supply without truncation.
  `NearDepositPre` derives the complete `DepOk` from represented storage and the context,
  and proves `budDep ≤ proofBound` for both the actual and unrecorded comparison hosts.
  The explicit protocol premises are value size ≥ 29, log count ≥ 1, and usage growth
  `85 + numExtraBytesRecord ≤ maxGasBurnt`, alongside `CostsV86`/`LimitsV86`.
- `NearDepositPanicAgreement` proves all panic agreement obligations. `NearDepositEffects`
  flattens `Post234` to exact storage, key, usage and kept-field effects.
  `NearDepositMintWords`, `NearDepositMintModel`, `NearDepositStorageAgreement`, and
  `NearDepositUsageModel` connect the amount, log, header, final storage and usage to
  `mintedOutcome`. `NearDepositSuccessAgreement` includes the final storage-stake check.
- **`near_deposit` is now the sixth completed method refinement under protocol premises.**
  `NearDepositGas.hbound_initialized` discharges loading plus `costDep`: at most 900009
  regular operations, 54 linear-operation charges, host fees at most 2 Tgas, and the
  three write paths within `trieGas`. The non-trie allowance is at most 2.945 Tgas
  against `computeGas = 4 Tgas` under the stated v86 bounds and binary size.
  `NearDepositMethod.nearDeposit_refines_all` combines initialized success/panics with the
  uninitialized case. The targeted build passed (1630 jobs), at
  `/tmp/pr40-deposit-all-build.log`. LSP verifies the gas-bound and all-state refinement
  theorems with only the standard three axioms.
- `NearDepositCostOps`, `NearDepositCostCalls`, `NearDepositCostPanics`,
  `NearDepositCostHosts`, `NearDepositCostBody`, and `NearDepositCostFees` separate bounded
  operation work from host fees and trie paths. `CostsDepositV86` extends `CostsNewV86`
  with the evicted-byte cost, log base/byte costs, and permission for at least one log.
  The added numeric bounds match `runtime_config_v86.json` (log count is 100). They are
  explicit protocol premises for M9, not new axioms or changes to the model.
- `lake build +Bridge.Functions.StateReadModel` passes (`/tmp/pr40-state-read-final.log`).
  An earlier concurrent build failed writing a read-only cached BorshFT.ilean; the local
  link was detached and the sequential build passed. Avoid overlapping builds of the same targets.
- Fixed the declared `Bridge` library's missing-root problem with `globs = ["Bridge.+"]`.
  The original full `lake build Bridge` passed (1679 jobs), including `ParseEscape` and
  `ParseStrEsc`, at `/tmp/pr40-full-bridge-build.log`. The current complete build through
  `just wnear-audit` also passed (2742 jobs, including all new deposit files, Model, Spec,
  Proofs, Differential and all three test executables), at `/tmp/pr40-final-wnear-audit.log`.
  The complete recipe exits successfully: the wNEAR audit checks 408 modules, 57240
  declarations and 52136 theorems. Its only three `sorryAx` dependencies are the original
  declarations in `Proofs.Refinement` (`refines_wnear_exported`, `refines_wnear`, and
  `withdraw_available_wasm`). All pinned statements match `STATEMENTS.md`.
- Current validation: strict NearLogic audit passes (56 modules, 4619 declarations,
  3467 theorems, zero violations); the Python suite runs 294 tests successfully (15 skipped); changed-source
  Lean style, toolchain, node-isolation and umbrella checks pass. The freshly rebuilt
  harness (20 contracts), adapter tests, and all 59 default scenarios pass. Evidence logs
  are `/tmp/pr40-final-python-tests.log` and `/tmp/pr40-continuation-{harness,adapter,scenarios}.log`.


## Parser rejection continuation

- `RejectContract` and `f65_reject` now choose their finite cost **before** the gas ceiling.
  The former `∀ Cg, ∃ K` statement was vacuous (`K = Cg + 1`); entry 7 of the misstatement log
  records the kernel-checked witness and the sweep.
- The former `SerdeRejDefs.lean.txt` WIP is now `Bridge/Functions/SerdeRej.lean`.
  Its scratch/result predicates and `f78_rej` are compiled proofs, conditional on `Rej228`.
- `SerdeRej.f68_scratch` (`SerdeScratchDrop.lean`) frees an empty or grown scratch at
  at most 315 regular operations, preserving all allocations live before parsing.
- `SerdeRej.f66_struct_rej` handles 66's struct-error branch, including scratch cleanup and
  complete stack restoration, at `1000 * regularOpCost + K F` from 228's rejecting contract.
- `FromSliceSpec.struct_reject_uniform` and `f65_struct_reject_uniform` connect that branch to
  the public 66/65 pre/postconditions at a fixed cost for **every** gas ceiling. 65's bound is
  `1045 * regularOpCost + K F`. `decode_reject_cases` splits model rejection into a struct
  failure or trailing non-whitespace.
- These are conditional building blocks, **not** a proof of the full rejecting contract.
  The continuation below adds the trailing branch and discharges 228's EOF case.
  The wrappers use `roomS`; the full rejection contract's heap-room assumptions still need
  validation when its callees are discharged.
- PR-wide whitespace findings are removed from `VecFromElem`, `VecWithCap`, `ParseStrEsc`
  and `StrRepeat`.
- Checkpoint `3bca68c` validation: `just wnear-audit` passes (2746 build jobs; 412 wNEAR modules, 57373
  declarations and 52261 theorems; only the three expected `Proofs.Refinement` sorry
  dependencies). Strict NearLogic remains at zero violations, and pinned statements match.
  The PR-wide Lean style check and `git diff --check origin/main` pass. Evidence:
  `/tmp/pr40-parser-final-audit.log` and `/tmp/pr40-parser-lean-style.log`.


## Trailing-character and EOF rejection continuation

- `AllocFinite.lean` proves `HeapModel.wf.freeList_length_le` and `heapInv_finite`:
  distinct free-cell addresses fit in the heap's byte length, so any existential
  free-list bound can be replaced by `2^32`. This supplies an error-only continuation
  with a fixed finite allocation cost after `strRes` has hidden its free-list bound.
- `SerdeRej.f66_trailing` (`SerdeTrailing.lean`) rejects non-whitespace after a parsed
  struct, drops the parsed account string and the empty scratch, and restores the
  complete frame. It assumes the existing struct-reading callees. Its bound is
  `(2000 + 96*rest.length)*c + costS + costErr(2^32, input.length + 1)`.
- `FromSliceSpec.trailing_reject_uniform` and `f65_trailing_reject_uniform`
  (`FromSliceTrailing.lean`) connect that path to the public parser contracts, with
  readers and costs fixed before **every** gas ceiling. 65 adds 45 regular operations.
- **Concrete rejecting case:** `SerdeRej.f228_eof` and `rej228_eof`
  (`SerdeStructEOF.lean`) prove that 228 rejects EOF after whitespace, by calling 322
  with `EofWhileParsingValue`. No parser-callee specification is assumed.
  `FromSliceSpec.f65_eof_reject_uniform` (`FromSliceEOF.lean`) carries this through
  228 → 78 → 66 → 65 for empty and whitespace-only arguments, using the actual
  instantiated code. `decode_eof` proves that the model rejects these inputs too.
- The full rejecting contract remains open for the other struct error cases.
  The accepted-prefix proof used by the trailing branch still needs the general
  escaped/deep-reader integration; this does not expand the shallow/no-escape accepting
  theorem's coverage by itself.
- Current validation: `just wnear-audit` passes (2751 build jobs; 417 wNEAR modules,
  57624 declarations and 52512 theorems; only the three expected open-refinement
  dependencies). Strict NearLogic has zero violations, and pinned statements match.
  PR-wide Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-trailing-final-audit.log` and `/tmp/pr40-trailing-lean-style.log`.

## Positioned errors and object-key EOF continuation

- `SerdePositionPositive.f645_pos`, `f638_pos`, and `f640_pos` strengthen the
  position-reader contracts with a nonzero line number. The loop invariant proves
  positivity from the actual byte scan; it is not a new parser premise.
- `SerdeErrorPositioned.f639_positioned`, `f325_positioned`, and `f322_positioned`
  retain the allocated error's twelve-byte code and its line/column words in
  `positionedBox`/`heapPos`, at the existing allocation and error cost bounds.
- `SerdeErrorPositioned.f327_positioned` and `f326_positioned`
  (`SerdeFixPosition.lean`) prove the actual `fix_position` path for an error whose
  line is already nonzero: the same box is returned and the stack is restored.
- `SerdeKeyReject.f193_eof` proves `next_key_seed` rejects EOF after whitespace
  with `EofWhileParsingObject`. It preserves the first-key flag, reader input,
  original live allocations and positioned error, and restores the full 176-byte
  stack footprint. Its uniform cost is
  `(600 + 96*wsLen(rest))*c + costErr(F, input.length + 1)`.
- The key-error, positioned peek-error, fix-position wrapper and positive position
  theorems pass Lean LSP axiom verification with only the standard three axioms.
  This is groundwork for 228's object-error branch; it does **not** yet discharge
  the public rejecting contract on an unfinished object such as `{`.
- Validation: `just wnear-audit` passes (2755 build jobs; 421 wNEAR modules,
  58443 declarations and 53322 theorems). Only the three expected open-refinement
  dependencies remain. The strict NearLogic audit has zero violations, and pinned
  statements match. PR-wide Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-positioned-final-audit.log` and `/tmp/pr40-positioned-lean-style.log`.

## Unfinished-object rejection continuation

- `SerdeErrorCode` strengthens syntax-error allocation and reader error contracts
  to retain the exact twelve input error-code bytes, with the existing cost and
  position bounds. `copy_code` proves the two Wasm copies preserve those bytes.
- `SerdeEndMapEOF.f90_eof` proves the closing-object check at EOF returns a
  positioned `EofWhileParsingObject` box with its tag retained.
- `SerdeErrorDrop.f92_syntax` proves drop glue for syntax-error tags above 1:
  there is no owned message to free, and the twenty-byte box is returned to the
  heap. Other live allocations are preserved.
- `SerdeRej.f228_obj_eof` and `rej228_obj_eof` prove the actual unfinished-object
  path. Serde creates the missing-key error, restores the nesting depth, then
  still runs the closing-object check. That check creates a second EOF error;
  228 frees it and returns the first through `fix_position`. The complete
  336-byte stack and empty scratch are restored. The two allocations use the
  existing `roomS` premise; their costs are fixed before the gas ceiling.
- `FromSliceSpec.decode_obj_eof` proves model rejection of the same inputs.
  `f65_obj_eof_reject_uniform` carries the concrete proof through 228 → 78 → 66 → 65,
  without assuming any parser-callee contract. This covers an opening `{`
  preceded and followed by arbitrary JSON whitespace.
- The remaining rejection branches, escaped accepting inputs and deep ignored
  values are still open. This does not complete `RejectContract` or a seventh
  method refinement.
- Validation: `just wnear-audit` passes (2760 build jobs; 426 wNEAR modules,
  59129 declarations and 53999 theorems). Only the three existing open-refinement
  dependencies remain; strict NearLogic has zero violations and statement pins
  match. The public parser theorem and the underlying 228 theorem pass LSP
  axiom verification with the standard three axioms. PR-wide Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-object-final-audit.log` and
  `/tmp/pr40-object-lean-style.log`.

## Accepting escaped-string cost continuation

- The existing all-outcome `costRun` cannot close the accepting linear gas bound.
  `StrCostLower.costRun_newlineEscapes_quadratic` proves a lower bound of
  `(800*n*n + 3400*n)*regularOpCost` for `n` newline escapes, with input length
  `2*n + 1`. `newlineEscapes_model` and `newlineEscapes_utf8` prove this family
  is accepted. The quadratic lower bound concerns the old conservative cost
  expression, not the binary's actual gas. Misstatement log entry 8 records the
  corrected proof plan; the general contracts and model gas bounds are unchanged.
- `SerdeEscSuccess.f655_some` proves `next_or_eof` on a present byte in at most
  100 regular operations, without allocator or stack-memory ownership.
  `f653_some` proves valid four-digit hex decoding in at most 300 regular
  operations, with no error-allocation room premise or error-cost reserve.
- `ParseEscapeSuccess.f649_nu_success` proves all successful simple escapes at
  `400*c + costExt`. `f649_u0_success` proves successful non-surrogate Unicode
  escapes at `900*c + costExt`. Both preserve the general reader/scratch result
  and restore the complete stack; neither reserves whole-input error scans.
- The Unicode success theorem passes LSP axiom verification with the standard
  three axioms; the quadratic lower bound uses only `propext` and `Quot.sound`.
- `ParseEscapeSurrogateSuccess.f649_u1_success` covers successful surrogate pairs at
  `2000*c + costExt`, preserving the same reader/scratch result and complete stack.
  `valid_high_tail` derives the required second escape and low surrogate from
  successful decoding. No error-allocation room premise or error reserve is used.
- `ParseEscapeSuccessCost.f649_success` combines all three successful paths.
  Its instruction allowance is bounded by `200*(m + 1)*regularOpCost` when the
  decoder consumes `m` bytes after the leading backslash; scratch growth/copying
  remains a separate `costExt` charge. This is an escape-level bound, not yet a
  linear bound for the complete string reader.
- LSP verifies the surrogate theorem, combined success contract and consumed-byte
  cost bound with only `propext`, `Classical.choice` and `Quot.sound`.
- The next continuation below supplies the successful 646 loop and a copy
  amortization lemma. The complete accepting gas bound, reader integration and
  full parser rejection remain open.
- Validation: `just wnear-audit` passes (2763 build jobs; 429 wNEAR modules,
  59857 declarations and 54713 theorems), with only the three existing
  open-refinement dependencies. Strict NearLogic has zero violations; statement
  pins, PR-wide Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-escape-success-final-audit.log` and `/tmp/pr40-escape-success-style.log`.

- Surrogate/combined-contract validation: `just wnear-audit` passes (2765 build
  jobs; 431 wNEAR modules, 60291 declarations and 55137 theorems). Only the three
  existing open-refinement dependencies remain. Strict NearLogic has zero
  violations; statement pins, PR-wide Lean style and whitespace checks pass.
  Evidence: `/tmp/pr40-surrogate-final-audit.log` and
  `/tmp/pr40-surrogate-style.log`.

## Successful string loop and amortized-copy continuation

- `StrSuccessCost` defines a success-only run cost. It uses the successful escape
  contracts, reserves no syntax errors, and charges UTF-8 validation only at the
  closing quote. The existing all-outcome contract and cost are unchanged.
- `ParseStrSuccess.f646_success` proves the actual 646 loop on every successful
  UTF-8 run, with arbitrary escapes and the original borrowed/copied `resStr`.
  It restores the complete 192-byte frame and all reader/scratch resources. It
  currently retains the existing conservative `roomRun` premise.
- `ParseStrSuccess.costRun_linear_work` bounds non-append work by
  `(400 + 450*consumed + 100*initialAccLength)*regularOpCost`, plus the separate
  recursive `appendCost`. `ParseStrSuccess.f646_success_linear` exposes the
  corresponding callable contract, including entry/exit work, at
  `(500 + 450*consumed)*regularOpCost + appendCost` from an empty scratch.
- `ScratchAmortized` follows the actual `capAfter` updates along arbitrary append
  lengths. `movedBytes_capacity` telescopes capacity increases; `movedBytes_linear`
  bounds all old-buffer copies by `2*finalUsed + 8` bytes. `copyOps_linear` includes
  memcpy's fixed overhead, bounding that component by `48*finalUsed + 192` regular
  operations. The trace's arithmetic premises are explicit.
- **The general accepting gas allowance is still open.** The 450-ops-per-byte
  component excludes append charges. The fitting case below now meets 470 with
  all append costs included; runs that grow the scratch still need a joint cost
  bound using the append trace and allocator/free-list work. Then integrate
  380/169 and escaped-key readers. No model gas allowance has been increased,
  and this is not a seventh method proof.

- Validation: `just wnear-audit` passes (2770 build jobs; 436 wNEAR modules,
  61095 declarations and 55896 theorems). The only tolerated dependencies on
  `sorryAx` remain the three existing declarations in `Proofs.Refinement`.
  Strict NearLogic has zero violations; statement pins, PR-wide Lean style and
  whitespace checks pass. LSP verifies `f646_success_linear` with the standard
  three axioms and `copyOps_linear` with only `propext` and `Quot.sound`.
  Evidence: `/tmp/pr40-str-success-final-audit.log` and
  `/tmp/pr40-str-success-style.log`.

## Tighter fitting paths and the 470-op accepting string contract

- `ScratchFast` proves fitting 630, 623, 589, 588 and 613. The final slice-append
  chain costs `180*c + MemCpy.cost(k)*c`, compared with `280*c + MemCpy.cost(k)*c`
  in the general contract. Direct 614 (`push`) costs 40 regular operations,
  compared with the general 260. `f613_fast` and `f614_fast` choose these fitting
  bounds and retain the existing growth bounds and exact functional postconditions.
- `ParseEscapeFast.f649_nu_fast` proves all eight successful simple escapes at
  `240*c + pushCost`, replacing `400*c + costExt`. Its generic `f649_fast` keeps
  the existing Unicode/surrogate proofs. Both the simple escape dispatch and
  the fitting push are now charged at their tighter bounds.
- The actual `ParseStrSuccess.f646_success` loop uses these contracts. Its segment
  reserve is reduced from 500 to 300 operations, and its public non-append bound
  is reduced from 550 to 450 operations per consumed byte, as recorded above.
- `costRun_fit` in `StrSuccessFitBound.lean` sums all fitting append charges jointly with
  escape dispatch and the single final UTF-8 validation. `ParseStrSuccess.f646_success_fit` in `ParseStrFit.lean`
  exposes the full callable contract at `(500 + 470*consumed)*c`, with the same
  borrowed/copied `resStr` and full 192-byte stack restoration. The explicit
  capacity premise covers all unread input, so this is the no-growth case. The
  existing conservative `roomRun` premise is retained. LSP verifies the callable
  theorem using only `propext`, `Classical.choice` and `Quot.sound`.
- Next: account for the initial scratch allocation and subsequent growths within
  the same 470-op budget, combining the append trace and allocator/free-list work.
  The argument reader still needs 380/169 integration and general rejection.

- Validation: `just wnear-audit` passes (2774 build jobs; 440 wNEAR modules,
  61364 declarations and 56157 theorems), with only the three existing
  `Proofs.Refinement` dependencies on the open theorem. Strict NearLogic has zero
  violations; statement pins, PR-wide Lean style and whitespace checks pass.
  LSP verifies `ParseStrSuccess.f646_success_fit` with the standard three axioms.
  Evidence: `/tmp/pr40-fast-fit-final-audit.log` and `/tmp/pr40-fast-fit-style.log`.

## Concrete allocation and growth accounting

- `baseAppend` in `StrSuccessCost` now charges a plain-byte append only at an
  escape or at the end of a copied string. The borrowed terminal path does not
  append, so its cost and trace no longer reserve an unused allocation. The
  actual loop proof and both previous cost bounds are repaired and checked.
- `ScratchGrowthTrace` follows `capAfter` and `fAfter` for each append. After `G`
  growths the allocator bound is exactly `F + 2*G`; summed walk bounds satisfy
  `walkBounds + G = F*G + G*G`. `extraCost` includes only growing reserves,
  retaining all allocator walks and memory-growth fees.
- `StrGrowthTrace.appendChunks` follows the actual plain/escape appends; borrowed
  strings have none. `appendChunks_valid` proves the trace arithmetic and final
  capacity/used-length bounds. All requested capacities total at most `4*N + 16`
  bytes; reallocation copies cost at most `48*N + 192` regular operations, with
  `N` the decoded byte length. Page charges are at most
  `(4*N + 16 + 66066*G) / 65536`. The growth-count certificate is
  `G = 0` or `8*2^(G-1) ≤ 2*N + 8`.
- `growthBudget cfg F G N` is zero when `G = 0`. Otherwise it is
  `(1790*G + 320*(F*G + G*G - G) + 36*N + 144)*regularOpCost`, plus
  `G*linearOpBaseCost` and the page-bound times `linearOpUnitCost`.
  `ParseStrSuccess.f646_success_growth` (`ParseStrGrowth.lean`) exposes the full
  successful binary call at `(500 + 470*consumed)*regularOpCost + growthBudget`,
  with the same borrowed/copied result, restored stack, and no capacity premise
  requiring the input to fit. Its existing `roomRun` and binary bounds remain
  explicit. LSP verifies this theorem and the growth-count certificate with the
  standard three axioms.
- **Still required:** absorb this explicit growth budget into the unchanged
  method allowance using the reachable parser heap/scratch invariant, and
  integrate 380/169 and the struct readers. `Hyp646` currently preserves heap
  length/free-list bounds and its borrowed-key instance is not a state-changing
  growth contract. Strengthen `resStr` to expose final capacity/free-list bounds
  from the trace (it currently hides these behind existentials), then carry
  changing scratch/heap state through the 193/228 integration. Also audit the
  borrowed-key consumer's 160-byte callee frame and `d + 16` premise against the
  general proof's 192-byte frame and `d + 30` premise.
  Do not assume a cost uniform in arbitrary initial `F`, or silently frame an
  unchanged heap through growth. Existing escape-free instances remain valid.
  General rejection and deeper ignored values are still open. This does not
  complete a seventh method refinement.

- Validation: `just wnear-audit` passes (2777 build jobs; 443 wNEAR modules,
  61554 declarations and 56309 theorems), with only the three existing
  open-refinement dependencies. Strict NearLogic has zero violations; statement
  pins, PR-wide Lean style and whitespace checks pass. The callable growth
  theorem and power certificate pass LSP axiom verification with the standard
  three axioms. Evidence: `/tmp/pr40-growth-accounting-final-audit.log` and
  `/tmp/pr40-growth-accounting-style.log`.


## Parser result continuation

- `StrTraceResult.resStrTraced` preserves the successful parser's concrete scratch
  trace endpoint. A copied result exposes exact final capacity and allocator
  free-list bound, plus lower/upper memory-length bounds. A borrowed result keeps
  the original scratch resources unchanged.
- `traceInv_escape` composes both appends at an escape; `traceInv_close` extracts
  the endpoint after the final plain append. These pure facts are threaded through
  the actual `f646_success_traced` Wasm loop. `f646_success_growth_traced` exposes
  the same result at the existing closed growth budget. The original two success
  interfaces follow by forgetting the additional information.
- The old key-reader `Hyp646` assumes an unchanged heap, a 160-byte callee frame,
  and a `d + 16` depth premise. The general escaped parser has changing scratch
  state, a 192-byte frame, and a `d + 30` depth premise. Generalize the reader and
  enclosing struct contracts before integrating it; the stronger result is the
  state information needed for that work. No seventh method is complete.
- Validation: `just wnear-audit` passes (2778 build jobs; 444 wNEAR modules,
  61570 declarations and 56321 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f646_success_growth_traced` with only
  the standard three axioms. Changed-source Lean style and whitespace checks pass.
  Evidence: `/tmp/pr40-trace-result-final-audit.log` and
  `/tmp/pr40-trace-result-style.log`.


## Copied value-reader continuation

- `SerdeDeStrEsc.f380_copied` proves the actual successful `deserialize_str` path
  through the general 646 parser and `StringVisitor::visit_str`. Scratch and the
  newly allocated owned `String` remain separate live allocations in one heap.
  The result retains the parser's capacity/free-list endpoint and memory bounds.
- `f380_copied_growth` exposes linear instruction work plus the closed scratch
  growth budget and the owned-string allocation/copy cost. `strRun_size` proves
  decoded bytes and the remaining suffix fit the encoded input, so no extra
  decoded-size premise is required. Allocation room is required at the maximum
  memory length charged by the trace; actual alignment and positivity come from
  the heap invariant, and `roomFor_le` transfers that room to the actual memory.
- `SerdeAccountIdEsc.f379_copied` and `f169_copied` carry this through the String
  wrapper and successful `ValidAccountId::try_from`. They restore complete 240-byte
  and 288-byte frames respectively, with depth premises `d + 32` and `d + 33`.
  `f169_copied_model` starts directly from the JSON model's decoded string and
  `validAccountIdBytes`; it derives the exact parser run and UTF-8 validity.
- These prove successful copied values under explicit reader-room, allocation-room
  and gas premises. The complete escaped accepting argument contract still needs
  changing-state struct-reader hypotheses, escaped keys, and absorption of the
  growth/owned-copy charges into the unchanged method allowance. Rejection and
  deep ignored values remain open; the completed-method count stays six.
- Validation: `just wnear-audit` passes (2780 build jobs; 446 wNEAR modules,
  62022 declarations and 56768 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f169_copied` and `f169_copied_model`
  with only the standard three axioms. Changed-source Lean style and whitespace
  checks pass. Evidence: `/tmp/pr40-copied-values-final-audit.log` and
  `/tmp/pr40-copied-values-style.log`.


## Changing-state struct continuation

- `SerdeValueState` separates scratch/heap ownership from the output descriptor
  and reader cursor. `scratchPre` allows any allocated scratch capacity;
  `valueStorage` retains both scratch and the owned account-id String, with exact
  parser endpoint facts and its memory-growth bound. `spec169_copied` instantiates
  the existing sequence-element callee boundary with this changing state.
- `SerdeSeqElemEsc.f214_copied` proves the first array element using that concrete
  account-id reader. `SerdeMapValueEsc.f205_copied` consumes the map colon and
  reads the copied account id. Both retain the returned scratch/heap state.
- `SerdeColonSuccess.f89_colon` and `f91_close` prove the actual successful
  punctuation paths with only reader/global resources. Heap, scratch and stack
  ownership are framed through; these paths neither allocate nor access their
  reserved stack memory. They retain the existing 200/400-operation allowances
  plus whitespace costs and require only `d + 2` call-depth room.
- `SerdeStructArrState.f228_arr_state` generalizes the array struct proof to an
  arbitrary changing-state element-reader pre/postcondition. The actual closing
  bracket check preserves the returned state and advances the reader. The full
  368-byte frame and nesting-depth byte are restored.
- `SerdeStructArrEsc.f228_arr_copied` instantiates that contract with the concrete
  JSON-model-facing escaped account-id reader, at `d + 35`. It accepts the array
  form with a copied valid account id under explicit parser/allocation room and
  growth/owned-copy gas charges. It does not assume the zero-capacity `tbl` or an
  unchanged heap after 169.
- Remaining integration: generalize the object's loop/key state, then carry the
  array/object results through scratch cleanup and the 78/66/65 wrappers. The
  scratch-drop contract uses membership and a remaining-live-list sublist premise,
  so retain the owned String through that interface rather than assuming scratch
  is the first live allocation. Absorb the explicit gas charges under reachable
  heap bounds. Full rejection and deep ignored values remain open; still six
  completed exported methods.
- Validation: `just wnear-audit` passes (2786 build jobs; 452 wNEAR modules,
  62545 declarations and 57287 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f228_arr_copied` with only the standard
  three axioms. Changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-struct-values-final-audit.log` and `/tmp/pr40-struct-values-style.log`.


## Copied-array entry and scratch cleanup continuation

- `SerdeScratchValueDrop.f68_value` proves the actual grown-scratch drop while
  retaining the owned String and every earlier live allocation. The live-list
  uniqueness invariant proves the two pointers differ, so erasing scratch removes
  its second entry rather than the String. The final free-list bound is exactly
  `max (endFreeBound F capS 0 chunks) 1 + 1`; memory growth includes the parser trace
  and the owned-string allocation. `cleanValue` retains these bounds.
- `SerdeEndSuccess.f320_eof` checks the final whitespace/end-of-input using only
  reader and global resources. The changed heap, scratch and stack are framed
  through, without requiring extra error-allocation room on this accepting path.
- `SerdeStruct78Esc.f78_arr_copied`, `SerdeFromTraitEsc.f66_arr_copied` and
  `FromSliceEsc.f65_arr_copied` carry the concrete array path through the actual
  78/66/65 calls. 66 constructs its own empty scratch, runs the array reader,
  checks the remaining whitespace, copies the result, frees grown scratch and
  restores its frame. The complete entry restores 448 bytes, preserves input and
  all three string tables, and returns only the owned String; its depth premise
  is `d + 38`.
- `FromSliceEsc.f65_arr_okAt` gives the existing public parser result shape for a
  model account id. This is a proved copied-array family under explicit shape,
  parser/allocation-room and growth/copy gas premises. It is not yet the uniform
  `AcceptContract` on every accepted input. The old contract's `roData` does not
  include the hex table; the general escaped path must carry that ownership.
- The 66 proof simplifies credits after each large call; leaving all nested
  subtraction expressions unnormalized caused a kernel recursion limit. The
  checked proof uses the same 700-operation local/end/drop allowance, plus final
  whitespace and `costArray`; 65 adds 45 operations. The uniform method allowance
  is unchanged and still needs the growth/copy charges absorbed.
- Remaining: object-loop/escaped-key state, deep ignored values, general parser
  rejection, and the reachable heap/room/gas bounds for the complete accepting
  contract. The copied-array cleanup and outer-wrapper integration are now done;
  no seventh exported-method refinement is claimed.
- Validation: `just wnear-audit` passes (2791 build jobs; 457 wNEAR modules,
  62822 declarations and 57562 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f65_arr_okAt` with only the standard
  three axioms. Changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-copied-array-entry-final-audit.log` and
  `/tmp/pr40-copied-array-entry-style.log`.

## General object-key and reusable-state continuation

- `SerdeKeyEsc.f646_key` adapts the general successful string reader to the existing
  `SerdeNextKey.Spec646` boundary. The extra 32 bytes required by the 192-byte parser
  frame travel through its abstract pre/post resources; `Spec646` and the original
  193 body proof remain reusable. The key's decoded bytes are lent to the field
  matcher, whether borrowed from input or copied into scratch.
- `SerdeKeyEsc.f193_key_model` proves the actual next-key call for any key decoded
  by `Json.stringBody`, on the first or subsequent member. It clears the physical
  scratch length, preserves input and all three string tables, restores the complete
  208-byte frame, and retains the concrete growth budget and returned scratch state.
  Both borrowed and copied paths accept arbitrary initial allocated scratch capacity.
- `sbuf_clear` forgets logical contents while retaining every byte as spare capacity;
  the next Wasm clear updates the descriptor length. `SerdeObjectState.keyState_reuse`
  exposes common existential scratch coordinates, memory-growth and free-list bounds.
  `parsed_capacity` proves the next reader's `cap < 2^25` premise. Its sharper trace
  bound is `max oldCapacity (max 8 (2 * finalUsed))`, avoiding the old additive-eight
  estimate at the input-size boundary.
- `AllocLivePerm.heapInv_perm` proves enumeration order is immaterial to the allocator's
  logical live list; it changes no physical cell. `SerdeObjectState.valueStorage_reuse`
  reorders scratch before the owned String and keeps the String's bytes, final allocator
  bound and parser-plus-owned-copy memory bound. This supplies reusable scratch after
  the account field has been read, while keeping every earlier live allocation.
- These close the concrete escaped-key reader and two resource transitions needed by
  the changing-state object invariant. The actual object loop is not yet generalized.
  A plain account-id value after an escaped key must also accept already-grown scratch;
  the existing copied-value theorem alone does not cover that borrowed path. Deep
  ignored values/ignored escapes, full rejection, reachable room and uniform gas bounds
  remain open. Six exported methods are complete under protocol premises.
- Next implementation route: instantiate `SerdeDeStr.f380_s` for a plain value with
  scratch already present in `live`, framing the scratch pointer/capacity and its
  spare bytes. Its existing no-escape parser does not touch those framed bytes.
  Normalize that borrowed result and the copied result to one owned-value/scratch
  boundary. The object loop then needs at least the larger value-reader stack
  footprint and costs indexed by the evolving scratch/allocator state; do not
  reset capacity between keys or sum growth charges as if each key started empty.
- Validation: `just wnear-audit` passes (2794 build jobs; 460 wNEAR modules,
  62879 declarations and 57616 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f193_key_model`, `parsed_capacity` and
  `valueStorage_reuse` with only the standard three axioms. Changed-source Lean
  style and whitespace checks pass. Evidence: `/tmp/pr40-key-state-final-audit.log`
  and `/tmp/pr40-key-state-style.log`.

## Unified value-reader continuation

- `SerdeValueReuse.f169_borrowed_model` proves a plain account-id value with scratch
  already allocated by an earlier escaped key. It instantiates the existing 169
  proof with scratch in the live list, frames its pointer/capacity/spare bytes and
  the hex table, and restores the same 288-byte frame as the copied path. The owned
  String remains distinct from scratch. No Wasm body is duplicated for that reader.
- `ownedValue` is the common returned resource: the String's bytes, descriptor facts,
  reusable scratch, exact parser endpoint capacity/free-list bound, and total memory
  growth including the owned copy. `heapS_reuse` and `valueStorage_owned` normalize
  the borrowed and copied allocation orders. The physical scratch length may remain
  existential; the next key or value reader clears it before reuse.
- `SerdeValueReuse.f169_model` now handles every valid model-decoded account-id string,
  whether borrowed/plain or copied/escaped, with arbitrary initial scratch capacity.
  It retains explicit reader-room and allocation-room premises. `spec169_model` adapts
  it to the existing sequence-element reader boundary.
- `SerdeMapValueReuse.f205_model` proves the actual colon-plus-value map call, while
  `SerdeSeqElemReuse.f214_model` proves the actual first array-element call. Both use
  the unified reader and return `ownedValue`, the reader cursor and all three string
  tables. The former requires a 288-byte frame; the latter restores all 304 bytes.
- `valueCost_le` proves both branches fit the existing growth-aware copied-reader
  charge. Borrowed strings have an empty append trace and zero scratch-growth charge;
  their String allocation/copy is still charged. The uniform method allowance remains
  unchanged, and its reachable heap/room/growth bounds are not yet discharged.
- Remaining: generalize the actual object loop around the key and unified value
  contracts, including ignored readers and the successful closing-object delimiter.
  After each member, unpack the returned scratch/heap coordinates into the evolving
  loop state. Do not retain `ownedValue` unchanged across later keys: its exact scratch
  endpoint describes the value read, and a later key can grow scratch again while the
  String remains live. Deep ignored values/ignored escapes and general rejection are
  still open. Six exported methods are complete under protocol premises.
- A possible control-proof interface is a member state `J i seen p cap`: keep heap,
  scratch and owned String bytes in `J`, with the loop's descriptor words separate.
  Abstract full 193/205/201 calls can move `J` from the entry cursor to the returned
  cursor while preserving or setting `seen`. This avoids assuming exact scratch
  endpoints remain fixed, and leaves uniform reachable-state cost bounds to the
  concrete reader instantiations. The existing object control proof and pure
  `loopRes`/`objCost` decomposition remain reusable.
- Validation: `just wnear-audit` passes (2797 build jobs; 463 wNEAR modules,
  62947 declarations and 57680 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f169_model`, `f205_model`, `f214_model`
  and `valueCost_le` with only standard axioms. Changed-source Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-value-reuse-final-audit.log`
  and `/tmp/pr40-value-reuse-style.log`.

## Changing-state object-loop continuation (2026-10-30)

- `SerdeStructObjState.f228_obj_state` proves the actual object path of 228 with
  cursor-indexed member state `J`. Keys and ignored values may change heap/scratch
  resources, and the account-id reader installs a saved String. The loop preserves
  that String through later members, checks the closing `}`, restores depth 128 and
  returns the complete 368-byte frame. It uses the existing `loopRes`/`objCost`
  decomposition and the existing charge; its explicit depth premise is `d + 42`.
- `SerdeEndMapSuccess.f90_close` proves the successful closing-object check with
  only reader/global resources, at `(200 + 96 * whitespace) * regularOpCost` and
  `d + 2`. The changed heap, scratch and stack remain framed through that call.
- `SerdeStructObjKeyState.core` exposes reachable heap/scratch coordinates and
  owns the vtable, all three string tables, static field name and literal table
  needed by ignored values. `member` adds the
  saved String's bytes and live allocation. It uses separate bounds before and after
  the one account-id allocation; a single bound predicate would make the pure value
  closure demand hypothetical repeated String allocations. `seen_core` lends that state while
  retaining the loop's descriptor; `key_exact` preserves the exact endpoint on
  borrowed and copied paths; `member_mono` transports pure cursor bounds.
- `SerdeStructObjKeyState.keyHyp` discharges the loop's actual key-call hypothesis
  with `SerdeKeyEsc.f193_key_model`. `KeyConditions` asks only for room, the fixed
  charge bound and preservation of pure reachable-state bounds. The saved String
  and its descriptor remain live while the scratch allocation can change.
- `SerdeStructObjValueState.account_model` derives the quoted decoded string from
  the model's account reader, including escaped inputs. `valueHyp` discharges the
  loop's actual colon/value hypothesis using `SerdeMapValueReuse.f205_model`.
  `ValueConditions` asks only for room, charge and endpoint bounds, including the
  owned String's allocation. Both borrowed and copied values use this interface.
- `SerdeStructObjModelState.f228_obj_model` assembles the concrete key/value
  contracts with the actual loop and the model account reader. The remaining Wasm
  reader hypothesis is `IgnoreHyp`. Its ignored decoder is parameterized with
  `Agrees ign valueSkip`, rather than requiring literal model skipping on malformed
  numeric prefixes that serde can reject. This retains the existing usable model
  correspondence instead of assuming an unprovable ignored-reader contract.
  An additional persistent code context supplies the ignored reader's transitive
  callees; the successful key/value code bundle alone does not contain them.
- The general object-control integration is now proved. The public result is still
  conditional on `KeyConditions`, `ValueConditions`, monotone reachable bounds, an
  initial `member` state and the ignored-reader contract. Those obligations, deeply
  nested/escaped ignored values, object-state cleanup through 78/66/65 and general
  rejection remain open. This does not establish full `AcceptContract` or a seventh
  exported method refinement.
- Room predicates receive alignment and positivity from the actual allocator,
  via `scratch_alignment`, rather than requiring the pure interval-closed bounds
  to imply them. `alignment_not_interval` records the counterexample; misstatement
  entries 9–11 explain the interface corrections made before publication.
- Quantitative follow-up at this checkpoint (borrowed-key part closed below):
  `keyHyp` paid the general string allowance
  `500 + 470 * consumed` even for borrowed keys. The existing dense-member bound
  used `300 + 130 * consumed`: for an empty key the new conservative allowance is
  540 operations higher, so it does not fit the old 470-per-input-byte member
  arithmetic unchanged. Reuse the old no-escape key reader with allocated scratch
  framed through (as for the plain value), and choose that tighter charge on
  borrowed keys. Escaped strings also retain separate growth charges; their
  accepting instruction estimate may need tightening before the uniform method
  allowance can absorb them. No complete uniform gas bound is claimed here.
- Validation: `just wnear-audit` passes (2802 build jobs; 468 wNEAR modules,
  63521 declarations and 58237 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies the public object theorem, concrete
  key/value adapters and closing check with only standard axioms. Changed-source
  Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-object-loop-final-audit.log` and `/tmp/pr40-object-loop-style.log`.

## Borrowed-key charge continuation (2026-10-30)

- `SerdeKeyReuse.f646_key_borrowed` reuses `SerdeNextKey.f646_key_noesc`
  with any existing scratch allocation in the allocator's live list. It frames
  scratch's pointer/capacity/spare bytes, the hex table and the extra 32 stack
  bytes through the old reader, then rejoins the unchanged scratch. The key's
  input-backed bytes are lent only until the field matcher returns them.
- `f646_key` selects that borrowed proof or the existing general copied-key
  proof. `f193_key_model` carries the selected charge through the actual next-key
  call with the complete 208-byte frame and the existing reusable `keyState`.
  No Wasm body proof is duplicated and no scratch capacity is reset.
- `keyCost_borrowed` proves the borrowed charge is exactly
  `(300 + 130 * consumedBytes) * regularOpCost`. Thus an empty key has a
  430-operation allowance at this reader boundary, rather than the general 970.
  This restores the old borrowed-key contribution to dense-member arithmetic
  even when an earlier key or value allocated scratch. `keyCost_le` proves the
  selected charge never exceeds the previous growth-aware allowance.
- `keyRoom` asks only for the old reader's error-box room on a borrowed key;
  copied keys retain the general `roomRun` premise. `keyRoom_of_roomRun` proves
  the old general premise still suffices. Borrowed keys no longer need room for
  a hypothetical scratch append. The changing-state `KeyConditions` and
  `keyHyp` now use this room predicate and selected charge, so the assembled
  object theorem inherits them.
- Remaining: absorb copied-key growth/instruction charges, prove reachable
  heap/scratch bounds and the ignored-reader transition, carry object results
  through 78/66/65 cleanup, and complete general rejection. The unchanged
  uniform accepting contract and seventh method are still open.
- Validation: `just wnear-audit` passes (2803 build jobs; 469 wNEAR modules,
  63551 declarations and 58265 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `SerdeKeyReuse.f193_key_model` and
  the assembled object theorem with only standard axioms. Changed-source Lean
  style and whitespace checks pass. Evidence: `/tmp/pr40-key-reuse-final-audit.log`
  and `/tmp/pr40-key-reuse-style.log`.

## Reusable scratch in shallow ignored values (2026-10-30)

- `SerdeIgnValue.scratchTables` parameterizes the scratch descriptor's pointer and
  capacity. `P81`, `inv4`, `contSt` and `brkSt` carry those coordinates through the
  existing shallow body proof. `f81_shallow_reuse` clears only the length, keeps
  pointer/capacity unchanged, and returns the complete 96-byte frame at the
  original `(166 + 470 * consumedBytes) * regularOpCost` allowance. The old
  `f81_shallow` follows as the `(1, 0)` specialization, preserving its callers.
- `SerdeIgnReuse.f201_shallow` proves the actual colon-plus-ignore call using the
  successful colon contract and generalized 81. It needs no allocator ownership
  or error allocation room on this accepted path. Scratch bytes, allocator cells,
  the hex table and a saved account-id String can remain framed through.
- `SerdeIgnReuse.ignoreHyp` supplies the changing-state loop's full ignored-call
  interface for `IgnoreShallow.ign1R`, with `cost81` fixed independently of the
  gas ceiling. It lends the descriptor and read-only tables from `core`, frames
  its allocator/buffer and the saved String, and reconstructs the same allocation
  state under the cursor-monotone `B` or `Bsaved` bound. All 304 caller stack
  bytes are returned. The shared literal table and additional persistent code
  context introduced with the object loop supply the reader's actual resources.
- Coverage remains shallow ignored values on inputs without escapes. This
  generalizes scratch ownership and discharges that family's state transition;
  it does not prove the full model-agreeing ignored reader, escaped/deep ignored
  values, the uniform accepting contract, general rejection or a seventh method.
  Next: prove successful 652/650 on escaped ignored strings, replace the global
  no-escape requirement at the two string branches, and generalize frame pushes
  for deeper nesting while retaining the changing allocator state. The escaped
  string reader must receive the hex table currently framed by `ignoreHyp`;
  carry it through 81’s invariant or a parameterized string-reader frame.
- Validation: `just wnear-audit` passes (2804 build jobs; 470 wNEAR modules,
  63588 declarations and 58299 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP's compiled-module axiom query verifies the
  generalized 81 theorem and retained specialization with only standard axioms;
  `ignoreHyp` also passes its individual axiom check. Changed-source Lean style
  and whitespace checks pass. Evidence: `/tmp/pr40-ignored-reuse-final-audit.log`
  and `/tmp/pr40-ignored-reuse-style.log`.

## Successful ignored escapes (2026-10-30)

- `SerdeHexSuccess.f653_some` proves successful four-digit hex decoding without
  owning a heap or allocator vtable. The actual 653 fast path needs only the
  instance, reader, global, 96-byte frame and hex table. It keeps the existing
  300-operation allowance and returns the packed value with the cursor advanced
  exactly four bytes. Error construction and allocation room are absent.
- `SerdeIgnoreEscape.f652_nu_success`, `f652_u0_success` and `f652_u1_success`
  prove the actual ignored-escape function for simple escapes, BMP Unicode and
  surrogate pairs. They preserve all 112 stack bytes and the hex table, need no
  allocator ownership, and return zero at cursor offsets 1, 5 and 11 after the
  leading backslash. Their instruction allowances are 400, 900 and 2000.
- `consumed_eq` proves those branch lengths equal the model's `escDecode`
  consumption. `f652_success` covers every model-accepted escape with that exact
  endpoint. `f652_success_linear` places its charge under
  `200 * (consumedBytes + 1) * regularOpCost`, including the leading backslash.
  The code predicate contains only the instance and successful callees 637/655/653.
- The pair proof establishes scalar range and surrogate-mask tests before the
  corresponding branches. Its large-mask step uses the explicit numeric rule
  with an abstract result, avoiding expensive generic simplification. No native
  decision procedure or additional axiom is used.
- Next is the full successful `ignore_str` loop (650), then removal of 81's
  no-escape premise. Preserve the model's `Option String`: ignored strings may
  have valid syntax but invalid raw UTF-8, and must not be restricted to `some s`.
  `strRun_model` can supply existential decoded bytes without a UTF-8 premise.
  The planned outer invariant tracks `strRun (bs.drop j) acc = .ok bytes rest`;
  the inner scan can reuse `SerdeIgnStr.inv650`. The complete stack includes
  650's 16 bytes plus 652's 112. Carry the hex table through the 81 invariant or
  an abstract successful string-reader frame. Deep frame pushes and their changing
  allocator state, uniform room/gas bounds, object wrappers and general rejection
  remain open. This does not complete `AcceptContract` or a seventh method.
- Validation: `just wnear-audit` passes (2806 build jobs; 472 wNEAR modules,
  64455 declarations and 59153 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP's compiled-module axiom queries verify the hex
  theorem and both combined escape theorems with only standard axioms.
  Changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-ignored-escapes-final-audit.log` and
  `/tmp/pr40-ignored-escapes-style.log`.

## Successful ignored strings (2026-10-30)

- `SerdeIgnoreString.f650_success` proves the actual 650 loop for every successful
  `strRun`, including arbitrary simple/Unicode escapes. The outer invariant tracks
  the remaining modeled run and accumulated decoded bytes; the inner loop reuses
  the existing plain-byte scan. The call returns zero at the exact model endpoint,
  preserves the ESCAPE/hex tables and reader input, and restores all 128 stack bytes.
- Its fixed charge is `(120 + 300 * consumedBytes) * regularOpCost`, independent
  of the gas ceiling. The escape branch pays for 652's successful linear contract,
  call activation and the next loop iteration. No allocator ownership, allocation
  room, error reserve or UTF-8 validation is required. The depth premise is `d + 14`.
- `strRun_of_stringBody` derives existential decoded bytes when the model returns
  `some (s, rest)` for any `s : Option String`. `f650_model` exposes the same
  contract directly at that model boundary. Thus skipped strings with invalid raw
  UTF-8 remain covered; the kernel also checks the witness `[255, 34]`, whose
  string body succeeds with `s = none` and an empty remainder.
- Next: integrate this boundary at 81's string-value and object-key branches,
  carry hex-table ownership through its invariant, and remove its global no-escape
  premise. 650 needs 128 bytes below 81's own 32-byte frame, so that integration
  must provide 160 bytes rather than the old 96-byte shallow footprint. The object
  adapter currently lends 304 bytes, but the complete frame must still be returned.
  Deep frame pushes, uniform heap/room/gas bounds, object wrappers and general
  rejection remain open. This does not complete `AcceptContract` or a seventh method.
- Validation: `just wnear-audit` passes (2807 build jobs; 473 wNEAR modules,
  64671 declarations and 59360 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies both public contracts and the model
  helper with only the three standard axioms. Changed-source Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-ignore-string-final-audit.log`
  and `/tmp/pr40-ignore-string-style.log`.

## Escaped shallow ignored values (2026-10-30)

- `SerdeIgnValue.f81_shallow_core` refactors the existing body proof around a
  successful `StringHyp` and an explicit preserved resource frame. Both the
  scalar-string branch and ignored-object-key branch now use the model's
  `stringBody` endpoint rather than a no-escape split. The existing
  `f81_shallow_reuse` is recovered with the plain reader and an empty extra
  frame; its public 96-byte footprint, depth premise and charge are unchanged.
- `SerdeIgnValueEsc.stringHyp` discharges that boundary with the proved full
  successful 650. Its extra frame owns the hex table, successful callee code and
  64 additional stack bytes. `f81_shallow_escaped` therefore covers every
  successful `ign1` skip with arbitrary string escapes, including strings whose
  raw UTF-8 is invalid, without a global no-backslash premise. It preserves
  reusable scratch pointer/capacity and all three string tables, returns the exact
  reader endpoint and restores all 160 bytes. The depth premise is `d + 15`;
  the charge remains `(166 + 470 * consumedBytes) * regularOpCost`.
- `SerdeIgnReuseEsc.f201_shallow` carries the result through the actual colon
  and ignored-value call with a 160-byte frame and `d + 16`. `ignoreHyp` supplies
  the changing-state object loop's ignored-call interface for `ign1R`, now with
  arbitrary escaped strings. It lends the hex table, frames the scratch buffer,
  allocator and saved account-id String, and rejoins all 304 caller stack bytes.
  The existing `cost81` and cursor-monotone bound predicates are reused. There
  is no allocator-room or ignored-reader behavioral hypothesis in these two
  concrete adapter results.
- Lean MCP checks the public contracts, generic core and retained specialization
  with only the three standard axioms. The kernel also checks `ign1` witnesses
  for a newline escape, invalid raw UTF-8, and an object with a Unicode-escaped
  key and escaped string value. `just wnear-audit` passes (2809 build jobs;
  475 wNEAR modules, 64712 declarations and 59399 theorems), with only the three
  existing `Proofs.Refinement` dependencies on `sorryAx`. The strict NearLogic
  audit has zero violations; pinned statements, changed-source Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-escaped-ignore-final-audit.log`
  and `/tmp/pr40-escaped-ignore-style.log`.
- Remaining: scratch frame pushes/pops for deep ignored containers, the full
  model-agreeing ignored reader, reachable heap/room and uniform gas bounds,
  object wrappers through 78/66/65 and general rejection. `ign1R` is still the
  shallow decoder; it must not be treated as globally agreeing with `valueSkip`.
  This does not establish the full `AcceptContract` or a seventh method.

## First nested frame allocation and nonempty pop (2026-10-30)

- The frame push (84) reserves through 698/712/715/716/714/713, rather than the
  string reader's 589/623/630/631/627/624 chain. The existing `VecGrow` proofs
  covered nonempty buffers; `VecGrowZero` closes this chain's capacity-zero case.
  `f713_alloc` allocates positive byte capacity, `f714_alloc` proves the
  `None` current-memory path, and `f716_alloc` installs `growCap 0 k = max(8,k)`
  from zero capacity and length. Their stack footprints are 16, 32 and 64 bytes.
- `f715_alloc`, `f712_alloc` and `f698_alloc` carry that first allocation through
  the actual reserve wrappers for a positive request. 698 restores all 80 bytes,
  preserves the length at zero, installs the fresh pointer/capacity, and keeps
  every earlier live block. Its fixed charge is
  `480 * regularOpCost + SerdeString.costA cfg F (growCap 0 k)`, with `d + 12`.
  `costA` retains the allocator walk and page fees; no charge is selected from
  the gas ceiling. The explicit room premise is `roomFor` for the new capacity.
- `SerdeIgnFrameStack.f84_initial` proves the actual first frame push, with the
  flag 1 on `(ptr, cap, len) = (1,0,0)`. It allocates capacity 8, stores the frame
  byte, sets length to 1 and restores all 80 bytes. Its two-phase loop invariant
  proves that the byte is written once before the iterator exits. The result is
  `sbuf ... (max F 1) p 8 [byteOf b]`, with the exact allocator memory-growth
  alternative and all earlier live allocations retained. The charge is
  `600 * regularOpCost + costA cfg F 8`, and the depth premise is `d + 13`.
- `f85_nonempty` proves the actual nonempty pop: a buffer holding `bs ++ [b]`
  returns `Some b`, updates the length to `bs.length`, and retains the same
  capacity, memory length, free-list bound and live blocks in `sbuf ... bs`.
  The removed byte becomes the first spare byte. The leaf needs no stack/global
  ownership or allocation room and uses at most 50 regular operations.
- Lean MCP verifies all eight public contracts with only the three standard
  axioms. `just wnear-audit` passes (2811 build jobs; 477 wNEAR modules,
  65208 declarations and 59890 theorems), with only the three existing
  `Proofs.Refinement` dependencies on `sorryAx`. Strict NearLogic has zero
  violations; statement pins, changed-source Lean style and whitespace checks
  pass. Evidence: `/tmp/pr40-frame-stack-final-audit.log`,
  `/tmp/pr40-frame-stack-style.log` and `/tmp/pr40-frame-stack-final-style.log`.
- Next: combine fitting, capacity-zero and nonempty-growing reserves under a
  common `sbuf` contract, prove the general frame push, then extend 81's invariant
  to the complete `IgnoreModel.ignM` machine with a changing heap/frame stack.
  Its existing 160-byte footprint can cover the 80-byte reserve beneath its
  32-byte frame, as well as the larger 650 path. Bound actual frame growth/copies,
  retaining the saved account-id String. Full ignored-reader integration,
  uniform bounds, object wrappers, rejection and the seventh method remain open.

## General frame reserves, stack operations and pop-aware growth (2026-10-30)

- `SerdeIgnReserve.f698_sbuf` unifies the actual fitting, capacity-zero and
  nonempty-reallocation paths of 698. It preserves the used prefix and earlier
  live allocations, restores all 80 stack bytes, and exposes the returned
  pointer, `capAfter`, `fAfter` and exact `hlAfter` alternative. Its cost is
  `59*c + growthCost`: fitting requests pay 59 regular operations, while growth
  retains the allocator walk, copying and requested-page fees. Its arithmetic
  and allocation-room premises remain explicit.
- `SerdeIgnPush.f84_some` proves the actual present-byte push for any represented
  scratch buffer, including fitting, first-allocation and reallocating cases.
  It appends exactly `byteOf b`, increments length once, and restores all 80
  bytes, at `140*c + growthCost` and call-depth premise `d + 13`.
- `SerdeIgnStack.state` stores `frames.reverse`, connecting the vector's
  append/pop-at-end representation to `IgnoreModel`'s innermost-first saved
  frames. `f84_cons` pushes a pure head; `f84_none` preserves the complete state
  at 120 regular operations; `f85_pop` implements the head/tail split, including
  the empty case, at a common 50-operation upper bound. `sbuf_clear` returns
  all formerly used bytes to the spare region without freeing the allocation;
  `f343_clear` carries that through the real clear call at 30 operations.
  The state retains the scratch pointer/capacity and all earlier live blocks.
- `SerdeIgnTrace` accounts for arbitrary interleaved pushes and nonempty pops.
  `Valid` requires the actual reserve arithmetic bounds at every state. Its
  transitions use the concrete `capAfter`/`fits` definitions, retain capacity
  on pops and evolve the free-list bound only on growth. The high-water used
  length `N = peak len ops` replaces the append-only trace's final used length:
  `movedBytes_peak` bounds total old bytes copied by `2*N + 8`, and
  `allocatedBytes_peak` bounds requested capacity by `4*N + 16`.
- `growthCount_power` proves `8 * 2^(G-1) <= finalCapacity` for a positive
  actual growth count `G`, even across pops. `endFreeBound_eq` gives `F + 2*G`,
  and `walks_eq` retains the summed allocator walks via
  `walks + G = F*G + G*G`. `pages_scaled` includes allocator headers and page
  rounding. `extraCost_budget` bounds all remaining real reserve charges by
  the closed `budget cfg F G N`, retaining regular-operation, allocator-walk,
  old-copy and requested-page contributions. The budget is independent of the
  gas ceiling; it is not yet absorbed into the parser's model gas allowance.
- Lean MCP diagnostics and standard-axiom checks pass for the public stack
  contracts and quantitative bounds. The targeted stack/trace build passes.
  `just wnear-audit` passes (2815 build jobs; 481 wNEAR modules, 65476
  declarations and 60097 theorems), with only the three existing open-refinement
  dependencies on `sorryAx`. Strict NearLogic has zero violations and all
  statement pins match. PR-wide changed-source Lean style and whitespace
  checks pass. Evidence: `/tmp/pr40-general-stack-final-audit.log` and
  `/tmp/pr40-general-stack-final-style.log`.
- Next: extract such a trace while extending 81's invariant to the complete
  `IgnoreModel.ignM` machine with a changing heap/frame stack. Preserve the
  saved account-id allocation in `live`, couple peak length to consumed input,
  and discharge reachable room/capacity bounds. Then integrate that reader
  into the changing-state object loop and its 78/66/65 cleanup wrappers.
  Full ignored-reader integration, uniform accepting bounds, general rejection,
  the seventh method and M9 remain open. No additional `sorry` is introduced.

## Full ignored-machine trace and local-frame save boundary (2026-10-30)

- `SerdeIgnMachineTrace.run` instruments the complete `IgnoreModel.ignM`,
  rather than the shallow decoder. `erase_run` proves that forgetting its
  trace gives exactly `ignM` for every mode, input and fuel. `erase_trace`
  specializes the already sufficient fuel to `vSkip`, and `trace_agrees`
  retains its complete `valueSkip` agreement, including serde's documented
  early-number exception. Ignored key strings retain their syntactic endpoint
  without requiring valid raw UTF-8.
- The trace accounts for 81's local-frame optimization. In value mode the pure
  stack's head is the pending local frame, so the physical height is one less
  than its logical length. Opening another container records a vector push
  only when that pending frame exists. Scalar completion uses the local head
  without a vector operation; closing a container records only a nonempty
  saved-frame pop. Entering an element or member records no vector push.
- `run_good` proves successful traces legal in every mode: no empty vector
  pop, final saved height zero, a nonincreasing reader endpoint, and push count
  at most consumed bytes. `trace_some` yields an actual trace for every
  successful complete `vSkip`, with peak height also at most consumed bytes.
- `valid_of_legal` turns legality and a peak bound into every per-state reserve
  arithmetic premise. `trace_valid` discharges those premises on the existing
  `bs.length < 2^24` parser domain, with any initial scratch capacity below
  `2^27`. `trace_budget` consequently bounds the produced complete-machine
  trace by `SerdeIgnTrace.budget` at consumed length and its actual growth
  count, retaining allocator-walk and page fees. Its final used length is zero;
  no append-only final-length assumption is used.
- `SerdeIgnMachineStack.physical` relates each pure mode to the represented
  vector. `f84_save` proves the actual optional 84 call from value mode to an
  opened container: it saves the pending local head, or preserves the complete
  state at the top level, retaining all earlier live allocations. `saveF_trace`
  matches the returned allocator bound to the trace, and `save_extraCost`
  splits the growth credits using exactly the returned capacity/free-list
  coordinates. `pop_extraCost` preserves those coordinates when a saved frame
  is restored. The fixed save allowance is at most 140 regular operations.
- Both modules pass Lean MCP diagnostics and standard-axiom checks; the
  targeted build passes. `just wnear-audit` passes (2817 build jobs; 483
  wNEAR modules, 65689 declarations and 60249 theorems), with only
  the three existing open-refinement dependencies. Strict NearLogic has zero
  violations, pinned statements match, and PR-wide changed-source Lean style
  and whitespace checks pass. Evidence: `/tmp/pr40-machine-trace-final-audit.log`
  and `/tmp/pr40-machine-trace-final-style.log`.
- Next: extend the actual 81 value/container-loop invariant with these mode
  views, the complete successful traced continuation, changing scratch/heap
  coordinates, and preserved saved-String ownership. The trace is now derived
  from the full pure machine; matching the whole Wasm 81 body to it is still
  open. Reachable allocation room and absorption of the complete parser charge
  remain open, as do object cleanup wrappers, full rejection, the seventh
  method and M9. No additional `sorry` is introduced.

## Concrete changing-state segments of Wasm 81 (2026-10-30)

- `SerdeIgnSegments.startCode_eq`, `openingBlock_tail` and `closingBlock_tail`
  pin the new segments to the actual decoded 81 body. The structured-control
  paths include the following real branches: opening goes out through `br 2`,
  and a restored close returns to the container loop through `br 1`.
- `start_prefix` proves the actual prologue, including global stack adjustment,
  clear through 82 and initialization of the value-loop flags. It starts with
  arbitrary represented reusable scratch contents, preserves its allocation
  and all earlier live blocks, and exposes the 160-byte frame as a 128-byte
  callee region plus 32 owned bytes. Its body-prefix allowance is 60 regular
  operations, with all remaining credits preserved.
- `open_prefix` proves the actual nested-opening tail: pass the optional
  pending local frame to 84, consume the opening byte through 333, clear the
  comma flag, and install the new current bracket. Its returned pointer,
  capacity, heap-length alternative and free-list bound are exactly the
  `SerdeIgnMachineStack.f84_save` coordinates. The allowance is 60 regular
  operations plus `saveCost`, and all 80 borrowed callee-stack bytes return.
- `close_nonempty` proves the real delimiter-consume/pop/flag-test/restore
  sequence for any nonempty saved stack. It installs the saved head in local 8,
  sets the comma flag, retains scratch capacity/heap/free-list bounds, advances
  the reader once and restores all 32 owned frame bytes. `close_empty` proves
  that the same code on an empty stack takes the actual `br_if 5` success
  branch, with the empty scratch allocation retained. Each fits 110 regular
  operations; the full function's success epilogue is still outside this segment.
- `open_traced` carries the complete successful pure continuation through the
  actual opening segment. It consumes only the recorded save growth charge
  from `extraCost`, returns the successful opened-mode trace, and leaves its
  remaining growth credits at the returned capacity/free-list coordinates.
  Its fixed allowance is 200 regular operations. `close_traced` restores the
  complete continuation through a real nonempty close, removing exactly the
  recorded pop and preserving the remaining growth budget and heap state.
- Lean MCP checks all six contracts and all three code-location equations;
  only standard axioms are used. The targeted build passes. `just wnear-audit`
  passes (2818 build jobs; 484 wNEAR modules, 65834 declarations and
  60380 theorems), with only the three existing open-refinement dependencies.
  Strict NearLogic has zero violations, pinned statements match, and PR-wide
  changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-ignore-segments-final-audit.log` and
  `/tmp/pr40-ignore-segments-final-style.log`.
- Next: assemble the complete 81 invariant around these concrete segments,
  including whitespace/byte dispatch, scalar completion, member-key/colon
  handling, control-label translation and the final success epilogue. The
  current bracket-opening and restoration segments preserve local 4 rather
  than assuming it is always 1: after a nested opening it can still be 0.
  The container-loop invariant must allow that until the next value entry
  resets it. Full reader/model refinement, reachable allocation room, uniform
  parser bounds, object wrappers, rejection, the seventh method and M9 remain
  open. No additional `sorry` is introduced.

## Complete ignored-container member tail (2026-10-30)

- `SerdeIgnMember.memberCode_eq` pins the entire member tail to the rest of
  81's decoded value-loop body after its four initial blocks. The code includes
  the real array fast path, both whitespace/peek guards with their rejecting
  branches, the key quote test, 650, the colon check, and the branch back to
  the outer value loop.
- `array_next` proves the actual array branch returns to control label 0 with
  value-entry flags `(l3,l4) = (1,0)`, preserving arbitrary caller resources,
  at ten regular operations. `object_next` proves the complete actual ignored
  object key and colon path with the concrete escaped string reader. It accepts
  `Option String`, including syntactically valid ignored keys with invalid raw
  UTF-8, and preserves both tables, all 128 borrowed callee-stack bytes, the
  global stack pointer and an arbitrary `Fr` (scratch/heap/saved String state).
- Its explicit cost is
  `(600 + 96*(q-i) + 300*(e-(q+1)) + 96*(j-e))*regularOpCost`, for quote `q`,
  string endpoint `e` and colon `j`. `cost_le_value` proves this charge plus
  the 60-operation value-entry allowance fits `470*(j+1-i)*regularOpCost`.
  No extra whole-input error reserve or UTF-8-validity assumption is introduced.
- `key_parts` and `key_indices` derive every concrete cursor premise from the
  complete pure machine's successful key/colon continuation. `object_traced`
  therefore needs no separate key-reader or index hypotheses: it executes the
  real member tail, returns the successful pending-value continuation, and
  preserves the remaining 470-per-byte and scratch-growth credits unchanged.
- `next_traced` unifies both branches into the common value-loop entry shape,
  with its logical pending bracket and restored 60-operation allowance. The
  incoming member-state fixed allowance is 75 operations for arrays and zero
  for objects, matching the existing shallow proof's phase accounting. The
  arbitrary caller frame can retain allocator, scratch and saved account-id
  String ownership. These are the keys inside ignored nested containers;
  outer `deserialize_struct` key/value resource-closure conditions remain open.
- Lean MCP verifies the code-location equation, actual execution contracts,
  cursor derivation and quantitative interfaces using only standard axioms.
  The targeted build passes. `just wnear-audit` passes (2819 build jobs; 485
  wNEAR modules, 65963 declarations and 60500 theorems), with only the
  three existing open-refinement dependencies. Strict NearLogic has zero
  violations, pinned statements match, and PR-wide changed-source Lean style
  and whitespace checks pass. Evidence: `/tmp/pr40-ignore-member-final-audit.log`
  and `/tmp/pr40-ignore-member-final-style.log`.
- Next: assemble the complete 81 invariant using `SerdeIgnSegments` and
  `SerdeIgnMember.next_traced`, closing the remaining value/container byte
  dispatch, scalar-completion and control-label transitions and the final
  success epilogue. Then carry full ignored-reader state through the object
  adapter and close reachable room and uniform parser bounds. General
  rejection, the seventh method and M9 remain open. No additional `sorry`
  is introduced.

## Complete-machine container peek and delimiter dispatch (2026-10-30)

- `SerdeIgnContainer` pins four concrete code locations in decoded 81:
  the container peek, the value-loop peek, the nested delimiter dispatch and
  the post-container-loop first-element guard. The rejecting and panic branches
  remain in the checked code, although the contracts below select successful
  paths using their explicit model/byte premises.
- `peek_success` proves both actual whitespace/peek blocks with arbitrary
  escape-label index. It preserves the caller frame and input bytes, updates
  local 5 to the actual optional byte, and advances only over leading JSON
  whitespace, including the EOF case. Its allowance is
  `(125 + 96*wsLen)*regularOpCost`.
- `dispatch_close` reaches the existing actual closing segment on either
  matching delimiter while preserving arbitrary caller resources, at 100
  regular operations. `dispatch_first` takes relative label 0 without eating
  the first member/value byte, at 35 operations, provided it is not a closing
  delimiter or comma. `dispatch_comma` consumes an accepted comma and takes
  relative label 2 toward the member path, at 65 operations. `first_exit`
  proves the actual five-operation post-loop guard for the no-comma first
  element/member case. The two exit labels are deliberately distinct.
- `phase_cases` derives exactly the corresponding three alternatives from
  successful execution of the complete traced pure machine, for either an
  opened container or a continuation after a value. Its close branch retains
  the full saved-frame-pop continuation; its first/comma branches give the
  successful `SerdeIgnMember.nextModel` continuation. `phase_nonempty` excludes
  EOF from either successful container phase. These lemmas replace the old
  shallow-only dispatch classification without assuming a general ignored
  reader contract.
- Lean MCP checks all five execution contracts, four code-location equations
  and the complete-machine classification/non-EOF lemmas with only standard
  axioms. The targeted build passes. `just wnear-audit` passes (2820 build jobs;
  486 wNEAR modules, 66207 declarations and 60722 theorems), with only the
  three existing open-refinement dependencies. Strict NearLogic has zero
  violations, pinned statements match, and PR-wide changed-source Lean style
  and whitespace checks pass. Evidence: `/tmp/pr40-ignore-container-final-audit.log`
  and `/tmp/pr40-ignore-container-final-style.log`.
- Next: assemble the container-loop invariant from these peeks/dispatches,
  `SerdeIgnSegments`' traced open/close operations and `SerdeIgnMember`'s
  value reentry. The remaining value dispatch, scalar-completion and success
  epilogue also need integration. Aggregate instruction accounting remains open:
  compose the phase allowances and tighten repeated-peek/frame charges or
  amortize them across nested opens and later closes as needed. The isolated
  component allowances do not themselves prove the full 470-per-byte bound.
  Full deep 81 refinement, reachable allocation room, uniform parser bounds,
  outer object wrappers, rejection, the seventh method and M9 remain open.
  No additional `sorry` is introduced.

## Actual scalar completion and successful return (2026-10-30)

- `SerdeIgnScalarDone` pins the common scalar-completion tail, success label
  and function epilogue to decoded 81 by three kernel-checked equalities.
- `scalar_pending` proves the actual seven-operation path for a scalar inside
  a container: set local 3 to one, retain local 4 at zero and branch to the
  container phase without touching the saved vector or arbitrary caller resources.
- `scalar_top` proves the actual empty-pop success path at 50 regular operations.
  It uses the tight concrete empty-pop contract, retains the reusable scratch
  allocation and prior live blocks, and restores the 32-byte caller frame.
  Its relative label 3 is distinct from the pending scalar's label 0.
- `success_return` proves the actual seven-operation success/return epilogue:
  result zero, restored stack global and all 160 stack bytes, with the cleared
  saved-vector allocation and arbitrary caller resources preserved.
- Validation: Lean MCP reports no errors and the targeted module build passes
  (1373 jobs). PR-wide changed-source Lean style and whitespace checks pass.
  `just wnear-audit` passes (2821 build jobs; 487 wNEAR modules, 66285
  declarations and 60797 theorems), with only the three existing dependencies
  on the open refinement. Strict NearLogic has zero violations and pinned
  statements match. Evidence: `/tmp/pr40-ignore-scalar-done-final-audit.log`
  and `/tmp/pr40-ignore-scalar-done-style.log`.
- Next: prove the remaining scalar dispatch, compose its cost with the value
  peek and completion tails, and assemble the full traced loop. Structural label
  unwinding and aggregate costs still need proof; the individual segments do
  not establish the complete deep reader. Reachable allocation room, uniform
  parser bounds, outer wrappers, rejection, the seventh method and M9 remain open.

## Complete-machine scalar dispatch and block exits (2026-10-30)

- `SerdeIgnScalar` pins the actual scalar dispatch, value-presence guard,
  complete dispatch body and enclosing block to decoded 81 by four
  kernel-checked equalities. The concrete error and container branches remain
  in that code; successful scalar premises select the proved paths.
- `scalar` proves every successful non-container value: both numeric paths,
  all three literals, and the full ignored-string reader with arbitrary escapes
  and syntactically valid invalid raw UTF-8. It preserves the reader input,
  literal/escape/hex tables, stack global, all 128 borrowed stack bytes and an
  arbitrary caller resource frame. It returns at the exact model cursor with
  local 6 zero and local 7 the initial value byte. Its charge is
  `(470*consumedBytes - 81)*regularOpCost`.
- `scalar_step` and `scalar_indices` extract that scalar endpoint and the
  complete pending-frame continuation from the full traced machine, with
  strict cursor progress and a monotone final endpoint. `scalar_traced`
  preserves that continuation and the unchanged physical frame-growth credits,
  reserving 470 operations per remaining byte. These use the complete machine,
  not the shallow decoder's restricted correspondence.
- `present` proves the real seven-operation presence guard without consuming
  the byte. `pending` and `top` compose the dispatch with the actual scalar
  completion tail at `(470*consumedBytes - 74)` and
  `(470*consumedBytes - 31)` regular operations, respectively.
- `pending_block` and `top_block` include the actual enclosing block and
  translate its control labels. Pending completion becomes normal container-phase
  entry at `(470*consumedBytes - 72)` operations; top-level completion takes
  relative success exit 2 at `(470*consumedBytes - 30)` operations. The pending
  path pays the additional operation for branching to the block's own label.
- `pending_cost` and `top_cost` prove these charges, the existing whitespace
  peek, presence guard and top-level success epilogue fit the existing value
  allowances: `60 + 470*consumedBytes` inside a container and
  `109 + 470*consumedBytes` at top level, including leading whitespace.
  This closes the scalar arithmetic; it does not establish full-loop execution
  or the aggregate container-phase bound.
- Validation: all declarations pass Lean MCP diagnostics; `scalar` passes the
  MCP axiom/source check, and compiled axiom checks for the scalar, trace,
  completion, block and cost contracts use only standard axioms. The targeted
  module build passes (1374 jobs). `just wnear-audit` passes (2822 build jobs;
  488 wNEAR modules, 66514 declarations and 61017 theorems), with only the
  three existing open-refinement dependencies. Strict NearLogic has zero
  violations and pinned statements match. PR-wide changed-source Lean style
  and whitespace checks pass. Evidence: `/tmp/pr40-ignore-scalar-final-audit.log`,
  `/tmp/pr40-ignore-scalar-final-style.log` and `/tmp/pr40-ignore-scalar-axioms.log`.
- Next: connect container-opening dispatch to the existing traced open segment,
  then assemble the complete loop invariant, including its changed heap and
  saved-String ownership. Aggregate nested-container instruction accounting,
  reachable allocation room, uniform parser bounds, outer wrappers, rejection,
  the seventh method and M9 remain open. No additional `sorry` is introduced.

## Complete opening prefix and closing-byte reserve (2026-10-30)

- `SerdeIgnOpening.opening` proves both actual container-dispatch paths in
  decoded 81, including the optional pending-frame save, opening-byte consume
  and relative exit zero. `opening_block` includes the real enclosing block
  and its charged exit into the opened-container phase. The fixed charges are
  110 and 112 regular operations, plus the existing concrete `saveCost`.
  `opening_traced` splits the actual save prefix and preserves the complete
  successful continuation at 252 regular operations plus the changing trace's
  growth charge. Arbitrary caller resources and prior live allocations survive.
- `entryCode_at` pins the first three actual value-loop blocks: whitespace
  peek, presence guard and dispatch. `entry` composes their execution at
  `(384 + 96*wsLen)*regularOpCost` plus the traced growth charge. It updates
  locals and cursor to the opened phase, retains the 80 borrowed stack bytes
  and returns exact scratch/heap/capacity/free-list coordinates. `opening_step`
  and `opening_indices` derive the transition and cursor bounds from the full
  traced machine; no general ignored-reader hypothesis is assumed.
- `SerdeIgnProgress.run_bound` proves a stronger fact than physical-vector
  legality: successful execution in every mode consumes at least one byte for
  each pending outer frame, plus one for its current work. `run_consumed`
  instantiates the full scalar/key readers. The final unrecorded close is
  included, so this also bounds the logical active depth rather than only
  vector pops.
- `SerdeIgnBudget` retains 110 operations per active container from the existing
  470-per-byte allowance. Full-machine progress proves the reserve cannot
  truncate. `regular_reserve` recovers the original allowance exactly when
  that reserve is added back. Its opening, closing, first-member, comma and
  scalar inequalities preserve this reserve across the corresponding phase
  charges. These are arithmetic lemmas, not complete-loop execution proofs.
- `entry_funded` connects that reserve to the complete actual opening prefix.
  It starts from full-machine success and the unchanged 60/109 value-entry
  allowances, establishes the 250/200 opened-phase allowance minus its new
  depth reserve, and leaves six operations for surrounding loop control.
  Remaining growth credits use the returned capacity and allocator bound;
  changing heap ownership and the arbitrary caller frame remain explicit.
- Validation: all three modules pass Lean MCP diagnostics. `entry_funded`
  passes the MCP axiom/source check, and compiled checks of the execution,
  progress and reserve theorems use only standard axioms. Targeted builds pass
  (1377 jobs for the opening module, including all three modules).
  `just wnear-audit` passes (2825 build jobs; 491 wNEAR modules, 66692
  declarations and 61173 theorems), with only the three existing dependencies
  on the open refinement. Strict NearLogic has zero violations and pinned
  statements match. PR-wide changed-source Lean style and whitespace checks
  pass. Evidence: `/tmp/pr40-ignore-opening-final-audit.log`,
  `/tmp/pr40-ignore-opening-final-style.log` and `/tmp/pr40-ignore-opening-axioms.log`.
- Next: connect the close and member execution contracts to the reserve,
  account for loop-label setup, and assemble the full control-flow/ownership
  invariant. The new opening result and phase arithmetic do not yet prove the
  complete deep reader. Reachable allocation room, uniform parser bounds,
  outer wrappers, rejection, the seventh method and M9 remain open.
  No additional `sorry` is introduced.

## Complete closing/member iterations with the depth reserve (2026-10-30)

- `SerdeIgnClosing` pins the actual closing/member block and the whole
  container-loop body by two kernel-checked code equations. `block_nonempty`
  restores the saved head and branches back to the loop; `block_empty` takes
  success exit four. Their charges are 212 and 211 regular operations. The
  complete whitespace-peeking closing iterations cost `337 + 96*wsLen` and
  `336 + 96*wsLen`, respectively. They preserve arbitrary caller resources,
  scratch capacity/heap bounds and the 32-byte caller frame.
- `close_indices` derives the close cursor and complete pop continuation from
  either full-machine container phase. `funded_nonempty` executes the whole
  actual closing iteration, releases the closed frame's reserve, preserves the
  outer continuation and unchanged growth credits, and retains 18 operations
  for surrounding control. `funded_empty` proves the exact final endpoint and
  empty remaining trace, retains the allocated empty vector and leaves 19
  operations for success-label/epilogue cleanup.
- The same actual iteration now has checked first-member and comma paths:
  `iteration_first` costs `162 + 96*wsLen` and becomes normal loop-body exit;
  `iteration_comma` costs `191 + 96*wsLen` and takes relative exit one.
  Only the comma consumes its selected byte. The previously proved dispatch
  guards and the enclosing block's charged exit are included.
- `SerdeIgnMemberBudget.first_funded` and `comma_funded` connect those complete
  iterations to full-machine member continuations and retain the depth reserve.
  They leave 13 and 9 operations, respectively, for the surrounding loop/block
  control, in addition to the actual next-member allowance. `next_depth`
  derives the needed remaining-byte bound through either member kind.
- `object_funded` and `next_funded` execute the complete actual array/key/colon
  tail while retaining the same reserve and growth credits. They fund 64
  operations for the next value entry and a separate operation for its loop
  branch. The key reader remains the concrete full escaped-string reader,
  including syntactically valid invalid raw UTF-8, with all 128 borrowed bytes,
  tables, global and arbitrary heap/saved-String resources preserved.
- `SerdeIgnSegments.start_prefix_tight` proves the actual entry at 53 regular
  operations; the original 60-operation interface is retained as a weakening.
  The scalar dispatch is tightened from `470*consumedBytes - 81` to
  `470*consumedBytes - 82`. Its composed pending/top bodies now cost
  `470*consumedBytes - 75`/`-32`, and their enclosing blocks cost `-73`/`-31`.
  `top_cost` explicitly includes both the outer success-label payment and the
  seven-operation success epilogue within the unchanged 109 value allowance.
  The new 64-operation member value allowance leaves space for loop setup.
- Validation is recorded after the complete build and audit finish.
- Next: assemble the two loop invariants from these funded transitions,
  translate the remaining outer labels and retain the changed heap/scratch
  coordinates and saved String throughout. These contracts do not themselves
  prove the complete deep reader. Reachable allocation room, uniform parser
  bounds, outer wrappers, rejection, the seventh method and M9 remain open.
  No additional `sorry` is introduced.

## Continuation: a single allocation-room budget for state and balance

`BalanceOf297AbsentCall.room_after_state` proves that `HeapRoomK 6` at state
entry supplies the two state-read allocations and leaves `HeapRoomK 4` after
any state-read growth. `state_through_cleanup_six_grows` integrates this into
the checked absent-account suffix: the separate state-read and later room
conditions follow from a single initial six-growth premise. Both proofs use
standard axioms. Reachability of that initial heap-room bound and of the
one-cell free-list entry after parsing remains open, as do the initial shared
proof budget, other branches and the complete method.

## Continuation: discharge the post-state-read gas bound

`BalanceOf297AbsentCall.storageReadUse_after_read` proves a storage read
preserves the modeled cost of a later read of any key.
`balanceReadGasAfterState_exact` instantiates the second-read gas condition with
the exact initial-state lookup cost, and `state_through_cleanup_exact_gas`
integrates that instantiation into the checked 82-instruction suffix. All three
proofs use standard axioms. The generic gas-bound predicate remains Open for an
arbitrary proposed bound, but the composed branch no longer assumes it. The
initial shared proof budget, parser-to-state-read entry resources (including the
one-cell free-list bound), allocation room, other branches and the complete
method remain open.

## Continuation: propagate a shared storage proof budget

`BalanceOf297AbsentCall.balanceReadAfterState_of_budget` derives the second
lookup's canonical trie, storage link, proof budget, absent value and key limit
from the initial state and a budget sufficient for both reads. It uses the
existing `StorageReadPost.next` transition. The remaining uniform post-read gas
bound is stated as `BalanceReadGasAfterState` and shown Open in the frontier.
`state_through_cleanup_of_budget` integrates this derivation into the checked
82-instruction suffix; both new proofs use standard axioms. Parser-to-state-read
entry resources, allocation room, post-read gas and the full method remain open.

## Continuation: state read through absent balance cleanup

`BalanceOf297AbsentCall.state_read_and_unwrap` checks the exact state-read and
successful unwrap instructions for a present model state. The checked
`state_through_cleanup_absent` composition covers the 82 instructions from
state reading through absent-account return and cleanup, starting with an
already parsed owned account. Both proofs use standard axioms.

This is conditional on `BalanceReadAfterState`, the explicit second-read
accounting, trie, proof-budget, absent-key and gas contract, and on reachable
allocation room. The state-read entry requires `pre219`, including a one-cell
free-list bound; it has not been shown to follow from the preceding parser,
which may leave a larger bound. Both the entry-resource predicate and second-read contract are shown Open in
the frontier for this handoff; other methods may already establish the generic
state-read entry resources in their own proofs.
Parsing, resource reachability, all other branches and full method refinement
remain open.

## Continuation: parsed account descriptor through cleanup

`BalanceOf297AbsentCall.argument_copy` checks the exact twelve instructions
copying the already parsed string descriptor into the balance-call argument.
`parsed_account_through_cleanup_absent` composes that handoff with the checked
absent-account suffix over 71 instructions through the function's end. Both use
standard axioms. The result still assumes a parsed owned account descriptor,
initialized state and explicit frame, host, return-limit, prefix-allocation and
heap-room resources. Connecting the parser and state setup, proving reachability
of these resources, and the full accepted-call method remain open.

## Continuation: function 297 absent balance through cleanup

`BalanceOf297AbsentCall.cleanup` checks the final two vector drops and stack
restoration. `call_through_cleanup_absent` composes it with the absent-account
path across the exact 59 instructions from the balance call to the function's
end: the host selects `[34, 48, 34]`, both allocated buffers are freed, and the
stack global is restored. Both proofs use standard axioms. The composition
requires the complete prefix allocation and its unused capacity, four-growth
heap room, the return limit and the existing host/trie and frame premises.
Reachability of those resources, earlier argument/state setup and the complete
accepted-call method remain open.

## Continuation: function 297 absent balance through value return

`BalanceOf297AbsentCall.return_vec` checks the actual dereference and
`value_return` instructions. `call_through_value_return_absent` composes this
with the absent-account path across 47 exact instructions, proving the host
selects JSON bytes `[34, 48, 34]` for zero. It retains the storage-read state
relation and requires an explicit three-byte return limit, four-growth heap
room, and frame resources. Both proofs use standard axioms. Reachability of the
heap room and the enclosing accepted-call method remain open; the subsequent
cleanup is composed in the continuation above.

## Continuation: function 297 successful result extraction

`BalanceOf297AbsentCall.expect_ok` checks the exact eight instructions calling
`Result::expect` on the successful serialized vector.
`call_copy_format_and_expect_absent` composes it with the absent-account path
across the exact 37-instruction slice, preserving the returned vector and host
resources. Both proofs use standard axioms. Reachable four-growth heap room,
argument setup and the full accepted-call method remain open; cleanup is
composed in the later continuation above.

## Continuation: function 297 absent call through serialization

`BalanceOf297AbsentCall.call_copy_and_format_absent` composes the checked
absent-account call and zero-copy slice with the zero serializer over the exact
29 instructions of function 297. It preserves the host, lookup and frame
resources for its caller and proves the serializer's allocation bounds from
`HeapRoomK 4`. The theorem uses only standard axioms. Reachability of that
four-growth room, argument parsing and the enclosing accepted-call method remain
open; the new proof is not claimed to complete the exported method.

## Continuation: function 297 zero serialization

`BalanceOf297AbsentCall.format_zero` proves the next seven decoded instructions
call the existing `to_vec::<U128>` proof on a zero value and return its JSON
string bytes. The theorem has explicit stack, memory, gas and two allocation-room
premises, and uses only standard axioms. The subsequent composition above supplies the extra four output bytes and 32
stack bytes explicitly; reachable allocation room, the accepted method and full
deployed refinement remain open.

## Continuation: function 297 absent-call result copy

`BalanceOf297AbsentCall.copy_zero` proves the actual twelve instructions after
the call copy the absent account's zero balance into the formatting input.
`call_and_copy_absent` composes that proof with `call_absent` over the exact
22-instruction slice of function 297. Both use only standard axioms; the
combined theorem remains conditional on reachable `HeapRoomK 2` and its
explicit host/resource premises. Parser and state setup, formatting and the
full accepted-call refinement remain open.

## Continuation: function 297 absent-call segment

`BalanceOf297AbsentCall.call_absent` proves the actual ten-instruction slice
of exported function 297 that prepares its frame pointers and calls function
293, composing the checked absent-account caller and preserving its postcondition.
The kernel proof uses only standard axioms and is conditional on reachable
`HeapRoomK 2` and the explicit host and resource premises. This is one segment:
the preceding parser/state setup, the later formatting/return code and the full
accepted-call and method obligations remain open.

## Continuation: balance method top-level composition

The full `ft_balance_of` method clause is now checked composition from three
separately named open obligations: no execution issue for any represented
context, full accepted-call refinement including arbitrary resource failures,
and rollback on rejected arguments. Its original statement is unchanged.
The accepted-call obligation has a planned dependency on the checked absent
function-297 call-and-copy segment; neither that edge nor the full method is claimed complete. All
three open leaves and their conditional dependents remain in the strict audit.

## Continuation: absent-account token balance caller

`BalanceOfAbsent.f293_none` proves the actual token balance caller for an
absent account. It copies the owned account string into its stack frame, calls
`f415_none`, returns the two-word zero and restores the stack while retaining
the host postcondition. The proof uses only standard axioms and remains
conditional on reachable `HeapRoomK 2` and its stated runtime premises. The
exported function 297, argument reader and complete method refinement remain
open.

## Continuation: absent-account balance lookup

`BalanceOfAbsent.f415_none` proves the actual fungible-token balance lookup
returns zero for an absent account. It calls the checked absent `LookupMap`
contract, converts `None` to zero, frees the owned account string, restores the
stack and preserves the metered host postcondition. The kernel proof has only
standard axioms and remains conditional on reachable `HeapRoomK 2` and the
explicit host, storage and representation premises. Function 293 now composes
this proof; the argument reader and exported method refinement remain open.

## Continuation: absent LookupMap get

`LookupMapGet.f399_none` proves the actual absent-key `get` path. It constructs
the Borsh key, calls the checked absent `get_raw` proof, frees the key, returns
`None` with zeroed payload and restores the stack. The proof uses only standard
axioms and is conditional on `HeapRoomK 2`: deriving that multi-allocation room
from reachable method states remains open. It is now integrated into function
415; the enclosing method and argument reader remain open.

## Continuation: absent raw lookup

`LookupMapGet.f400_none` proves the real `get_raw` path for an absent key:
it constructs the combined key, calls `f548_noneF_host`, frees the temporary
key and returns `None`, preserving the host postcondition and the stated heap
bound, conditional on the explicit reachable allocation-room obligation. The checked
caller integrates the absent storage-read theorem. The
`LookupMap` 399 absent branch now composes this result; parser integration and
the method proof remain open.

## Continuation: absent storage read

`StorageReadWrapF.f548_noneF` proves the actual Wasm `storage_read` wrapper
returns `None` for an absent key, preserving an arbitrary allocator bound and
the host postcondition without allocating a value. `f548_noneF_host` instantiates
that contract with the metered host, trie overlay and explicit proof budget.
The wrapper is integrated through the absent `LookupMap` 400 and 399 proofs;
the method caller still needs checked composition.
The present-key path and full method remain separate obligations.

## Continuation: `ft_balance_of` model agreement

`FtBalanceOfMethod.account_lookup_and_step` proves that the exact encoded key
for an arbitrary requested account retrieves the optional pair of binary words
corresponding to the represented model balance. Decoding the words without
truncation, or defaulting an absent record to zero, gives the initialized
`ft_balance_of` model boundary result, including its storage-stake failure.
This is kernel-checked under the stated context, state, representation and
erased-host premises; it is a planned dependency of the method proof, not yet
a checked call from it. The argument reader, actual Wasm method execution,
resource bounds and uninitialized branch remain open.

The pinned protocol parse witness also remains open: `Lean.Json.Parser.anyCore`
is opaque, so compiled evaluation of the JSON does not establish its result in
the kernel. A verified parsing route or another sound proof of that exact parse
statement is still required.

## Methods

There are 15 exported methods; six now have complete per-call refinement proofs under their protocol premises.

| Method | Status | Top theorem |
|---|---|---|
| `ft_total_supply` (296) | done | `FtTotalSupplyAll.ftTotalSupply_refines_all` |
| `storage_minimum_balance` (231) | done | `StorageMinimumBalanceRefines.storageMinimumBalance_refines_all` |
| `storage_balance_bounds` (306) | done | `StorageBalanceBoundsRefines.storageBalanceBounds_refines_all` |
| `ft_metadata` (309) | done | `FtMetadataRefines.ftMetadata_refines_all` |
| `new` (290) | done | `NewRefines.newRefines_all` |
| `near_deposit` (234) | done | `NearDepositMethod.nearDeposit_refines_all`, under `CostsV86`, `LimitsV86`, `CostsDepositV86`, the module protocol premises and code size. Gas, functional agreement and host preconditions are all discharged. |
| `ft_balance_of` (297) | argument layer, partial parser acceptance, and account lookup/model-boundary agreement | `FtBalanceOfMethod.account_lookup_and_step`; Wasm method and full parser remain open |
| `storage_balance_of`, `storage_deposit`, `storage_withdraw`, `storage_unregister`, `near_withdraw`, `ft_transfer`, `ft_transfer_call`, `ft_resolve_transfer` | not started | they need the parser; `ft_transfer_call` and `ft_resolve_transfer` also need promises and promise results |

The premises left in the method theorems are the binary's code size and protocol 86's parameters:
- `CostsV86` and `LimitsV86` (in `FtTotalSupplyGas`/`FtTotalSupplyPre`);
- `CostsNewV86` (in `NewPanicsRefines`);
- `CostsDepositV86` (in `NearDepositCostFees`, extends `CostsNewV86`).

Every value in them is checked against `near-lean/vm/configs/runtime_config_v86.json`. M9 discharges them.

## Infrastructure in place

**Logic and the boundary.**
- SAF-67, the storage-proof budget (#42):
  - `relax` turns recording off;
  - the below-the-bound case uses `eraseP` (`Method.lean`, `Relational.lean`);
  - the trap clause in `runMetered_relaxL`.
- Calls that trap: `MFunSpecT`, `mwpi_call_host_trap`.
- The method-level panic framework: `Panics.lean`.

**Context.** New `Context.WF` fields:
- `trie_no_zero_hash`;
- `prospective_unique`;
- `committed_unique`.

**Host contracts** (`near-lean/near-logic/NearLogic/Hosts`), each with a `.next` lemma that carries the proof budget:
- `storage_read`, which reads through the overlay (`viewVal`, `storage_lookup_view`);
- `storage_write`, `storage_has_key`, `storage_remove`;
- `panic_utf8`, `log_utf8`;
- `attached_deposit`, `predecessor_account_id`, `storage_usage`.

**Allocator.** wee_alloc on a free list of any length (`AllocWalk*`). Reallocation is in `VecGrow`, the scratch buffer in `ScratchGrow`, the `String` sinks in `StrSink*` and `HookSink`.

**Formatting.**
- `core::fmt::write` with any number of arguments, including a trailing piece: `FmtWriteN`, `FmtWriteT`, `FmtWriteP`.
- `Formatter::pad`, and `fmt_u64` for values below 10⁴.
- `format!`.

**Panics.** Rust's panic path is unconditional:
- `begin_panic` (`PanicBeginFull.f664_full`);
- `expect_failed`, `core::panicking::panic` (`PanicFmtFull.f879_unc`, `f853_unc`);
- near-sdk's `panic_str` (`PanicStr`).

The texts are proved equal to the model's `Panic.message` (`PanicText`).

**Containers.** `LookupMap` get, insert and remove, and Borsh for the contract, `String` and `u128`.

**JSON arguments (M6).**
- **Pure layer.** serde's struct machine is proved equal to the model's `parse` followed by `structFields` (`SerdeStructModel.fromSlice_eq`, `decode_balanceOf`). `ignore_value` as an iterative machine is in `IgnoreModel`.
- **Strings.** `parse_str` and `parse_escape` hold on every input, against `stringBody` (`ParseStrEsc.f646_spec`, `str_model`). `from_utf8` agrees with `String.fromUTF8?`. `ParseEscape.lean` takes about 45 minutes to build.
- **Accepting half.** `FromSliceShallow.acceptContract_shallow`, at `K1 = 470` regular ops per argument byte:
  - it covers input without escapes, with ignored values at most one bracket deep;
  - its cost is `(1725 + 470·len)·c + x169`, with under `20·c` of slack;
  - the binary's measured worst case is 275.5 Mgas per byte against the model's 400 (`scenarios/27_arguments_cost.json`).

## Next steps

1. **The parser, finishing `ft_balance_of`'s argument contract.**
   1. `RejectContract`. A loose cost suffices. Use `fromSlice_eq` and the reject paths listed in M6. The outer struct-error and trailing-character paths are proved; 228's EOF case is discharged through 65. Finish the other 228 error cases, and integrate the general string/ignored-value readers.
   2. Escapes in the accepting half:
      - absorb `growthBudget` into the unchanged allowance under the reachable
        heap/scratch invariant; use the concrete append trace and its logarithmic
        growth-count, copy and page bounds;
      - discharge `KeyConditions`/`ValueConditions` and the reachable member-state
        bounds of the proved changing-state object loop;
      - keep the all-outcome `costRun` separate: it has a proved quadratic lower
        bound even on accepted newline escapes (`StrCostLower`);
      - the copied array is integrated through 214/228/78/66/65, with scratch
        cleanup; carry the proved changing-state object result through 78/66/65
        and close general argument-contract bounds, including hex-table ownership;
      - instantiate the remaining ignored-reader state transition in that loop;
      - extend the escaped shallow 81 reader to deep frames, preserving its
        changing scratch/heap state and the complete stack footprint.
   3. Ignored values nested deeper: use `SerdeIgnStack`'s proved clear/push/pop
      contracts and `SerdeIgnTrace`'s pop-aware growth budget while tracking the
      full scratch frame stack in 81. The complete pure trace and its consumed-byte
      peak bound are proved in `SerdeIgnMachineTrace`; match the actual 81 body
      to that trace. `SerdeIgnSegments` supplies the concrete entry, save and
      restore transitions; `SerdeIgnMember.next_traced` supplies the complete
      member tail and value-loop reentry with traced credits. `SerdeIgnContainer`
      supplies actual peeks/dispatches and their full-machine case classification.
      `SerdeIgnScalar` supplies complete scalar dispatch/completion and block exits.
      `SerdeIgnOpening.entry_funded` connects the actual full opening prefix to
      `SerdeIgnBudget`'s closing-byte reserve; `SerdeIgnProgress` supplies the
      needed logical-depth/remaining-byte bound. `SerdeIgnClosing` now funds
      both complete closing iterations, while `SerdeIgnMemberBudget` funds the
      complete first/comma iterations and next-member tails with explicit control
      credits and a 64-operation value entry. Assemble both loops, finish their
      outer-label translations and retain the changed heap/scratch coordinates.
      `Hyp81` must allow heap and scratch changes.
2. **`ft_balance_of`, method level.** Take the parser's contracts as parameters until they are proved. The argument layer is in `EnvInput` and `ArgsLeaves`, the balance read in `LookupMapGet`/`StorageReadWrapF`.
3. **The remaining methods**, in M8's order:
   - `storage_balance_of` (its parser is the same code as `ft_balance_of`'s);
   - `storage_*`, `near_withdraw`, `ft_transfer`;
   - then `ft_transfer_call` and `ft_resolve_transfer`, which need promise and promise-result host contracts.
4. **M9.** Instantiate the checked global/exported composition: discharge the remaining method contracts, pinned-JSON parse witness, `WProtocol`, `CostsV86`, `LimitsV86`, `CostsNewV86` and `CostsDepositV86`. The deployed code size is already kernel-checked.

The complete decoded `ft_balance_of` body is checked for a copied-string array
and an absent account. `copied_array_absent_body_initial_room` derives both input
register room and account-copy allocation room from the initial combined growth
budget. It still assumes the parser's `roomRun`, the concrete input shape, trie
and absent-account facts, host and frame resources, and gas; it is not the full
accepted/rejected method refinement. The frontier's type-dependency graph lists
`RegOk` and `roomFor` on the helper because they occur as derived conclusions,
not because the helper assumes them.

The checked conjunction `copied_array_absent_body_model_agreement` now pairs that
decoded-body execution with the model's zero result for the same absent key.
It explicitly requires a well-formed represented state, erased-host agreement and
zero storage deficit in addition to the execution assumptions; it does not yet
derive the complete boundary refinement or cover other inputs and outcomes.

## Continuation: explicit global composition

`Binary.Exported.Clauses` names the exact exported-method interface, including
execution safety, sufficient-resource agreement, arbitrary-resource rollback and
rejected arguments. It is an **Open verification contract**, not a proof.
`all_clauses` assembles it from the checked fifteen-method dispatch, reviewed
`Environment` premises, code size and the nine named `Remaining` contracts.

`refines_wnear_of_clauses` now closes the entire deployed-binary refinement from
that interface: the exported branch consumes it, and the non-exported branch uses
the kernel-checked module export facts and runtime rollback result. The original
`refines_wnear` calls this composition with `refines_wnear_exported`; its statement
and admitted leaves are unchanged. `refines_wnear_with_obligations` additionally
exposes an admission-free route from `Environment` and `Remaining` to the full
refinement. These assembly theorems contain no `sorryAx`, but remain
**Conditional** because their exact verification contracts are unresolved. The
blueprint checks both the explicit hypotheses and their actual caller edges.

The next parser-room obligation must cover the actual `roomRun` definition:
error-box space before and after each scratch append, each reserve's `roomRes`,
and every intermediate heap length permitted by `hlAfter`. A bound only on the
successful append trace and downstream six allocations does not by itself
establish this all-outcome contract. Keep that distinction explicit when deriving
room from initial method resources.

This checkpoint integrates the global composition; it does not discharge a method,
protocol premise, parser hypothesis or deployment parse witness. In particular,
`IgnoreHyp`, `KeyConditions`, `ValueConditions`, parser room and reachable resource
bounds remain open, and all downstream method obligations remain visible.

## Working notes

- **Running agents.** Agents work in their own worktrees and copy `.lake` from the main worktree. They must not launch helper agents: cleaning up a worktree once removed a sub-agent's worktree while it was still working.
- **Merging.** Always check the build's own exit status before pushing; piping it through `grep` hides failures.
- **Tactics.** The tactic pitfalls are collected in the M6 and M8 notes: `mcredits` resets, `Hide`, `mwpi_split`, deep-recursion workarounds.
- **Fixed by the `near_deposit` agent**:
  - **The digit table at 1070974 was owned twice,** by the log data and by the panic hook's location formatting. It is now passed separately to the panic sites.
  - **`GetFmt.getData` named the wrong table entry for the sink's `write_str`.** The vtable word at 1065692 is entry 166, not 165.
