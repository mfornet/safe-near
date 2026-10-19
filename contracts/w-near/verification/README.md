# wNEAR verification

Formal model and specifications of `wrap.near`
(`../contract.wasm`, code hash `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1`,
source `../source/w-near` at core-contracts commit `54f8267`, near-sdk 3.1.0).

The layout follows `docs/human/PROJECT_STRUCTURE.md`:

| Directory | Lake library | Content |
|---|---|---|
| `Model/` | `Model` | The model: state, host context, every method as a Lean function, on-chain layout |
| `Spec/` | `Spec` | Properties to prove, one `def ... : Prop` each |
| `Proofs/` | `Proofs` | One theorem per spec (`sorry` where still open) |
| `blueprint/` | | Lean blueprint (`docs/human/PROVING.md`), fed by `@[blueprint]` annotations via LeanArchitect |

```
just build            # lake build
just sorries          # which specs are still open
just blueprint-web    # lake build :blueprint && leanblueprint web  -> blueprint/web/
just blueprint-pdf    # -> blueprint/print/print.pdf
```

Packages are shared with `near-lean` (`packagesDir = ../../../near-lean/.lake/packages`,
toolchain `v4.34.1`, Mathlib `v4.34.1`, LeanArchitect `v4.34.0`); the project
depends on `near-lean/vm` for `Spec/RuntimeInstance.lean`.

## The model

`Model/State.lean` keeps the three pieces of on-chain state of the
`FungibleToken` with mathematical types: the set of registered accounts, a
balance function, the total supply and the measured per-account storage usage.
`Model/Methods.lean` has one function per exported method and the entry point
`step cfg state env call : Except Panic Outcome`, which also implements the
checks the `#[near_bindgen]` wrapper generates. Every `require` is one panic
site in the Rust source, in source order. `Model/Storage.lean` is the exact
Borsh layout (`encode`) and its inverse, the view of `docs/human/NEAR_MODEL.md`.

Facts about the source the model relies on (verified against near-sdk 3.1.0,
near-sdk-core 3.1.0 and near-contract-standards 3.1.0):

- View methods (`&self`) have no attached-deposit check; non-payable mutating
  methods panic with `Method <name> doesn't accept deposit`.
- `ft_resolve_transfer` is `#[private]`; `new` is `#[init]` and the contract
  is `PanicOnDefault`.
- `storage_byte_cost()` is the constant `10^19`, not a host call.
- `ft_transfer_call` computes `prepaid_gas - 30 TGas` with overflow checks on.
- `ft_resolve_transfer` parses the receiver's return value as a JSON `U128`;
  anything else counts as "nothing used". The model receives the parsed value
  in `Env.promiseResult`.
- `account_storage_usage` is measured with a 64-byte account id (125 bytes
  under mainnet accounting, hence the 0.00125 NEAR fee).

## Specifications

| Spec | Statement | Proof |
|---|---|---|
| `InvPreserved` | Bounds, `Σ balances = total_supply` and the measured storage usage are preserved by every execution | proved |
| `BalanceAuthorization` | Only the predecessor loses balance, except the receiver of a transfer-call inside the contract's own callback, by at most the transferred amount | open |
| `RegistrationAuthorization` | Only the predecessor can be unregistered | open |
| `Conservation` | Minted supply plus collected fees never exceed deposit minus NEAR sent out (per execution; solvency follows at chain level) | open |
| `WithdrawAvailable` | A holder attaching 1 yoctoNEAR can always unwrap any amount it holds, and gets `amount + 1` back | proved |
| `DepositAvailable` | A positive deposit that fits the supply (and covers the fee if unregistered) always wraps | proved |
| `ViewsPure`, `ViewsTotal` | View methods never panic, never change state, never schedule promises | proved |
| `BalanceOfCorrect`, `TotalSupplyCorrect` | `ft_balance_of` and `ft_total_supply` report the model balance and the sum of balances | proved |
| `InitOnce` | `new` cannot run twice; nothing runs before `new` | proved |
| `ProjectEncode` | The view recovers every well-formed state from its storage | open |
| `StorageCoverage` | Occupied storage is at most the `STATE` record plus `account_storage_usage` per registered account | open |
| `Refines` / `RefinesNearLean` | The binary executed by the runtime behaves exactly as `step`; `Spec/RuntimeInstance.lean` instantiates the interface with `near-lean/vm` so the obligation is concrete | stated, open |

## Proof approach and lessons

`Proofs/StateLemmas.lean` characterises each internal operation
(`deposit_ok`, `withdraw_ok`, `registerAccount_ok`, ...) as an iff, plus how
`setBalance`/`register`/`unregister` move `supply`. Preservation proofs then
follow the monadic structure of each method with `bind_ok_iff` and
`split_ifs`. Two things learnt while doing it, both relevant to how models
should be written:

- Keep amounts as literal `Nat`. `omega` does not look through `abbrev`s, so
  `abbrev Balance := Nat` silently disables it on every hypothesis typed with
  the alias.
- Split long methods where the Rust code switches concerns
  (`ft_resolve_transfer` became `unusedAmount` + `resolveRefund`): the pieces
  get their own lemmas and the proofs stop depending on how `do` desugars.

The open specs (`BalanceAuthorization`, `RegistrationAuthorization`,
`Conservation`) are each a pass over all fifteen methods; the natural next
step is one relational characterisation of `dispatch` from which all three
follow by case analysis. `ProjectEncode` and `StorageCoverage` need
injectivity of the Borsh encoders in `Model/Borsh.lean`.

`Spec/Refinement.lean` states the interface the proofs need from a runtime;
`Spec/RuntimeInstance.lean` fills it with `near-lean/vm` (`NearVM.run`, the
JSON encodings of near-sdk 3.1.0, receipts read back as model promises), so
`RefinesNearLean cfg code size modelCfg` is the exact obligation on
`contract.wasm`. The blueprint's chapter "Chain-level properties" states
solvency, the storage lock and the end-to-end transfer-call property
informally; `near-lean/chain` now has the definitions (`Reachable`,
`runIsolated`, `touches`, `upgrades`) to write them in Lean. Bounded runs now
report whether they completed; `measureCallGasBurnt` measures a successful
settled run but does not establish sufficient prepaid gas. The refinement
obligation requires model issues to be absent and successful receipt projections
to be valid. JSON and receipt projection regression tests run with
`just runtime-adapter-test` from the repository root.

The refinement input includes `ExecutionResources`: liquid balance before the
attached deposit and total measured storage usage, including account/code
overhead. These come from the enclosing runtime, rather than zero defaults.
`Valid` bounds host integers and requires usage to cover the stored records;
`Supports` requires funds for the model's outgoing deposits and room for its
resulting storage. Proving these preconditions from chain-level solvency remains
an obligation. Successful refinement additionally requires exact NEAR accounting,
retained storage overhead, and bounded burnt/used gas. Every failed execution,
including out of gas, must restore input storage, balance and usage and emit no
receipts. Failure logs may survive. These are specification obligations, not yet
proved properties of the deployed binary. Adapter regressions carry real resources
through initialization, deposit, withdrawal, panic and gas exhaustion.
