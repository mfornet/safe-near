# Third-party notices

This repository is licensed under the Apache License 2.0 ([LICENSE](LICENSE)).
The material listed below comes from other projects and stays under its own
licence.

## Contract binaries (`contracts/*/contract.wasm`)

Each binary is the code deployed on NEAR mainnet, fetched byte-for-byte. Its
source is the upstream repository pinned as the `source/` submodule, at the
commit in `contract.toml`; `build.sh` rebuilds the binary from it. The binaries
are redistributed under the upstream licence. The Lean models, specifications
and proofs about them are this project's own work.

| Contract | Upstream | Licence |
|---|---|---|
| `aurora-engine` | [aurora-is-near/aurora-engine](https://github.com/aurora-is-near/aurora-engine) | CC0-1.0 |
| `eth2-client` | [Near-One/rainbow-bridge](https://github.com/Near-One/rainbow-bridge) | GPL-3.0, see [contracts/eth2-client/LICENSE](contracts/eth2-client/LICENSE) |
| `intents-defuse` | [near/intents](https://github.com/near/intents) | MIT, Copyright (c) 2025 NEAR Foundation |
| `linkdrop` | [near/near-linkdrop](https://github.com/near/near-linkdrop) | none stated upstream |
| `mpc-contract` | [near/mpc](https://github.com/near/mpc) | MIT, Copyright (c) 2025 NEAR One Limited |
| `omni-bridge` | [Near-One/omni-bridge](https://github.com/Near-One/omni-bridge) | MIT, Copyright (c) 2025 Near One |
| `ref-farming` | [DevOfCredit/ref-contracts](https://github.com/DevOfCredit/ref-contracts) | MIT or Apache-2.0, Copyright 2019 Ref Finance |
| `skyward` | [skyward-finance/contracts](https://github.com/skyward-finance/contracts) | Unlicense (public domain) |
| `sputnik-dao-factory` | [near-daos/sputnik-dao-contract](https://github.com/near-daos/sputnik-dao-contract) | MIT, Copyright (c) 2021 near-daos |
| `sputnikdao2-v3.2` | [near-daos/sputnik-dao-contract](https://github.com/near-daos/sputnik-dao-contract) | MIT, Copyright (c) 2021 near-daos |
| `w-near` | [near/core-contracts](https://github.com/near/core-contracts) | MIT or Apache-2.0 (the repository's current licence; the pinned commit has no licence file) |

`eth2-client` is GPL-3.0: its complete corresponding source is the pinned
rainbow-bridge commit, and the GPL text sits next to the binary. `linkdrop`
carries no licence upstream; it is included as the public on-chain code of the
`near` account, and will be removed on request of its authors.

## nearcore

[nearcore](https://github.com/near/nearcore) is licensed MIT or Apache-2.0.

- `tools/node-conformance/src/storage_fam.rs` copies type definitions from
  nearcore's `core/store` (marked in the file).
- `near-lean/vm/configs/*.json` are runtime configurations dumped from nearcore
  (`tools/dump-runtime-config`).
- The Rust tools under `tools/` link nearcore crates (`near-primitives`,
  `near-vm-runner`, ...) from crates.io; they are not vendored.

## WasmLogic

`near-lean/wasm-logic` ports material from
[Iris-Wasm](https://github.com/logsem/iriswasm) (MIT, Copyright (c) 2024 Logic
and Semantics @ Aarhus University) and follows
[iris-lean](https://github.com/leanprover-community/iris-lean) (Apache-2.0).
Details and the full MIT text are in
[near-lean/wasm-logic/NOTICE](near-lean/wasm-logic/NOTICE).

## lean-lsp-mcp skill

`.claude/skills/lean-lsp-mcp/SKILL.md` is adapted from the README of
[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) (MIT, Copyright (c)
Oliver Dressler).

## Submodules and dependencies

Not copied into this repository, listed for reference:

- `near-lean/wasm/vendor/testsuite`:
  [WebAssembly/testsuite](https://github.com/WebAssembly/testsuite),
  Apache-2.0. `near-lean/wasm/testsuite_report.txt` records results of running
  it.
- `contracts/*/source`: the upstream contract repositories above.
- Lean packages fetched by Lake (mathlib, batteries, aesop, iris-lean, ...):
  Apache-2.0.

## Talos (git history only)

Commits from `1a6ceb2` (2026-10-16) up to `5713333` (2026-10-23) contain a copy
of the interpreter and codelib of
[Talos](https://github.com/cajal-technologies/talos), licensed AGPL-3.0, with
its licence file. That code was removed and replaced by a runtime written from
the WebAssembly specification (see `notes/history/wasm_runtime_rewrite.md` and
the clean-room reviews in `near-lean/wasm/REVIEW.md`). No Talos material is in
the current tree, and the Apache-2.0 licence does not apply to those
historical snapshots of Talos code.

## MIT License text

The MIT-licensed material above is distributed under the following terms, with
the copyright notices given above:

```
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
