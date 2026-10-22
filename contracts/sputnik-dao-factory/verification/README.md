# Sputnik DAO factory verification — in progress

Pinned source: `2b0f34a3860460f285307ec2ccf36345acbe05a2`, crate
`sputnikdao-factory2` 0.2.1. Binary hash:
`BXd5idTXSnC7WRfxHmi7z4crw2F5WXQJ6MZUEv8DfnnY`.
The manifest requests near-sdk 5.24; Cargo.lock resolves **5.24.1**, checksum
`0f3fa35758aba48e4f13528ba2f603e860dad03233d446e5c65ebd619296b607`.
The SDK macro and legacy collections at that version were inspected locally.

This package now has a typed, atomic model for **all 18 exported source methods**,
including SDK wrapper guards, raw trie mutations, legacy collection decoders,
receipts and return values in transaction context. The model is an executable
specification, not a
deployed-binary refinement. Method invariants, full collection representation
proofs, concrete runtime connection and chain-level properties remain open.
Passing builds/audits below establishes only the checked declarations present here.

```sh
just build sputnik-dao-factory
just audit contracts/sputnik-dao-factory/verification
```

`Model/Storage.lean` models a shared raw trie, Borsh keys, and the exact internal
storage checks/operations used for code reads, deletion and default selection
after authorization. `Model/Transaction.lean` gives ordered reads and writes with
an explicit atomic-failure boundary. `Model/Borsh.lean`, `Model/Collections.lean`
and `Model/Methods.lean` cover serialized headers, vector/set/map operations and
all exported entry points. `Proofs/Trie.lean` and `Proofs/Transactions.lean`
prove raw key uniqueness across every successful modeled call, initialization
guards and early callback/deposit guards. `Proofs/Callbacks.lean` proves failed
creation refunds the exact original deposit without registration, and distinguishes
successful, unready and missing callback results. The successful and failed
branches are also proved through the exported wrapper and STATE commit, conditional
on a decodable header and successful set insertion for the success branch.
`Proofs/Borsh.lean` proves little-endian, byte-vector, exact set/map header and
metadata value encode/decode round trips under their u32/u64 length bounds.
The UTF-8 inverse for Lean strings is proved from the kernel representation.
`Proofs/Receipts.lean`
proves that a `create` call from a qualifying state schedules the exact base and
callback receipts while returning promise 0, conditional on the default raw key,
account syntax and minimum deposit checks.
`Spec/Storage.lean` states a canonical DAO layout with explicit vector order and
membership indexes. `Proofs/Storage.lean` proves `new` establishes its empty
instance, that the count getter agrees with its vector length, and that a code
key alias at an absent DAO's index is excluded by this conditional invariant.
The same files state a canonical ordered metadata-map layout and prove that its
empty header decodes, while `get_contracts_metadata` fails if that header is
missing and returns an empty list when it is present and empty.
`Proofs/StorageProjection.lean` proves the general projection: under a coherent
metadata layout and bounded values, `get_contracts_metadata` returns the exact
stored key/value vector order through the exported entry point.
`Proofs/DaoProjection.lean` proves canonical Borsh account decoding and that
the exported DAO list getter returns the exact vector order under a weaker
vector-only layout. Its pagination theorem returns the corresponding physical
slice when `from_index + limit` fits u64, including an empty result past the
end; overflowing addition aborts before vector reads. The weaker layout does
not assume unique accounts or coherent membership indexes.
`Proofs/DaoAliasGetter.lean` applies it to the code/DAO key-alias witness: after
the previously proved membership erase and reinsertion sequence, a two-entry
STATE header makes the exported list getter return the same account twice.
It also gives a constructed raw state in which code bytes occupy an absent
DAO's membership key: a successful exported callback returns `true` without
appending that account, and a following list getter remains empty. These are
source-model storage witnesses, not full reachable chain traces.
`Proofs/DaoInsert.lean` proves both successful-callback insertion branches.
With an absent raw membership key and u64 vector room, the exported callback
appends one index and element, saves STATE, preserves the canonical DAO layout,
and the list getter reads back the appended account. With an existing raw
membership key, it returns `true` and resaves the unchanged header without
growing the vector; a coherent starting layout remains coherent.
`Proofs/MetadataInsert.lean` proves that the first successful
`store_contract_metadata` establishes that layout when the metadata index
namespace is empty. Both values of `set_default` are covered; a following
getter returns the inserted pair, and the `true` branch selects its hash.
`Proofs/MetadataMalformed.lean` gives the exact exported result of replacing a
valid existing value in a singleton map: the value record changes and the same
header is saved again. It proves that the canonical singleton layout survives
the replacement and that a following getter returns the new value. It also
proves the failure case: replacing an existing metadata entry whose old value
bytes are malformed provisionally writes
the replacement, then fails while decoding the discarded old value. The
exported owner-only method returns `invalidMetadata` for either default flag;
the pure transaction model commits no writes on failure. Runtime rollback
refinement remains open. `Proofs/MetadataSecondInsert.lean` proves that adding a
distinct second hash to a canonical singleton map extends the index, both
vectors and header coherently; the exported getter returns both pairs in order.
`Proofs/MetadataGeneralInsert.lean` extends insertion to every canonical map
length with room below the u64 vector limit: an absent hash appends its index,
key and value at the old length. The exported method preserves the ordered
layout, and its getter returns the old entries followed by the new pair when
values are bounded.
`Proofs/MetadataRemove.lean` proves the singleton deletion path through the
exported method: the index and two vector cells are removed, the old value is
decoded, and an empty header is saved. The resulting raw storage satisfies the
empty metadata layout, and a following getter returns an empty list.
`Proofs/MetadataSwapRemove.lean` proves deleting the first entry of a canonical
two-entry map: the final key is read, its index is rewritten to zero, the final
key and value cells move into slot zero, and their old slot-one cells are
removed. The exported method preserves a singleton layout, and a following
getter returns the surviving pair. `Proofs/MetadataTailRemove.lean` handles
the other two-entry branch: removing slot one deletes its index and vector
records without rewriting slot zero. The exported method preserves the first
entry's layout, and its getter returns that entry.
`Proofs/MetadataAbsentDelete.lean` proves a general no-op branch: deleting a
hash absent from a coherent map resaves the same header, preserves its layout
for any bounded map length, and leaves the getter's ordered result unchanged.
`Proofs/MetadataMalformed.lean` also gives an arbitrary-index replacement
theorem: for a present index below the u64 vector bound and a bounded old
value, the exported store method replaces exactly that value record and resaves
the same header. `Proofs/MetadataGeneralLayout.lean` proves for every bounded
coherent map that the replacement preserves the canonical layout with the
logical value updated at that index, and the exported getter returns the
resulting ordered list. `Proofs/MetadataGeneralRemove.lean` proves general nonempty vector
pop and both final-slot and nonfinal-slot swap-removal mechanics. It also proves
the exact exported storage effect for deleting the final metadata entry from a
map of at least two entries, under a bounded old value and coherent raw index
and vector records. For a bounded coherent map, the final-entry deletion also
preserves the canonical layout of the remaining prefix, and the exported
getter returns exactly that prefix. For a nonfinal entry at any bounded map
size, it proves the raw SDK transition under canonical layout and explicit
target/last-slot facts: erase the removed index, point the moved hash to the
vacated slot, swap both vectors, decode the evicted value, and save the shorter
header through the exported method. It also proves that this result preserves
the canonical layout with the last pair moved into the removed slot and that
the exported getter returns exactly that reordered list. The hypotheses expose
the SDK's u64 index bound, distinct hashes, present vector records, and
decodable old metadata. Concrete runtime refinement remains open.
`Proofs/Authorization.lean` proves that each owner-only exported method rejects
a different predecessor before running its body, provided the STATE header and
effective OWNER value decode successfully.
`Proofs/Admin.lean` proves the exported owner update, valid-owner getter
readback and rejection of the previous predecessor on subsequent owner-only
calls. It proves the default-hash setter's raw-key-present and missing branches
and its getter readback. The owner argument's valid AccountId condition is
explicit because the pure Call constructor does not implement SDK JSON parsing.
`Proofs/AdminAlias.lean` extends the DAO-index collision witness through the
exported owner-gated default setter and default-hash getter: a constructed
STATE-plus-DAO-index raw state satisfies the setter's existence check even
though the eight-byte index is not Wasm. Chain reachability remains open.
`Proofs/Update.lean` proves the exported `update` guard order and exact
successful receipt: the effective owner must decode even for a DAO-self caller;
the predecessor must be owner or DAO, a raw membership key must exist, and the
raw code key must exist. Success leaves factory storage unchanged and returns
promise 0 for one `update` call with raw code bytes, zero deposit/static gas,
and weight 1. Failure at the authority, membership or code check commits no
receipt in the atomic model. A constructed alias state with an empty DAO vector
nevertheless passes both raw existence checks and schedules a four-byte
payload; no chain reachability or receiver success is inferred.
`Proofs/Store.lean` proves the two source-model `store` branches through the
exported wrapper: a sufficient deposit commits the raw code and deploy-global
receipt, while an insufficient deposit aborts after the provisional write under
the model's atomic transaction rule. The cost is bounded by u128 saturation.
`Proofs/Delete.lean` proves the exported deletion aborts on a missing METADATA
header even though the method body has already provisionally erased the code
key. This makes runtime rollback a precise obligation for that path.
`Proofs/Namespaces.lean` supplies checked counterexamples to disjoint code/DAO
storage. The binary/source surface is recorded in
[binary-boundary.json](binary-boundary.json); this is static evidence, not runtime
conformance. The blueprint index is [blueprint/README.md](blueprint/README.md).

## Why the full model must keep raw storage

The factory stores code directly under its supplied 32-byte hash. Its DAO
`UnorderedSet` uses `di + borsh(AccountId)` for membership and `de + u64 index`
for the vector. A 26-byte account has a 32-byte membership key. In particular,
`aaaaaaaaa.sputnik-dao.near` is a valid direct child with that length.

`collisionHash` is exactly the 32 bytes of its membership key. No SHA256
collision or preimage search is involved: administrative methods accept any
32-byte `Base58CryptoHash`. The kernel checks these source-model facts:

- the two raw keys are identical;
- with that DAO index present, the storage check in the owner-authorized default
  setter accepts the supplied hash;
- the raw code getter returns the eight-byte DAO index, not Wasm;
- internal code deletion removes membership but retains the DAO vector element;
- after that deletion, a successful set insertion appends the same DAO again,
  leaving two equal vector entries;
- with the matching two-entry STATE header, the exported DAO list getter
  returns both equal entries;
- a constructed absent-DAO/code-key alias can make an exported successful
  callback return `true` without vector registration;
- the fixed OWNER, CODE, STATE and METADATA keys are disjoint from code keys by
  length; the canonical DAO and metadata vector keys and metadata indexes are
  also disjoint from code keys. Code/DAO membership keys are not, and overlap
  requires a 26-byte UTF-8 account ID.

These are storage-level witnesses. They do **not** prove an on-chain exploit or
bypass owner checks. The complete exported deletion also checks the default hash
and invokes metadata deletion, which requires an existing metadata header.
Those guards must be included before claiming a successful full-call sequence.
Deleting a membership key can allow a later successful callback to append the
same account to the vector again. Thus unconditional logical-set uniqueness
cannot simply be assumed after arbitrary authorized code deletions.

The full entry model operates on this shared trie and treats missing or malformed
collection records as panics. Full method refinement still needs to establish
that the modeled serialization, storage write order and panic behavior match the
pinned SDK and binary on all reachable inputs.

## Reviewed entry points and proof obligations

The following is the source review behind the model, **not a list of completed
method proofs**. Argument parsing, account syntax, u64/u128 bounds,
host storage rules, out-of-gas rollback and receipt effects also apply.

| Method | Source checks/effects and properties to formalize |
|---|---|
| `new` | Nonpayable init; empty DAO vector, no OWNER/CODE/METADATA initialization. Owner defaults to current factory, not initializer predecessor. Does not publish default code. |
| `set_owner` | Existing owner only; writes raw UTF-8 OWNER. Authority changes only through this method in coherent storage. |
| `set_default_code_hash` | Owner; raw storage_has_key(hash), not Wasm validation, metadata existence or global-code readiness. Protect exact distinction. |
| `delete_contract` | Owner; default hash must decode and differ; raw deletion; then metadata deletion. Failure at missing METADATA must roll back the earlier deletion. Shared-key aliasing affects DAO membership. Does not delete global code or deployed DAO code. |
| `create` | Payable; concatenate name + '.' + current and parse; default must decode before helper checks; >=0.01 NEAR; raw key must exist. Schedule create, transfer entire deposit, use global code, call `new` with raw decoded args and 40 TGas; append 10 TGas callback; **return original receipt 0**, not callback 1. Registration occurs later. |
| `on_create` | Private, nonpayable; exactly one callback result. Success inserts DAO; failure detaches full-deposit refund and returns false. A successful account receipt can be followed by a failed callback, so caller success does not imply registry inclusion. |
| `update` | Owner or DAO itself; raw membership check; raw target code read. Calls DAO `update` with raw code, zero deposit, zero static gas and weight 1; returns receipt 0. Does not guarantee receiver authorization, migration success or registry change. |
| `get_dao_list` | Reads vector in insertion order; can contain duplicates after raw membership deletion. Missing/corrupt elements panic. |
| `get_number_daos` | Vector length, not necessarily number of distinct accounts in corrupted set. |
| `get_daos` | `from_index + limit` is checked u64 arithmetic (release overflow-checks=true), so arbitrary parsed u64 inputs need not succeed. Out-of-range start otherwise yields an empty range. |
| `get_owner` | Missing OWNER defaults to current; present value must be valid UTF-8 and AccountId or panic. |
| `get_default_code_hash` | Missing or malformed CODE panics; getter does not check referenced raw bytes or metadata. |
| `get_default_version` | METADATA header must exist/decode; default must decode; its metadata entry must exist. Presence of default code alone is insufficient. |
| `store` | Payable owner; input is raw Wasm bytes, not JSON. Hash input, reject existing raw key, write code, schedule global deployment, return hash using env::value_return despite Rust `()`. Deposit check follows writes/scheduling and uses two saturating multiplications: `min(min(byteCost * deltaUsage, u128::MAX) * 11, u128::MAX)`. Failure rolls everything back. Global publication is asynchronous. |
| `get_code` | Raw bytes at supplied hash; absent key panics. Does not independently validate code/hash binding. |
| `store_contract_metadata` | Owner; raw code key must exist; initialize or decode legacy map prefix m, insert metadata, save METADATA header; optionally select default. Metadata describes owner assertions, not proven provenance of code. |
| `delete_contract_metadata` | Owner; header must exist/decode; removes entry by swap removal if present. May remove default metadata, making version getter fail. |
| `get_contracts_metadata` | Header must exist/decode; returns current map vector order, not a sorted map. |

## SDK wrapper distinctions

Many administratively mutating methods take `&self` and write through host
functions. SDK 5.24.1 classifies those signatures as View for wrapper generation,
which omits the attached-deposit guard. They still mutate storage during ordinary
transactions. Do not infer purity from `&self` or apply a blanket nonpayable guard.
A host view-context execution rejects writes separately.

Only `new` and `on_create` among these source signatures have generated deposit
rejection. `create` and `store` are explicitly payable. Private predecessor
checking precedes deposit checking, argument parsing and state loading.
`is_promise_success()` requires exactly one result, ignores Successful bytes,
and aborts for NotReady. Callback provenance must come from the receipt graph,
not just `predecessor == current`.

The low-level `create_contract` helper returns the base receipt despite appending
a callback. Its gas is fixed 40/10 TGas. This differs from linkdrop's weighted
SDK ext callbacks returning the callback receipt. Factory upgrades instead use
zero static gas with unused-gas weight 1. These cases must remain distinct.

## Remaining model and runtime work

1. Complete source-to-model validation of all exported entry semantics, including
   SDK collection serialization, malformed records, header commits and rollback.
2. Extend the existing owner/default, receipt and callback proofs to cover
   remaining branches and resource bounds across all 18 methods.
3. Formulate conditional DAO set coherence and code/hash binding that survive the
   real raw-key behavior; retain counterexamples to stronger unconditional claims.
4. Prove model storage projection and encode/decode round trips without hiding
   UnorderedSet/UnorderedMap vector order or swap removal.
5. Connect the pinned binary to NearVM with exact JSON/raw argument and return
   formats. Weighted calls and global-contract imports are currently absent from
   the VM import table; a failed import resolution is a model gap.
6. Prove conditional chain properties: global-code publication before use,
   callback argument authenticity, refunds/locked storage, pending liabilities,
   administrative trust, and receiver upgrade/migration assumptions.

No deployed-binary refinement, whole-chain safety or liveness is claimed here.
