import NearVM.Run
import Wasm.Wat

/-! Execute actual Wasm storage hosts against a canonical one-leaf trie. These
checks cover the external-call ordering, including failures that final contract
storage alone cannot distinguish. Native trie encodings/cache behavior are also
checked independently by tools/chain-conformance/test_trie_updates.py. -/
namespace TrieStorage
open Wasm Wasm.Near

private def account : List UInt8 := "storage.near".toUTF8.toList
private def key : List UInt8 := [107]
private def old : List UInt8 := [42, 43]
private def rawKey := _root_.Near.TrieOverlay.contractKey account key

private def context (trie : _root_.Near.TrieOverlay.State) : VMContext :=
  { currentAccountId := account, signerAccountId := account, signerAccountPk := []
    predecessorAccountId := account, input := [], prepaidGas := 10 ^ 14
    storageUsage := 10000, storageAccounting := some trie }

private def cost (o : VMOutcome) (name : String) : Nat :=
  ((o.gasProfile.ext.find? (·.1 == name)).map (·.2)).getD 0

private def cache (o : VMOutcome) : List (List UInt8) :=
  (o.storageAccounting.map (·.accounting.seen)).getD []

private def pending (o : VMOutcome) : _root_.Near.TrieOverlay.Changes :=
  (o.storageAccounting.map (·.prospective)).getD []

private def code : IO Module := do
  let text := "(module\n" ++
    "(import \"env\" \"storage_write\" (func $w (param i64 i64 i64 i64 i64) (result i64)))\n" ++
    "(import \"env\" \"storage_remove\" (func $d (param i64 i64 i64) (result i64)))\n" ++
    "(import \"env\" \"storage_read\" (func $r (param i64 i64 i64) (result i64)))\n" ++
    "(import \"env\" \"storage_has_key\" (func $h (param i64 i64) (result i64)))\n" ++
    "(import \"env\" \"panic\" (func $p))\n" ++
    "(memory 1) (data (i32.const 0) \"k\") (data (i32.const 8) \"v\")\n" ++
    "(func $write i64.const 1 i64.const 0 i64.const 1 i64.const 8 i64.const 0 call $w drop)\n" ++
    "(func (export \"write\") call $write)\n" ++
    "(func (export \"twice\") call $write call $write)\n" ++
    "(func (export \"panic\") call $write call $p)\n" ++
    "(func (export \"remove\") i64.const 1 i64.const 0 i64.const 0 call $d drop)\n" ++
    "(func (export \"read\") i64.const 1 i64.const 0 i64.const 0 call $r drop)\n" ++
    "(func (export \"has\") i64.const 1 i64.const 0 call $h drop))"
  match ← Wat.compile text with
  | .ok code => pure code
  | .error error => throw (IO.userError s!"trie storage fixture: {error}")

def check (cfg : RuntimeConfig) (check : String → Bool → IO Unit) : IO Unit := do
  let code ← code
  let trie ← match _root_.Near.TrieOverlay.start [(rawKey, old)] with
    | .ok trie => pure trie
    | .error message => throw (IO.userError message)
  let storage := [(key, old)]
  let call := fun method ctx => run cfg code 0 method ctx storage
  let disk := cfg.wasm.extCosts.cost "touching_trie_node"
  let mem := cfg.wasm.extCosts.cost "read_cached_trie_node"
  for method in ["write", "remove"] do
    let o := call method (context trie)
    check s!"trie {method}: leaf and value charged once"
      (o.succeeded && cost o "touching_trie_node" == 2 * disk &&
        cost o "read_cached_trie_node" == 0 && (cache o).length == 2)
  let read := call "read" (context trie)
  check "flat read warms value hash without trie gas"
    (read.succeeded && cost read "touching_trie_node" == 0 &&
      cost read "read_cached_trie_node" == 0 && cache read == [_root_.Near.Sha256.hash old])
  if let some warmed := read.storageAccounting then
    let write := call "write" (context warmed)
    check "later VM call retains the read's free value-cache access"
      (write.succeeded && cost write "touching_trie_node" == disk &&
        cost write "read_cached_trie_node" == mem)
  else check "read returned shared trie" false
  let read := call "read" { context trie with storageReadsFromTrie := true }
  check "trie-mode read charges leaf but fetches value for free"
    (read.succeeded && cost read "touching_trie_node" == disk && (cache read).length == 2)
  let has := call "has" (context trie)
  check "flat has-key neither dereferences nor warms cache" (has.succeeded && (cache has).isEmpty)
  let has := call "has" { context trie with storageReadsFromTrie := true }
  check "trie-mode has-key warms only leaf"
    (has.succeeded && cost has "touching_trie_node" == disk && (cache has).length == 1)
  let twice := call "twice" (context trie)
  check "prospective write bypasses trie on the next host call"
    (twice.succeeded && cost twice "touching_trie_node" == 2 * disk &&
      cost twice "read_cached_trie_node" == 0)
  let failed := call "panic" (context trie)
  check "VM panic retains cache and prospective writes for receipt rollback"
    (failed.aborted.isSome && failed.storage == storage && (cache failed).length == 2 &&
      pending failed == [(rawKey, some [118])])
  if let some after := failed.storageAccounting then
    match _root_.Near.TrieOverlay.step account .rollback after with
    | .ok (rolled, _) =>
      check "receipt rollback restores old value and retains warmed cache"
        (rolled.view == [(rawKey, old)] && rolled.accounting.seen == cache failed)
    | .error _ => check "receipt rollback" false
  let mismatch := run cfg code 0 "read" (context trie) [(key, [99, 99])]
  check "inconsistent external bytes are an execution issue" (mismatch.issue?.isSome)
  let missing := run cfg code 0 "has" (context trie) []
  check "inconsistent external presence is an execution issue" (missing.issue?.isSome)
  -- Zero unrelated fees isolate exactly where exhaustion occurs.
  let limited := { cfg with wasm := { cfg.wasm with regularOpCost := 0, extCosts := {
    lookup := fun name => if name == "storage_write_evicted_byte" ||
      name == "storage_remove_ret_value_byte" || name == "storage_read_value_byte" then 100
      else if name == "touching_trie_node" then 10 else 0 } } }
  for method in ["write", "remove"] do
    let o := run limited code 0 method { context trie with prepaidGas := 50 } storage
    check s!"trie {method}: byte exhaustion warms leaf but not value or updates"
      (o.aborted == some (.hostError .gasExceeded) && (cache o).length == 1 &&
        cost o "touching_trie_node" == 0 && (pending o).isEmpty)
  let o := run limited code 0 "read" { context trie with prepaidGas := 50 } storage
  check "flat read byte exhaustion does not fetch value"
    (o.aborted == some (.hostError .gasExceeded) && (cache o).isEmpty)
  let ttnLimited := { limited with wasm := { limited.wasm with extCosts := {
    lookup := fun name => if name == "touching_trie_node" then 10 else 0 } } }
  for method in ["write", "remove"] do
    let o := run ttnLimited code 0 method { context trie with prepaidGas := 5 } storage
    check s!"trie {method}: node exhaustion retains both hashes and native update ordering"
      (o.aborted == some (.hostError .gasExceeded) && (cache o).length == 2 &&
        o.storage == storage && pending o == (if method == "remove" then [(rawKey, none)] else []))
  let oversized := List.replicate 4001 (42 : UInt8)
  let inMemory := trie.set rawKey oversized
  let o := run cfg code 0 "read" (context inMemory) [(key, oversized)]
  check "large overlay read charges overhead before register output"
    (o.succeeded && (cache o).isEmpty && cost o "storage_large_read_overhead_base" ==
      cfg.wasm.extCosts.cost "storage_large_read_overhead_base" &&
      cost o "storage_large_read_overhead_byte" == 4001 * cfg.wasm.extCosts.cost "storage_large_read_overhead_byte")
  -- `per_receipt_storage_proof_size_limit`, against a trusted proof size: here 1000 bytes per
  -- trie node or value the call has seen, with a 1500-byte limit.
  check "v86 limits a receipt's storage proof to 4 MB" (cfg.wasm.limits.perReceiptStorageProofSizeLimit == 4_000_000)
  check "proof limits print as nearcore's ByteSize"
    (byteSizeString 4_000_000 == "4.0 MB" && byteSizeString 1500 == "1.5 KB" && byteSizeString 999 == "999 B")
  let small := { cfg with wasm := { cfg.wasm with limits := { cfg.wasm.limits with
    perReceiptStorageProofSizeLimit := 1500 } } }
  let sized := { context trie with storageProofSize := some fun t => 1000 * t.accounting.seen.length }
  for method in ["write", "remove"] do
    let o := run small code 0 method sized storage
    check s!"trie {method}: a proof past the per-receipt limit fails with RecordedStorageExceeded"
      (o.aborted == some (.hostError (.recordedStorageExceeded 1500)) && (cache o).length == 2 &&
        ((o.aborted.map (·.message)) == some
          "Size of the recorded trie storage proof has exceeded the allowed limit (1.5 KB)"))
  let read := run small code 0 "read" sized storage
  check "a flat read within the proof limit succeeds" (read.succeeded && (cache read).length == 1)
  -- nearcore observes a read's proof after it dereferences the value: the value's bytes count.
  let base := { context trie with storageProofSize := some fun t => 1000 + 1000 * t.accounting.seen.length }
  let o := run small code 0 "read" base storage
  check "a read whose value takes the proof past the limit fails with RecordedStorageExceeded"
    (o.aborted == some (.hostError (.recordedStorageExceeded 1500)) && (cache o).length == 1)
  let write := run cfg code 0 "write" sized storage
  check "the same write within the v86 limit succeeds" write.succeeded
  let unchecked := run small code 0 "write" (context trie) storage
  check "without a proof size input the limit is not checked" unchecked.succeeded
end TrieStorage
