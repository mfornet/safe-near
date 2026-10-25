import Lean.Data.Json
import NodeConformance.Runner
import NearNode.Zstd
import NearNode.Primitives
import NearNode.Trie

/-!
`node-conformance-sync [DIR]`: the state sync building blocks against fixtures that
`tools/node-conformance/native-trie/src/bin/state_sync_oracle.rs` writes with nearcore's own `zstd` and
`near-store` (default `near-lean/node/fixtures/state-sync`).

* `zstd.jsonl`: frames of the `zstd` crate over inputs of many shapes and levels (the stream encoder
  nearcore compresses parts with, the bulk one with the content size in the header, one with the
  checksum, several frames and a skippable one). The decoder must give the input back (its length and
  SHA-256, the bytes themselves when short). A frame cut short must be refused, and a flipped bit
  must give an error or other bytes, never the same ones; with a checksum, an error.
* `parts.jsonl`: tries of several shapes; for each part count and index the part nearcore generates
  (as a set of nodes and values), which the Lean walk must regenerate, validate and apply to the
  same references; and parts changed in the ways a peer could (a node removed, repeated, changed or
  added, the parts of another index or count, nothing), each with `Trie::validate_state_part`'s verdict,
  which must be the same.
-/

open Lean Near.Node Near.Node.Conformance Near.Node.Trie

private def lines (path : System.FilePath) : IO (Array Json) := do
  let text ← IO.FS.readFile path
  let mut out := #[]
  for l in text.splitOn "\n" do
    if l.trimAscii.isEmpty then
      continue
    match Json.parse l with
    | .ok j =>
      out := out.push j
    | .error e =>
      throw (IO.userError s!"{path}: {e}")
  pure out

private def bytesOf (j : Json) (k : String) : Except String ByteArray := do
  match ofHex (← j.getObjValAs? String k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

private def hexList (j : Json) (k : String) : Except String (Array ByteArray) := do
  (← (← j.getObjVal? k).getArr?).mapM fun x => do
      match ofHex (← x.getStr?) with
      | some b =>
        pure b
      | none =>
        throw s!"{k} holds a string that is not hex"

private structure Tally where
  checks : Nat := 0
  failures : Array String := #[]

private def Tally.ok (t : Tally) (good : Bool) (what : String) : Tally :=
  { t with
    checks := t.checks + 1, failures := if good then t.failures else t.failures.push what }

private def sorted (xs : Array ByteArray) : Array ByteArray :=
  xs.qsort fun a b => Borsh.compareBytes a b == .lt

/-- A valid frame against its input. -/
private def zstdCase (t : Tally) (row : Json) : IO Tally := do
  let name ← IO.ofExcept (row.getObjValAs? String "name")
  let level ← IO.ofExcept (row.getObjValAs? Int "level")
  let style ← IO.ofExcept (row.getObjValAs? String "style")
  let label := s!"{name} (level {level}, {style})"
  let frame ← IO.ofExcept (bytesOf row "frame")
  let length ← IO.ofExcept (row.getObjValAs? Nat "rawLength")
  let sha ← IO.ofExcept (bytesOf row "rawSha256")
  let mut t := t
  match Zstd.decompress frame (512 * 1048576) with
  | .error e =>
    t := t.ok false s!"{label}: {e}"
  | .ok out =>
    t := t.ok (out.size == length) s!"{label}: {out.size} bytes, want {length}"
    t := t.ok ((CryptoHash.hash out).bytes == sha) s!"{label}: wrong bytes"
    if let .ok raw := bytesOf row "raw" then
      t := t.ok (out == raw) s!"{label}: wrong bytes (short input)"
  -- every proper prefix of a single frame is an error
  if style != "concat" && frame.size > 0 then
    let step := max 1 (frame.size / 24)
    let mut cut := 0
    while cut < frame.size do
      let r := Zstd.decompress (frame.extract 0 cut) (512 * 1048576)
      t := t.ok r.isOk.not s!"{label}: the first {cut} of {frame.size} bytes were accepted"
      cut := cut + step
    -- a flipped bit
    for k in [0:12] do
      let pos := (k * 7919 + 13) % frame.size
      let mut bad := frame
      bad := bad.set! pos (bad.get! pos ^^^ (1 <<< (k % 8)).toUInt8)
      match Zstd.decompress bad (512 * 1048576) with
      | .error _ =>
        pure ()
      | .ok out =>
        -- a flipped bit may change nothing that matters (a ignored flag), but with a checksum it
        -- never changes the bytes
        t :=
          t.ok ((CryptoHash.hash out).bytes == sha || style != "checksum")
            s!"{label}: bit {k} flipped at {pos} gave other bytes"
  pure t

/-- A fixture trie: its entries as a node source. -/
private structure Fixture where
  root : CryptoHash
  src : NodeSource
  memoryUsage : UInt64
  numParts : UInt64

private def fixture (row : Json) : Except String Fixture := do
  let entries ←
    (← (← row.getObjVal? "entries").getArr?).mapM fun e => do
        let k ←
          match ofHex (← (← e.getArrVal? 0).getStr?) with
          | some b =>
            pure b
          | none =>
            throw "key"
        let v ←
          match ofHex (← (← e.getArrVal? 1).getStr?) with
          | some b =>
            pure b
          | none =>
            throw "value"
        pure (k, v)
  let changes ← Trie.fromEntries entries
  let store ← ({} : MemStore).apply changes
  pure
      { root := changes.newRoot, src := store.source,
        memoryUsage := (← row.getObjValAs? Nat "memoryUsage").toUInt64,
        numParts := (← row.getObjValAs? Nat "numParts").toUInt64 }

private def applyMutation (op : String) (k p : Nat) (nodes : Array ByteArray) : Array ByteArray :=
  match op with
  | "remove" => nodes.eraseIdx! k
  | "flip" => nodes.modify k fun b => if b.size == 0 then b else b.set! p (b.get! p ^^^ 1)
  | "repeat" => nodes.push nodes[k]!
  | "reverse" => nodes.reverse
  | "add" =>
    nodes.push
      (ByteArray.mk
        ((List.range 40).toArray.map fun i =>
          -- the bytes of the oracle's `bytes(7, 40)` are not reproduced; any unrelated node is refused
          (i * 37 + 11).toUInt8))
  | "empty" => #[]
  | _ => nodes

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.head?.getD "near-lean/node/fixtures/state-sync"
  let mut t : Tally := {}
  let zrows ← lines (dir / "zstd.jsonl")
  for row in zrows do
    t ← zstdCase t row
  IO.println s!"zstd: {zrows.size} frames"
  let rows ← lines (dir / "parts.jsonl")
  let mut cases : Std.HashMap String Fixture := {}
  let mut parts : Std.HashMap (String × UInt64 × UInt64) (Array ByteArray) := {}
  let mut regenerated := 0
  let mut changed := 0
  for row in rows do
    let name ← IO.ofExcept (row.getObjValAs? String "case")
    if (row.getObjVal? "entries").isOk then
      let f ← IO.ofExcept (fixture row)
      cases := cases.insert name f
      let want ← IO.ofExcept (bytesOf row "root")
      t := t.ok (f.root.bytes == want) s!"{name}: root differs"
      t := t.ok (getNumStateParts f.memoryUsage == some f.numParts) s!"{name}: part count"
      continue
    let some f := cases[name]? | throw (IO.userError s!"{name}: part before its trie")
    let total := (← IO.ofExcept (row.getObjValAs? Nat "total")).toUInt64
    let idx := (← IO.ofExcept (row.getObjValAs? Nat "idx")).toUInt64
    let label := s!"{name} part {idx}/{total}"
    if (row.getObjVal? "mutation").isOk then
      let op ← IO.ofExcept (row.getObjValAs? String "mutation")
      let bi := (← IO.ofExcept (row.getObjValAs? Nat "baseIdx")).toUInt64
      let bt := (← IO.ofExcept (row.getObjValAs? Nat "baseTotal")).toUInt64
      let k ← IO.ofExcept (row.getObjValAs? Nat "k")
      let p ← IO.ofExcept (row.getObjValAs? Nat "p")
      let valid ← IO.ofExcept (row.getObjValAs? Bool "valid")
      let some base := parts[(name, bi, bt)]? | throw (IO.userError s!"{label}: no base part")
      let nodes := applyMutation op k p base
      let verdict := (validatePart f.root idx total nodes).isOk
      t := t.ok (verdict == valid) s!"{label} {op}: Lean says {verdict}, nearcore {valid}"
      changed := changed + 1
      continue
    let nodes ← IO.ofExcept (hexList row "nodes")
    parts := parts.insert (name, idx, total) nodes
    -- the part nearcore generated validates
    t := t.ok (validatePart f.root idx total nodes).isOk s!"{label}: nearcore's part is refused"
    -- the Lean walk generates the same set
    match partNodes f.src f.root idx total with
    | .error e =>
      t := t.ok false s!"{label}: {e}"
    | .ok ours =>
      t :=
        t.ok (sorted ours == sorted nodes)
          s!"{label}: generated {ours.size} nodes, nearcore {nodes.size}"
    -- applying adds the same references
    let want : Array (String × Nat) ←
      IO.ofExcept
          (do
            let adds ← (← row.getObjVal? "additions").getArr?
            adds.mapM fun a => do
                pure (← (← a.getArrVal? 0).getStr?, ← (← a.getArrVal? 1).getNat?))
    match applyPart f.root idx total nodes with
    | .error e =>
      t := t.ok false s!"{label}: {e}"
    | .ok adds =>
      let ours := adds.map fun (h, _, rc) => (toHex h.bytes, rc.toNat)
      t :=
        t.ok (ours.qsort (fun a b => a.1 < b.1) == want.qsort (fun a b => a.1 < b.1))
          s!"{label}: references differ"
    regenerated := regenerated + 1
  IO.println
      s!"state parts: {regenerated} parts generated, validated and applied; {changed} changed parts judged"
  IO.println s!"{t.checks} checks, {t.failures.size} failures"
  for f in t.failures.extract 0 20 do
    IO.println s!"  FAIL {f}"
  return if t.failures.isEmpty then 0 else 1
