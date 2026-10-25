import NearNode.Chain.ApplyChunk
import NearNode.Validator.Doomslug
import NearNode.Validator.Messages
import NearNode.Validator.Pool
import NearNode.Store.Trie

/-!
`node-validator-tests`: the validator's state machines, with the unit tests of `doomslug.rs` ported
(`test_endorsements_and_skips_basic`, `test_get_delay_reacts_to_config_updates`,
`test_doomslug_approvals`, `test_doomslug_one_approval_per_target_height`), checked against the same
numbers.
-/

open Near.Node Near.Node.Validator Near.Node.Chain Near.Node.Network

private initialize checks : IO.Ref Nat ←
  IO.mkRef 0

private def check (failures : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  checks.modify (· + 1)
  if !ok then
    IO.eprintln s!"FAIL {name}"
    failures.modify (· + 1)

/-- A signer whose key derives from `name`. -/
private def signerOf (name : String) : Signer :=
  let seed := CryptoHash.hash name.toUTF8
  match NodeKey.ofSeed? seed.bytes with
  | some key => ⟨⟨name⟩, key, seed.bytes⟩
  | none => panic! "key"

private def hashOf (n : Nat) : CryptoHash :=
  CryptoHash.hash (ByteArray.mk #[n.toUInt8])

private def stakeOf (name : String) (this next : Nat) : ApprovalStake :=
  { accountId := ⟨name⟩, publicKey := (signerOf name).publicKey, stakeThisEpoch := ⟨this⟩,
    stakeNextEpoch := ⟨next⟩ }

private def delays : Delays :=
  { endorsement := 400, base := 1000, cap := 3000 }

/-- The decoder that lets a validator learn code a contract deploys from its own memory: the bytes it does not
know travel in the text of an issue and come out unchanged; the bytes it knows are answered from the catalogue. -/
private def learnedCode (f : IO.Ref Nat) : IO Unit := do
  let all : List UInt8 := (List.range 256).map (·.toUInt8)
  let text := Near.Node.Apply.hexOfBytes all
  check f "hex text of all byte values" (text.length == 512 && text.take 6 == "000102")
  check f "hex round trip" ((Near.Node.Apply.bytesOfHexPrefix text).toList == all)
  check f "hex stops at the first other character"
      ((Near.Node.Apply.bytesOfHexPrefix "00ff zz01").toList == [0, 255])
  let blob : List UInt8 := [0, 97, 115, 109, 1, 0, 0, 0, 255]
  let unknown := Near.Node.Apply.learningCodeOf [] blob
  let message := (unknown.decodeIssue.map (·.message)).getD ""
  check f "unknown bytes carry an issue" unknown.decodeIssue.isSome
  check f "the issue hands the bytes back"
      ((Near.Node.Apply.undeclaredBytes? message).map (·.toList) == some blob)
  check f "an ordinary issue hands nothing back"
      ((Near.Node.Apply.undeclaredBytes? "Interpreter error: out of fuel").isNone)
  let entry : ChainReplay.LoadedCode :=
    { bytes := blob, code := { module := default, size := blob.length, hash := "known" } }
  let known := Near.Node.Apply.learningCodeOf [entry] blob
  check f "known bytes are answered from the catalogue"
      (known.decodeIssue.isNone && known.hash == "known")

/-- The reference count changes that garbage collection reads back from `DBCol::TrieChanges`. -/
private def trieChangesRecord (f : IO.Ref Nat) : IO Unit := do
  let c : Near.Node.Trie.TrieChanges :=
    { oldRoot := hashOf 1, newRoot := hashOf 2,
      insertions := #[⟨hashOf 1, ByteArray.mk #[1, 2, 3], 3⟩, ⟨hashOf 3, ByteArray.empty, 1⟩],
      deletions := #[⟨hashOf 2, 5⟩, ⟨hashOf 1, 70000⟩] }
  let bytes := Near.Node.Store.changesBytes c
  check f "the changes take 8 + 36 per reference bytes" (bytes.size == 8 + 36 * 4)
  match Near.Node.Store.changesOfBytes? bytes with
  | some (ins, del) =>
    check f "insertions read back" (ins == #[(hashOf 1, 3), (hashOf 3, 1)])
    check f "deletions read back" (del == #[(hashOf 2, 5), (hashOf 1, 70000)])
  | none =>
    check f "the changes read back" false
  check f "a cut record is refused"
      ((Near.Node.Store.changesOfBytes? (bytes.extract 0 (bytes.size - 1))).isNone)
  check f "a record with a tail is refused"
      ((Near.Node.Store.changesOfBytes? (bytes.push 0)).isNone)
  check f "the empty record"
      ((Near.Node.Store.changesOfBytes?
          (Near.Node.Store.changesBytes
            { oldRoot := hashOf 1, newRoot := hashOf 1, insertions := #[],
              deletions := #[] })).isSome)
  -- taking back a deletion is a negative reference on the node of the shard
  let ops := Near.Node.Store.deleteOpsOfRefs (ByteArray.mk #[9]) #[(hashOf 2, 5)]
  check f "deletions are negative references"
      (match ops[0]? with
      | some (Near.Node.Store.Op.rcAdd Near.Node.Store.Col.state _ _ n) => n == -5
      | _ => false)

/-- `test_endorsements_and_skips_basic`. -/
private def basic (f : IO.Ref Nat) : IO Unit := do
  let signer := some (signerOf "test")
  let mut now := 0
  let mut ds := Doomslug.new now 0 delays
  let step (ds : Doomslug) (now : Nat) : Doomslug × Array Approval := ds.processTimer now signer
  -- a new tip must produce an endorsement
  ds := ds.setTip (hashOf 1) 1 1 now
  now := now + 399
  let (d, a) := step ds now
  ds := d
  check f "no approval before the endorsement delay" a.isEmpty
  now := now + 1
  let (d, a) := step ds now
  ds := d
  check f "endorsement"
      (a[0]?.map (·.inner) == some (.endorsement (hashOf 1)) &&
        a[0]?.map (·.targetHeight) == some 2)
  -- same tip, no approval
  let (d, a) := step ds now
  ds := d
  check f "same tip" a.isEmpty
  now := now + 599
  let (d, a) := step ds now
  ds := d
  check f "before the skip" a.isEmpty
  now := now + 1
  let (d, a) := step ds now
  ds := d
  check f "skip of 1"
      (a[0]?.map (·.inner) == some (.skip 1) && a[0]?.map (·.targetHeight) == some 3)
  -- not processing a block at height 2 gives no approval
  ds := ds.setTip (hashOf 2) 2 0 now
  now := now + 400
  let (d, a) := step ds now
  ds := d
  check f "no approval at the new tip 2" a.isEmpty
  now := now + 600
  ds := ds.setTip (hashOf 3) 3 0 now
  now := now + 400
  let (d, a) := step ds now
  ds := d
  check f "endorsement of 3"
      (a[0]?.map (·.inner) == some (.endorsement (hashOf 3)) &&
        a[0]?.map (·.targetHeight) == some 4)
  now := now + 600
  now := now + 199
  let (d, a) := step ds now
  ds := d
  check f "before the skip of 3" a.isEmpty
  now := now + 1
  let (d, a) := step ds now
  ds := d
  check f "skip of 3" (a.size == 1 && a[0]!.inner == .skip 3 && a[0]!.targetHeight == 5)
  now := now + 800
  now := now + 499
  let (d, a) := step ds now
  ds := d
  check f "before the skip to 6" a.isEmpty
  now := now + 1
  let (d, a) := step ds now
  ds := d
  check f "skip to 6"
      (a[0]?.map (·.inner) == some (.skip 3) && a[0]?.map (·.targetHeight) == some 6)
  now := now + 500
  now := now + 899
  let (d, a) := step ds now
  ds := d
  check f "before the skip to 7" a.isEmpty
  now := now + 1
  let (d, a) := step ds now
  ds := d
  check f "skip to 7"
      (a[0]?.map (·.inner) == some (.skip 3) && a[0]?.map (·.targetHeight) == some 7)
  now := now + 100
  -- a block at 5 with finality on the previous block: no approval
  ds := ds.setTip (hashOf 5) 5 4 now
  now := now + 400
  let (d, a) := step ds now
  ds := d
  check f "no approval at tip 5" a.isEmpty
  -- skipping a whole bunch of heights
  now := now + 100000
  let (d, a) := step ds now
  ds := d
  check f "many skips" (a.size > 10)
  now := now + 17
  ds := ds.setTip (hashOf 6) 6 4 now
  now := now + 400
  let (d, a) := step ds now
  ds := d
  check f "no approval at tip 6" a.isEmpty
  now := now + 699
  let (d, a) := step ds now
  ds := d
  check f "before the skip to 8" a.isEmpty
  now := now + 1
  let (_, a) := step ds now
  check f "skip to 8"
      (a[0]?.map (·.inner) == some (.skip 6) && a[0]?.map (·.targetHeight) == some 8)

/-- `test_get_delay_reacts_to_config_updates`, the values. -/
private def delayValues (f : IO.Ref Nat) : IO Unit := do
  let d : Delays := { endorsement := 400, base := 1000, cap := 3000 }
  check f "delay 5" (d.delay 5 == 1300)
  check f "delay 50" (d.delay 50 == 3000)
  let d : Delays :=
    { d with
      base := 2000, cap := 5000 }
  check f "updated delay 5" (d.delay 5 == 2600)
  check f "updated delay 50" (d.delay 50 == 5000)
  check f "delay below 2" (d.delay 0 == 2000 && d.delay 2 == 2000)

/-- `test_doomslug_approvals`. -/
private def approvals (f : IO.Ref Nat) : IO Unit := do
  let names := #["test1", "test2", "test3", "test4"]
  let stakes :=
    #[stakeOf "test1" 2 0, stakeOf "test2" 1 0, stakeOf "test3" 3 0, stakeOf "test4" 1 0]
  let signers := names.map signerOf
  let mut now := 0
  let mut ds := Doomslug.new now 0 { endorsement := 400, base := 1000, cap := 3000 }
  let mut readiness := fun (ds : Doomslug) (who : Nat) (parent : Nat) (target : Nat) (now : Nat) =>
    ds.onApprovalInternal
      (newApproval signers[who]! (hashOf parent) parent.toUInt64 target.toUInt64) stakes now
  let expect (name : String) (r : Readiness) (want : Readiness) : IO Unit :=
    check f name (r == want)
  -- the total stake is 7, so the threshold is 5
  let (d, r) := readiness ds 0 1 2 now
  ds := d
  expect "test1, 2" r .notReady
  let (d, r) := readiness ds 2 1 4 now
  ds := d
  expect "test3, 4" r .notReady
  let (d, r) := readiness ds 3 1 4 now
  ds := d
  expect "test4, 4" r .notReady
  now := now + 100
  let (d, r) := readiness ds 3 1 4 now
  ds := d
  expect "test4, 4 again" r .notReady
  let (d, r) := readiness ds 1 1 4 now
  ds := d
  expect "test2, 4" r (.readySince now)
  let (d, r) := readiness ds 0 1 4 now
  ds := d
  expect "test1, 4" r (.readySince now)
  let (d, r) := readiness ds 3 1 2 now
  ds := d
  expect "test4, 2" r .notReady
  now := now + 200
  let (d, r) := readiness ds 2 1 2 now
  ds := d
  expect "test3, 2" r (.readySince now)
  let (_, r) := readiness ds 1 2 4 now
  expect "a different parent" r .notReady
  readiness := readiness

/-- `test_doomslug_one_approval_per_target_height`. -/
private def onePerHeight (f : IO.Ref Nat) : IO Unit := do
  let stakes :=
    #[stakeOf "test1" 2 0, stakeOf "test2" 1 2, stakeOf "test3" 3 3, stakeOf "test4" 2 2]
  let signers := #["test1", "test2", "test3", "test4"].map signerOf
  let a (s h parent : Nat) := newApproval signers[s]! (hashOf parent) parent.toUInt64 h.toUInt64
  let mut h : AtHeight := {}
  let amounts (h : AtHeight) (inner : ApprovalInner) : Option (Nat × Nat) :=
    (h.tracker? inner).map fun t => (t.approvedThis, t.approvedNext)
  let skip1 := ApprovalInner.skip 1
  h := (h.process (a 0 4 1) stakes 0).1
  check f "first" (amounts h skip1 == some (2, 0))
  h := (h.process (a 0 4 1) stakes 0).1
  check f "the same approval twice" (amounts h skip1 == some (2, 0))
  h := (h.process (a 1 4 1) stakes 0).1
  h := (h.process (a 2 4 1) stakes 0).1
  check f "three approvals" (amounts h skip1 == some (6, 5))
  h := (h.process (a 0 4 3) stakes 0).1
  check f "one moved away" (amounts h skip1 == some (4, 5))
  h := (h.process (a 1 4 3) stakes 0).1
  check f "two moved away" (amounts h skip1 == some (3, 3))
  h := (h.process (a 2 4 3) stakes 0).1
  check f "the old tracker is gone" ((h.tracker? skip1).isNone)
  let endorse3 := ApprovalInner.endorsement (hashOf 3)
  check f "the new tracker" (amounts h endorse3 == some (6, 5))
  h := (h.process (a 2 4 3) stakes 0).1
  check f "the same approval again" (amounts h endorse3 == some (6, 5))

/-- Readiness with the chunks missing: the wait is a third of `T`. -/
private def chunkWait (f : IO.Ref Nat) : IO Unit := do
  let stakes := #[stakeOf "a" 1 0, stakeOf "b" 1 0]
  let sa := signerOf "a"
  let sb := signerOf "b"
  let mut ds := Doomslug.new 0 0 { endorsement := 400, base := 1000, cap := 3000 }
  ds := ds.setTip (hashOf 1) 1 0 0
  ds := (ds.onApproval (newApproval sa (hashOf 1) 1 2) stakes 10)
  check f "one of two is not enough" (!(ds.readyToProduce 2 .notReady 10).2)
  ds := (ds.onApproval (newApproval sb (hashOf 1) 1 2) stakes 20)
  check f "ready with the chunks" (ds.readyToProduce 2 (.ready 20) 20).2
  -- without chunks, T(2 - 0) = 1000 so a third of it is 333 ms after the threshold
  check f "waiting for the chunks" (!(ds.readyToProduce 2 .notReady 20).2)
  check f "waited long enough" (ds.readyToProduce 2 .notReady 354).2
  check f "not at the limit" (!(ds.readyToProduce 2 .notReady 353).2)
  check f "another height has no tracker" (!(ds.readyToProduce 3 (.ready 0) 400).2)
  -- the tip moves on: old heights are dropped, and approvals below the tip are ignored
  ds := ds.setTip (hashOf 9) 100 0 500
  check f "old trackers are gone" (ds.trackers[(2 : UInt64)]?).isNone
  ds := ds.onApproval (newApproval sa (hashOf 1) 1 2) stakes 500
  check f "an approval below the tip is ignored" (ds.trackers[(2 : UInt64)]?).isNone
  -- the largest target height only grows
  let mut ds2 := Doomslug.new 0 5 delays
  ds2 := ds2.setTip (hashOf 2) 2 0 0
  let (_, out) := ds2.processTimer 400 (some sa)
  check f "no endorsement for a height already approved" out.isEmpty

/-! ### The transaction pool (`chain/pool` tests) -/

private def keyOfIndex (i : Nat) : PublicKey :=
  .ed25519 (CryptoHash.hash (ByteArray.mk #[i.toUInt8])).bytes

private def txOf (signer : String) (key : Nat) (nonce : Nat) (strict : Bool := false) :
    SignedTransaction :=
  if strict then
    ⟨.v1
        { signerId := ⟨signer⟩, publicKey := keyOfIndex key, nonce := .nonce nonce.toUInt64,
          receiverId := ⟨"other"⟩, blockHash := CryptoHash.zero, actions := #[],
          nonceMode := .strict },
      default⟩
  else
    ⟨.v0
        { signerId := ⟨signer⟩, publicKey := keyOfIndex key, nonce := nonce.toUInt64,
          receiverId := ⟨"other"⟩, blockHash := CryptoHash.zero, actions := #[] },
      default⟩

private def noncesOf (ts : Array SignedTransaction) : List (String × Nat) :=
  ts.toList.map fun t => (t.transaction.signerId.val, t.transaction.nonceValue.toNat)

private def poolTests (f : IO.Ref Nat) : IO Unit := do
  -- insertion: duplicates are refused, the size limit is enforced, removal frees the space
  let a1 := txOf "alice" 0 1
  let a2 := txOf "alice" 0 2
  let b1 := txOf "bob" 1 1
  let (p, r) := ({ limit := none } : Pool).insert a1
  check f "insert" (r == .success && p.count == 1)
  let (p, r) := p.insert a1
  check f "duplicate" (r == .duplicate && p.count == 1)
  let (p, _) := p.insert a2
  let (p, _) := p.insert b1
  check f "three transactions" (p.count == 3 && p.size == a1.wireSize + a2.wireSize + b1.wireSize)
  let (_, full) := ({ limit := some (a1.wireSize + 1) } : Pool).insert a1 |>.1.insert a2
  check f "no space left" (full == .noSpaceLeft)
  let p' := p.remove #[a1, b1]
  check f "remove" (p'.count == 1 && p'.size == a2.wireSize && p'.groups.size == 1)
  check f "removing what is not there changes nothing" ((p'.remove #[b1]).count == 1)
  -- the same signer with two keys is two groups; the same key with a gas key index is another
  let k1 := txOf "alice" 5 1
  check f "group per key"
      (p.groupKey a1 == p.groupKey a2 && p.groupKey a1 != p.groupKey k1 &&
        p.groupKey a1 != p.groupKey b1)
  -- prepare: one transaction from each group in turn; nonces within a group in order
  let mut q : Pool := { limit := none }
  for t in
    #[txOf "alice" 0 3, txOf "alice" 0 1, txOf "alice" 0 2, txOf "bob" 1 2, txOf "bob" 1 1,
      txOf "carol" 2 1] do
    q := (q.insert t).1
  let admitAll (n : Nat) (_ : SignedTransaction) : Except String (Nat × Nat) := .ok (n + 1, 10)
  let prepared :=
    q.prepare 0 1000000 1000000 SignedTransaction.wireSize (fun _ _ => none) (fun _ => true)
      admitAll
  check f "all prepared" (prepared.txs.size == 6 && prepared.limit == .noMoreTxsInPool)
  let nonces := noncesOf prepared.txs
  check f "per group nonces ascend"
      (["alice", "bob", "carol"].all fun a =>
        ((nonces.filter (·.1 == a)).map (·.2)) ==
          (List.range ((nonces.filter (·.1 == a)).length)).map (· + 1))
  -- round robin: no group yields twice before every group yielded once
  check f "round robin" ((((nonces.take 3).map (·.1)).eraseDups).length == 3)
  check f "prepared stay in the pool" (prepared.pool.count == 6)
  -- the gas limit
  let g :=
    q.prepare 0 15 1000000 SignedTransaction.wireSize (fun _ _ => none) (fun _ => true) admitAll
  check f "gas limit" (g.txs.size == 2 && g.limit == .gas && g.pool.count == 6)
  -- the size limit
  let one := a1.wireSize
  let sz :=
    q.prepare 0 1000000 (2 * one + 1) SignedTransaction.wireSize (fun _ _ => none) (fun _ => true)
      admitAll
  check f "size limit" (sz.txs.size == 2 && sz.limit == .size)
  -- invalid transactions are taken out of the pool and not returned
  let rejectBob (n : Nat) (t : SignedTransaction) : Except String (Nat × Nat) :=
    if t.transaction.signerId.val == "bob" then .error "bob is broke" else .ok (n, 1)
  let rj :=
    q.prepare 0 1000000 1000000 SignedTransaction.wireSize (fun _ _ => none) (fun _ => true)
      rejectBob
  check f "rejected transactions" (rj.txs.size == 4 && rj.rejected.size == 2 && rj.pool.count == 4)
  -- strict nonces: a gap leaves the transaction in the pool; an expired one is dropped
  let mut s : Pool := { limit := none }
  s := (s.insert (txOf "dave" 3 5 (strict := true))).1
  let gap :=
    s.prepare 0 1000000 1000000 SignedTransaction.wireSize (fun _ _ => some 2) (fun _ => true)
      admitAll
  check f "nonce gap waits" (gap.txs.isEmpty && gap.pool.count == 1)
  let expired :=
    s.prepare 0 1000000 1000000 SignedTransaction.wireSize (fun _ _ => some 2) (fun _ => false)
      admitAll
  check f "expired gap is dropped" (expired.txs.isEmpty && expired.pool.count == 0)
  let fits :=
    s.prepare 0 1000000 1000000 SignedTransaction.wireSize (fun _ _ => some 4) (fun _ => true)
      admitAll
  check f "no gap" (fits.txs.size == 1)
  -- the iterator continues after the last used key
  let mut r2 : Pool := { limit := none }
  for t in #[txOf "a" 0 1, txOf "b" 1 1, txOf "c" 2 1] do
    r2 := (r2.insert t).1
  let first :=
    r2.prepare 0 1 1000000 SignedTransaction.wireSize (fun _ _ => none) (fun _ => true) admitAll
  let second :=
    first.pool.prepare 0 1 1000000 SignedTransaction.wireSize (fun _ _ => none) (fun _ => true)
      admitAll
  check f "the next chunk starts after the last group used"
      (first.txs.size == 1 && second.txs.size == 1 && first.txs[0]! != second.txs[0]!)

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  learnedCode failures
  trieChangesRecord failures
  basic failures
  delayValues failures
  approvals failures
  onePerHeight failures
  chunkWait failures
  poolTests failures
  let n ← checks.get
  let bad ← failures.get
  IO.println s!"{n} checks, {bad} failures"
  return if bad == 0 then 0 else 1
