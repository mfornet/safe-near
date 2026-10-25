import NearNode.Validator.Doomslug
import NearNode.Validator.Messages

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

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  basic failures
  delayValues failures
  approvals failures
  onePerHeight failures
  chunkWait failures
  let n ← checks.get
  let bad ← failures.get
  IO.println s!"{n} checks, {bad} failures"
  return if bad == 0 then 0 else 1
