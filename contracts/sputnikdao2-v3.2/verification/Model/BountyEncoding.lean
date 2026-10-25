import Model.BountyStorage
import NearSdk

namespace SputnikDAO2

abbrev BountyBytes := List UInt8

-- Little-endian integers and their parser come from the shared `NearSdk` library.

def bountyBorshString (account : String) : BountyBytes :=
  NearSdk.Borsh.leBytes 4 account.toUTF8.data.toList.length ++
    account.toUTF8.data.toList

-- StorageKeys is the pinned eight-variant enum in lib.rs, in declaration
-- order. Borsh enum discriminants are single bytes for these variants.
def bountyClaimersKey (account : String) : BountyBytes :=
  5 :: bountyBorshString account

def bountyCountKey (bountyId : Nat) : BountyBytes :=
  6 :: NearSdk.Borsh.leBytes 8 bountyId

-- The other StorageKeys variants have single-byte tags 0,1,2,3,4,7.
def otherDAOPrefixes : List UInt8 := [0, 1, 2, 3, 4, 7]

-- BountyClaim is Borsh-serialized as u64 id, U64 start, U64 deadline, bool.
-- `paidBond` is proof history and has no on-chain byte representation.
def encodeStoredBountyClaim (claim : StoredBountyClaim) : BountyBytes :=
  NearSdk.Borsh.leBytes 8 claim.bountyId ++
    NearSdk.Borsh.leBytes 8 claim.start ++
    NearSdk.Borsh.leBytes 8 claim.deadline ++
    [if claim.completed then 1 else 0]

def encodeStoredBountyClaims (claims : List StoredBountyClaim) : BountyBytes :=
  NearSdk.Borsh.leBytes 4 claims.length ++ claims.flatMap encodeStoredBountyClaim

def encodeBountyCount (count : Nat) : BountyBytes := NearSdk.Borsh.leBytes 4 count

abbrev BountyParser (α : Type) := BountyBytes → Option (α × BountyBytes)

def bountyParseBool : BountyParser Bool
  | [] => none
  | byte :: rest =>
      if byte == 0 then some (false, rest)
      else if byte == 1 then some (true, rest)
      else none

structure PhysicalBountyClaim where
  bountyId : Nat
  start : Nat
  deadline : Nat
  completed : Bool
  deriving Repr, DecidableEq

def physicalBountyClaim (claim : StoredBountyClaim) : PhysicalBountyClaim :=
  ⟨claim.bountyId, claim.start, claim.deadline, claim.completed⟩

def bountyParseClaim : BountyParser PhysicalBountyClaim := fun input => do
  let (bountyId, rest) ← NearSdk.BorshParse.natural 8 input
  let (start, rest) ← NearSdk.BorshParse.natural 8 rest
  let (deadline, rest) ← NearSdk.BorshParse.natural 8 rest
  let (completed, rest) ← bountyParseBool rest
  some (⟨bountyId, start, deadline, completed⟩, rest)

def bountyParseCount (input : BountyBytes) : Option Nat := do
  let (count, rest) ← NearSdk.BorshParse.natural 4 input
  if rest.isEmpty then some count else none

def bountyParseClaimsN : Nat → BountyParser (List PhysicalBountyClaim)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (claim, rest) ← bountyParseClaim input
      let (claims, tail) ← bountyParseClaimsN count rest
      some (claim :: claims, tail)

def bountyParseClaims (input : BountyBytes) :
    Option (List PhysicalBountyClaim) := do
  let (count, rest) ← NearSdk.BorshParse.natural 4 input
  if count * 25 > rest.length then none
  else do
    let (claims, tail) ← bountyParseClaimsN count rest
    if tail.isEmpty then some claims else none

def validStoredBountyClaim (claim : StoredBountyClaim) : Prop :=
  claim.bountyId < 256 ^ 8 ∧
  claim.start < 256 ^ 8 ∧
  claim.deadline < 256 ^ 8

end SputnikDAO2
