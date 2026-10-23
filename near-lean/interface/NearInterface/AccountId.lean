import NearInterface.Gas

namespace Wasm.Near

/-- V2 account syntax: lowercase ASCII letters/digits separated by single
`-`, `_`, or `.` characters, with alphanumeric endpoints. -/
def accountIdFormat : Bool → List UInt8 → Bool
  | previousSeparator, [] => !previousSeparator
  | previousSeparator, byte :: rest =>
    let n := byte.toNat
    if (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) then accountIdFormat false rest
    else if (n == 45 || n == 95 || n == 46) && !previousSeparator then accountIdFormat true rest
    else false

def validAccountIdBytes (bytes : List UInt8) : Bool :=
  2 ≤ bytes.length && bytes.length ≤ 64 && accountIdFormat true bytes

/-- Account type affects transfer fees even when the receiver already exists. -/
inductive AccountKind where
  | named | nearImplicit | ethImplicit | nearDeterministic
  deriving BEq, DecidableEq, Repr

def lowerHexByte (byte : UInt8) : Bool :=
  let n := byte.toNat
  (48 ≤ n && n ≤ 57) || (97 ≤ n && n ≤ 102)

/-- Pinned near-account-id classification; the two-character prefixes are ASCII. -/
def accountKind (bytes : List UInt8) : AccountKind :=
  if bytes.length == 42 && bytes.take 2 == [48, 120] && (bytes.drop 2).all lowerHexByte then .ethImplicit
  else if bytes.length == 64 && bytes.all lowerHexByte then .nearImplicit
  else if bytes.length == 42 && bytes.take 2 == [48, 115] && (bytes.drop 2).all lowerHexByte then .nearDeterministic
  else .named

def accountIsImplicit (ethEnabled : Bool) (bytes : List UInt8) : Bool :=
  match accountKind bytes with
  | .nearImplicit => true
  | .ethImplicit | .nearDeterministic => ethEnabled
  | .named => false

/-- ETH creation installs protocol code; deterministic creation needs additional
runtime context. Existing receivers can still accept ordinary transfers. -/
def unsupportedImplicitCreation (ethEnabled : Bool) (bytes : List UInt8) : Bool :=
  match accountKind bytes with
  | .ethImplicit | .nearDeterministic => ethEnabled
  | _ => false

/-- Pinned transfer_send_fee/transfer_exec_fee: NEAR implicit accounts require
creation and a full-access key, enabled ETH and deterministic accounts creation. -/
def transferFees (fees : ActionFees) (ethEnabled : Bool) (receiver : List UInt8) : Fee :=
  let extra := match accountKind receiver with
    | .nearImplicit => fees.createAccount.add fees.addFullAccessKey
    | .ethImplicit => if ethEnabled then fees.createAccount else {}
    | .nearDeterministic => fees.createAccount
    | .named => {}
  fees.transfer.add extra

end Wasm.Near
