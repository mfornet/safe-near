import Std

/-! Source-level model of near-linkdrop at 9a6bb316. Identifiers are abstract
validated identifiers; JSON, Borsh, gas, and runtime action execution are separate
refinement obligations. Amounts use Nat with explicit u128 representation bounds. -/
namespace Linkdrop

abbrev Key := Nat
abbrev Account := String

def maxAmount : Nat := 2 ^ 128 - 1

def keyAllowance : Nat := 10 ^ 24

def callbackGas : Nat := 13 * 10 ^ 12

/-- SDK ext defaults to weight 1, adding a share of unused gas to static gas. -/
def callbackWeight : Nat := 1

structure LimitedKey where
  key : Key
  allowance : Nat
  receiver : Account
  methods : String
  deriving DecidableEq, Repr

structure Options where
  fullKeys : Option (List Key) := none
  limitedKeys : Option (List LimitedKey) := none
  bytes : Option (List UInt8) := none
  base64Bytes : Option (List UInt8) := none
  globalHash : Option (List UInt8) := none
  globalAccount : Option Account := none
  deriving DecidableEq, Repr

def Options.deployments (o : Options) : Nat :=
  o.bytes.isSome.toNat + o.base64Bytes.isSome.toNat +
    o.globalHash.isSome.toNat + o.globalAccount.isSome.toNat

-- Some [] counts as an option, exactly as in the source.
def Options.present (o : Options) : Bool :=
  o.fullKeys.isSome || o.limitedKeys.isSome || o.bytes.isSome ||
    o.base64Bytes.isSome || o.globalHash.isSome || o.globalAccount.isSome

inductive Action where
  | create
  | transfer (amount : Nat)
  | fullKey (key : Key)
  -- None means Unlimited; the source interprets zero allowance this way.
  | limitedKey (key : Key) (allowance : Option Nat) (receiver : Account) (methods : String)
  | deleteKey (key : Key)
  | deploy (bytes : List UInt8)
  | globalHash (hash : List UInt8)
  | globalAccount (account : Account)
  | onCreated (predecessor : Account) (amount staticGas weight : Nat)
  | onClaimed (amount staticGas weight : Nat)
  deriving DecidableEq, Repr

structure Receipt where
  receiver : Account
  actions : List Action
  afterReceipt : Option Nat := none
  deriving DecidableEq, Repr

inductive Return where
  | unit
  | boolean (value : Bool)
  | balance (amount : Nat)
  | information (amount : Nat)
  | promise (index : Nat)
  deriving DecidableEq, Repr

inductive Panic where
  | initialized | uninitialized | deposit | privateCall | zeroDeposit
  | missingKey | noOptions | conflictingOptions | resultCount | resultNotReady
  deriving DecidableEq, Repr

inductive PromiseResult where
  | successful (bytes : List UInt8)
  | failed
  | notReady
  deriving DecidableEq, Repr

structure Env where
  current : Account
  predecessor : Account
  signerKey : Key
  deposit : Nat := 0
  -- Raw bytes and result positions are retained, even though success ignores the bytes.
  results : List PromiseResult := []
  deriving DecidableEq, Repr

inductive Call where
  | new
  | send (key : Key)
  | claim (account : Account)
  | createAndClaim (account : Account) (key : Key)
  | createAccount (account : Account) (key : Key)
  | createAdvanced (account : Account) (options : Options)
  | onCreated (predecessor : Account) (amount : Nat)
  | onClaimed (amount : Nat)
  | getBalance (key : Key)
  | getInformation (key : Key)
  deriving DecidableEq, Repr

def Call.payable : Call → Bool
  | .send _ | .createAccount .. | .createAdvanced .. => true
  | _ => false

def Call.view : Call → Bool
  | .getBalance _ | .getInformation _ => true
  | _ => false

def Call.private : Call → Bool
  | .claim _ | .createAndClaim .. | .onCreated .. | .onClaimed _ => true
  | _ => false

-- Arguments have already passed SDK deserialization; do not add fictitious guards.
def Call.WF : Call → Prop
  | .onCreated _ n | .onClaimed n => n ≤ maxAmount
  | .createAdvanced _ o =>
    (∀ k ∈ o.limitedKeys.getD [], k.allowance ≤ maxAmount) ∧
    (∀ h, o.globalHash = some h → h.length = 32)
  | _ => True

end Linkdrop
