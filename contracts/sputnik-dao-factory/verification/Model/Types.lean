import Model.Storage

namespace SputnikFactory

def u64Bound : Nat := 2 ^ 64
def maxAmount : Nat := 2 ^ 128 - 1

structure Metadata where
  major : UInt8
  minor : UInt8
  commit : String
  changelog : Option String
  deriving DecidableEq, Repr

export NearSdk.Collections (VectorHeader SetHeader MapHeader)

def initialSet : SetHeader := ⟨[100, 105], ⟨0, [100, 101]⟩⟩
def initialMap : MapHeader := ⟨[109, 105], ⟨0, [109, 107]⟩, ⟨0, [109, 118]⟩⟩

inductive Panic where
  | privateCall | deposit | initialized | uninitialized | invalidState
  | owner | invalidOwner | defaultMissing | metadataMissing | invalidMetadata
  | codeMissing | alreadyExists | noInput | insufficientDeposit | defaultProtected
  | invalidAccount | callbackArity | notReady | updateAuthority | daoMissing
  | overflow | invalidIndex | inconsistent | missingElement
  deriving DecidableEq, Repr

inductive PromiseResult where
  | successful (bytes : Bytes)
  | failed
  | notReady
  deriving DecidableEq, Repr

structure Env where
  -- Transaction context only. Host view-mode rejection of storage writes is a
  -- separate runtime refinement obligation, including for &self methods.
  current : Account
  predecessor : Account
  deposit : Nat := 0
  input : Option Bytes := some []
  results : List PromiseResult := []
  deriving DecidableEq, Repr

structure Config where
  -- Deterministic SHA256 interpretation. No injectivity is assumed; concrete
  -- host equivalence remains part of binary refinement.
  sha256 : Bytes → Hash
  storageByteCost : Nat
  recordOverhead : Nat

inductive Call where
  | new
  | setOwner (owner : Account)
  | setDefault (hash : Hash)
  | deleteContract (hash : Hash)
  | create (name : Account) (args : Bytes)
  | onCreate (account : Account) (amount : Nat) (predecessor : Account)
  | update (account : Account) (hash : Hash)
  | daoList
  | daoCount
  | daos (fromIndex limit : Nat)
  | getOwner
  | defaultHash
  | defaultVersion
  | store
  | getCode (hash : Hash)
  | storeMetadata (hash : Hash) (metadata : Metadata) (setDefault : Bool)
  | deleteMetadata (hash : Hash)
  | getMetadata
  deriving DecidableEq

def Call.isNew : Call → Bool | .new => true | _ => false

def Call.private : Call → Bool | .onCreate .. => true | _ => false

-- &self methods perform raw writes but SDK View wrappers do not reject deposits.
def Call.rejectDeposit : Call → Bool | .new | .onCreate .. => true | _ => false

def Call.saveHeader : Call → Bool
  | .create .. | .onCreate .. | .store => true
  | _ => false

def Call.ownerOnly : Call → Bool
  | .setOwner _ | .setDefault _ | .deleteContract _ | .store |
    .storeMetadata .. | .deleteMetadata _ => true
  | _ => false

def Call.pure : Call → Bool
  | .daoList | .daoCount | .daos .. | .getOwner | .defaultHash |
    .defaultVersion | .getCode _ | .getMetadata => true
  | _ => false

/-- Inputs have passed SDK JSON (or raw store input) deserialization. -/
def Call.WF : Call → Prop
  | .setOwner account | .create account _ => validAccount account = true
  | .onCreate account amount predecessor => validAccount account = true ∧
      validAccount predecessor = true ∧ amount ≤ maxAmount
  | .update account _ => validAccount account = true
  | .daos fromIndex limit => fromIndex < u64Bound ∧ limit < u64Bound
  | .storeMetadata _ metadata _ => metadata.commit.toUTF8.size < 2 ^ 32 ∧
      ∀ text, metadata.changelog = some text → text.toUTF8.size < 2 ^ 32
  | _ => True

inductive Action where
  | createAccount
  | transfer (amount : Nat)
  | useGlobal (hash : Hash)
  | deployGlobal (bytes : Bytes)
  | functionCall (method : String) (args : Bytes) (deposit staticGas weight : Nat)
  | onCreate (account : Account) (amount : Nat) (predecessor : Account) (staticGas : Nat)
  deriving DecidableEq

structure Receipt where
  receiver : Account
  actions : List Action
  afterReceipt : Option Nat := none
  deriving DecidableEq

inductive Return where
  | unit
  | hash (value : Hash)
  | bytes (value : Bytes)
  | boolean (value : Bool)
  | accounts (value : List Account)
  | count (value : Nat)
  | version (major minor : UInt8)
  | metadata (value : List (Hash × Metadata))
  | promise (index : Nat)
  | account (value : Account)
  deriving DecidableEq

structure Effects where
  header : SetHeader
  receipts : List Receipt := []
  result : Return := .unit

structure Outcome where
  raw : Raw
  receipts : List Receipt := []
  result : Return := .unit

end SputnikFactory
