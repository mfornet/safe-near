import Std

/-! Pinned factory storage primitives. These retain the shared raw-key namespace
rather than postulating disjoint logical code and DAO maps. Full exported-method
semantics and SDK entry guards are added separately; helpers here are the exact
internal operations after their callers' guards. -/
namespace SputnikFactory

abbrev Bytes := List UInt8
abbrev Raw := List (Bytes × Bytes)
abbrev Account := String
abbrev Hash := { bytes : Bytes // bytes.length = 32 }

def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

def borshBytes (bs : Bytes) : Bytes := leBytes 4 bs.length ++ bs

def borshString (text : String) : Bytes := borshBytes text.toUTF8.data.toList

def codeKey (hash : Hash) : Bytes := hash.val

def defaultKey : Bytes := [67, 79, 68, 69]
def ownerKey : Bytes := [79, 87, 78, 69, 82]
def metadataKey : Bytes := [77, 69, 84, 65, 68, 65, 84, 65]
def stateKey : Bytes := [83, 84, 65, 84, 69]

/-- UnorderedSet::new(b"d"): the index prefix is "di", elements prefix is "de". -/
def daoIndexKey (account : Account) : Bytes := [100, 105] ++ borshString account

def daoElementKey (index : Nat) : Bytes := [100, 101] ++ leBytes 8 index

def read (raw : Raw) (key : Bytes) : Option Bytes := raw.lookup key

def remove (raw : Raw) (key : Bytes) : Raw := raw.filter fun entry => entry.1 != key

def write (raw : Raw) (key value : Bytes) : Raw := (key, value) :: remove raw key

def has (raw : Raw) (key : Bytes) : Bool := (read raw key).isSome

/-- Trie keys are unique. Enumeration order is not semantically significant. -/
def Raw.WF (raw : Raw) : Prop := (raw.map Prod.fst).Nodup

/-- AccountId parser's ASCII syntax, including separator adjacency and length.
This is a source-model validator; equivalence with the pinned Rust parser is open. -/
def validAccount (account : Account) : Bool := Id.run do
  let bytes := account.toUTF8.data.toList
  if bytes.length < 2 || bytes.length > 64 then return false
  let mut previousSeparator := true
  for byte in bytes do
    let n := byte.toNat
    if (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) then
      previousSeparator := false
    else if (n == 45 || n == 95 || n == 46) && !previousSeparator then
      previousSeparator := true
    else return false
  return !previousSeparator

inductive StorageError where
  | codeMissing
  deriving DecidableEq, Repr

/-- lib.rs::set_default_code_hash, after assert_owner. It checks storage_has_key
of the raw supplied hash, not membership in a separately namespaced code table. -/
def setDefaultAfterAuthorization (raw : Raw) (hash : Hash) : Except StorageError Raw :=
  if has raw (codeKey hash) then .ok (write raw defaultKey hash.val) else .error .codeMissing

/-- factory_manager.rs::get_code: returns the raw bytes at the supplied key. -/
def getCode (raw : Raw) (hash : Hash) : Except StorageError Bytes :=
  match read raw (codeKey hash) with
  | none => .error .codeMissing
  | some bytes => .ok bytes

/-- factory_manager.rs::delete_contract has no independent domain tag or guard.
The exported caller supplies owner/default/metadata checks. -/
def deleteCode (raw : Raw) (hash : Hash) : Raw := remove raw (codeKey hash)

/-- The successful UnorderedSet insertion writes an index record and a vector
record. Overflow and duplicate-index guards belong to the calling set operation. -/
def writeDaoEntry (raw : Raw) (account : Account) (index : Nat) : Raw :=
  write (write raw (daoIndexKey account) (leBytes 8 index))
    (daoElementKey index) (borshString account)

end SputnikFactory
