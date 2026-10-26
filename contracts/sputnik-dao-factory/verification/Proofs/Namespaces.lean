import Spec.Namespaces
import Model.Collections

namespace SputnikFactory

theorem dao_index_key_length (account : Account) :
    (daoIndexKey account).length = 6 + account.toUTF8.data.toList.length := by
  simp [daoIndexKey, borshString, NearSdk.Borsh.bytes, NearSdk.Borsh.u32]
  omega

theorem dao_element_key_length (index : Nat) : (daoElementKey index).length = 10 := by
  simp [daoElementKey]

theorem code_ne_dao_element (hash : Hash) (index : Nat) :
    codeKey hash ≠ daoElementKey index := by
  intro he
  have hlen := congrArg List.length he
  simp [codeKey, dao_element_key_length, hash.property] at hlen

theorem code_ne_metadata_index (hash key : Hash) :
    codeKey hash ≠ mapIndexKey initialMap key := by
  intro he
  have hlen := congrArg List.length he
  simp [codeKey, mapIndexKey, initialMap, hash.property, key.property] at hlen

theorem code_ne_metadata_vector (hash : Hash) (index : Nat) :
    codeKey hash ≠ vectorKey initialMap.keys index ∧
    codeKey hash ≠ vectorKey initialMap.values index := by
  constructor
  · intro he
    have hlen := congrArg List.length he
    simp [codeKey, vectorKey, initialMap, hash.property] at hlen
  · intro he
    have hlen := congrArg List.length he
    simp [codeKey, vectorKey, initialMap, hash.property] at hlen

theorem dao_index_ne_element (account : Account) (index : Nat) :
    daoIndexKey account ≠ daoElementKey index := by
  intro he
  have hprefix := congrArg (List.take 2) he
  simp [daoIndexKey, daoElementKey] at hprefix

/-- Code/DAO index overlap is possible precisely at 26 UTF-8 account bytes. -/
theorem code_dao_overlap_requires_26_bytes (hash : Hash) (account : Account)
    (he : codeKey hash = daoIndexKey account) :
    account.toUTF8.data.toList.length = 26 := by
  have hlen := congrArg List.length he
  rw [dao_index_key_length] at hlen
  change hash.val.length = 6 + account.toUTF8.data.toList.length at hlen
  rw [hash.property] at hlen
  omega

theorem fixedKeysDisjoint : Spec.FixedKeysDisjoint := by
  intro hash
  have hlen := hash.property
  constructor
  · intro h
    have he := congrArg List.length h
    simp [codeKey, defaultKey, hlen] at he
  constructor
  · intro h
    have he := congrArg List.length h
    simp [codeKey, ownerKey, hlen] at he
  constructor
  · intro h
    have he := congrArg List.length h
    simp [codeKey, metadataKey, hlen] at he
  · intro h
    have he := congrArg List.length h
    simp [codeKey, stateKey, hlen] at he

/-- This is a syntactically valid direct child created by name "aaaaaaaaa".
No SHA256 collision or preimage is needed: the setter accepts arbitrary hashes. -/
def collisionAccount : Account := "aaaaaaaaa.sputnik-dao.near"

def collisionHash : Hash := ⟨daoIndexKey collisionAccount, by decide⟩

theorem collision_account_valid : validAccount collisionAccount = true := by decide

theorem collision_account_is_child :
    collisionAccount = "aaaaaaaaa" ++ "." ++ "sputnik-dao.near" := rfl

theorem code_dao_key_collision : codeKey collisionHash = daoIndexKey collisionAccount := rfl

theorem namespaces_not_disjoint : ¬Spec.CodeDaoNamespacesDisjoint := by
  intro h
  exact h collisionHash collisionAccount collision_account_valid code_dao_key_collision

/-- A storage fragment of a valid one-element DAO set; STATE/metadata records
can be added at their disjoint keys without changing these observations. -/
def singletonDaoStorage : Raw := writeDaoEntry [] collisionAccount 0

theorem singleton_storage_unique : Raw.WF singletonDaoStorage := by
  unfold Raw.WF
  decide

/-- The owner-authorized setter's internal storage check accepts this DAO index
as if it named code. This proves source-model behavior, not full-call refinement. -/
theorem dao_index_accepted_as_default :
    (setDefaultAfterAuthorization singletonDaoStorage collisionHash).map
      (fun raw => read raw defaultKey) = .ok (some collisionHash.val) := rfl

theorem get_code_can_return_dao_index :
    getCode singletonDaoStorage collisionHash = .ok (leBytes 8 0) := rfl

theorem returned_index_is_not_wasm_magic : (leBytes 8 0).take 4 ≠ [0, 97, 115, 109] := by decide

/-- Internal deletion can remove DAO membership while retaining its vector
entry. Exported delete additionally needs authorization, a non-default hash and
an existing metadata header; those guards are not bypassed by this witness. -/
theorem code_deletion_erases_membership_only :
    has (deleteCode singletonDaoStorage collisionHash) (daoIndexKey collisionAccount) = false ∧
    read (deleteCode singletonDaoStorage collisionHash) (daoElementKey 0) =
      some (borshString collisionAccount) := by decide

/-- A subsequent set insertion can append the already present DAO a second
time after raw-code deletion removes its membership index. -/
def oneDaoHeader : SetHeader :=
  { initialSet with elements := { initialSet.elements with length := 1 } }

def duplicateDaoRaw : Raw :=
  write
    (write (deleteCode singletonDaoStorage collisionHash)
      (daoIndexKey collisionAccount) (leBytes 8 1))
    (daoElementKey 1) (borshString collisionAccount)

theorem deleted_membership_allows_duplicate_vector_entry :
    (setInsert oneDaoHeader collisionAccount).run
      (deleteCode singletonDaoStorage collisionHash) =
      .ok ({ oneDaoHeader with elements := { oneDaoHeader.elements with length := 2 } },
        duplicateDaoRaw) ∧
    read duplicateDaoRaw (daoElementKey 0) = some (borshString collisionAccount) ∧
    read duplicateDaoRaw (daoElementKey 1) = some (borshString collisionAccount) := by
  constructor
  · rfl
  · decide

end SputnikFactory
