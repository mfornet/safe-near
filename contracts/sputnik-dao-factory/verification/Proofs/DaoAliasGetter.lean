import Proofs.DaoProjection
import Proofs.Namespaces
import Proofs.DaoInsert

namespace SputnikFactory

/-- Supply the two-element STATE header after the raw-key alias sequence. The
source-level vector already contains the same account twice. -/
def duplicateDaoStateRaw : Raw :=
  write duplicateDaoRaw stateKey
    (Borsh.encodeSet (Spec.daoHeader [collisionAccount, collisionAccount]))

theorem duplicate_dao_vector_layout :
    Spec.DaoVectorLayout duplicateDaoStateRaw
      [collisionAccount, collisionAccount] := by
  constructor
  · exact read_write_self _ _ _
  · intro index hindex
    have hi : index = 0 ∨ index = 1 := by simp at hindex; omega
    rcases hi with hzero | hone
    · subst index
      decide
    · subst index
      decide

/-- The exported getter can report duplicate accounts after the known raw-key
alias sequence. It reads the vector and does not deduplicate by membership. -/
theorem duplicate_dao_getter (cfg : Config) (env : Env) :
    step cfg duplicateDaoStateRaw env .daoList =
      .ok ⟨duplicateDaoStateRaw, [],
        .accounts [collisionAccount, collisionAccount]⟩ := by
  apply dao_list_matches_layout cfg duplicateDaoStateRaw env
    [collisionAccount, collisionAccount] duplicate_dao_vector_layout
  · decide
  · intro account hmem
    have he : account = collisionAccount := by simpa using hmem
    subst account
    decide

/-- Constructed raw storage where the 32-byte code key is also an absent
DAO's membership key. This is a storage witness, not a reachability claim. -/
def aliasOnlyRaw : Raw :=
  write (write [] stateKey (Borsh.encodeSet initialSet))
    collisionHash.val [0, 97, 115, 109]

theorem alias_only_state :
    read aliasOnlyRaw stateKey = some (Borsh.encodeSet initialSet) := by decide

theorem alias_only_membership :
    read aliasOnlyRaw (daoIndexKey collisionAccount) =
      some [0, 97, 115, 109] := by decide

/-- The callback reports success but skips registration because the raw
membership key was already occupied by code bytes. The following list getter
still reports an empty vector. -/
theorem alias_only_callback_true_without_registration (cfg : Config)
    (env : Env) (predecessor : Account) (amount : Nat) (bytes : Bytes)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes]) :
    let after := write aliasOnlyRaw stateKey (Borsh.encodeSet initialSet)
    step cfg aliasOnlyRaw env
      (.onCreate collisionAccount amount predecessor) =
        .ok ⟨after, [], .boolean true⟩ ∧
    step cfg after env .daoList = .ok ⟨after, [], .accounts []⟩ := by
  dsimp
  have hinsert : (setInsert initialSet collisionAccount).run aliasOnlyRaw =
      .ok (initialSet, aliasOnlyRaw) := by
    apply set_insert_present_general
    simpa [setIndexKey, initialSet, daoIndexKey] using alias_only_membership
  constructor
  · exact successful_creation_entry_registers cfg initialSet initialSet
      aliasOnlyRaw aliasOnlyRaw env collisionAccount predecessor amount bytes
      alias_only_state (by decide) (by decide) (by decide)
      hauth hdeposit hresults hinsert
  · have hvector : Spec.DaoVectorLayout
        (write aliasOnlyRaw stateKey (Borsh.encodeSet initialSet)) [] := by
      constructor
      · exact read_write_self _ _ _
      · intro index hi
        simp at hi
    exact dao_list_matches_layout cfg _ env [] hvector (by decide)
      (by intro account hmem; simp at hmem)

end SputnikFactory
