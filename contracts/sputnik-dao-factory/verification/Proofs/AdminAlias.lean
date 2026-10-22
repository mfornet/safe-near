import Proofs.Admin
import Proofs.Namespaces

namespace SputnikFactory

/-- Constructed factory storage with one DAO membership index and its STATE
header. The index key is also `collisionHash.val`; no Wasm record is added. -/
def aliasDefaultRaw : Raw :=
  write singletonDaoStorage stateKey (Borsh.encodeSet oneDaoHeader)

theorem alias_default_state :
    read aliasDefaultRaw stateKey = some (Borsh.encodeSet oneDaoHeader) := by decide

theorem alias_default_raw_key :
    read aliasDefaultRaw collisionHash.val = some (leBytes 8 0) := by decide

theorem alias_default_owner_missing : read aliasDefaultRaw ownerKey = none := by decide

theorem alias_default_owner_is_current (current : Account)
    (hvalid : validAccount current = true) :
    (getOwner current).run aliasDefaultRaw = .ok (current, aliasDefaultRaw) := by
  have hutf8 := string_utf8_roundtrip current
  simp only [String.toUTF8_eq_toByteArray] at hutf8 ⊢
  simp [getOwner, alias_default_owner_missing, hutf8, hvalid,
    load, expect, require, Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- Through the exported owner-gated method, the factory accepts a DAO index
as its default code hash because only raw key presence is checked. The getter
then reports that hash. This constructed storage witness does not establish
that a chain can reach the state through authorized public transactions. -/
theorem exported_default_accepts_dao_index (cfg : Config) (env : Env)
    (hauth : env.predecessor = env.current)
    (hvalid : validAccount env.current = true) :
    let after := write aliasDefaultRaw defaultKey collisionHash.val
    step cfg aliasDefaultRaw env (.setDefault collisionHash) =
      .ok ⟨after, [], .unit⟩ ∧
    step cfg after env .defaultHash = .ok ⟨after, [], .hash collisionHash⟩ := by
  dsimp
  have howner : (getOwner env.current).run aliasDefaultRaw =
      .ok (env.predecessor, aliasDefaultRaw) := by
    rw [hauth]
    exact alias_default_owner_is_current env.current hvalid
  exact set_default_then_getter cfg aliasDefaultRaw env oneDaoHeader
    collisionHash (leBytes 8 0) alias_default_state
    (by decide) (by decide) (by decide) howner alias_default_raw_key

end SputnikFactory
