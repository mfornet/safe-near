import Model.ConstructorTrie
import Proofs.ConfigPolicyDecoding

namespace SputnikDAO2

theorem constructor_keys_distinct :
    ([daoConfigKey, daoPolicyKey, daoFactoryKey,
      daoVersionKey, daoRootKey] : List BountyBytes).Nodup := by
  decide

theorem constructor_aux_has_no_root
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) :
    constructorAuxTrie config policy predecessor daoRootKey = none := by
  simp [constructorAuxTrie, bountyRawWrite, bountyEmptyRaw,
    daoRootKey, daoVersionKey, daoFactoryKey,
    daoPolicyKey, daoConfigKey]

theorem constructor_trie_exact_keys
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) :
    constructorTrie config policy predecessor daoConfigKey =
      some (encodeWireConfig config) ∧
    constructorTrie config policy predecessor daoPolicyKey =
      some (encodeWireVersionedPolicy (.current policy)) ∧
    constructorTrie config policy predecessor daoFactoryKey =
      some (initializedFactoryBytes predecessor) ∧
    constructorTrie config policy predecessor daoVersionKey =
      some initializedVersionBytes ∧
    constructorTrie config policy predecessor daoRootKey =
      some initializedRootBytes := by
  simp [constructorTrie, constructorAuxTrie, bountyRawWrite,
    daoConfigKey, daoPolicyKey, daoFactoryKey,
    daoVersionKey, daoRootKey]

theorem constructor_trie_no_other_keys
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) (key : BountyBytes)
    (hother : ¬ constructorKey key) :
    constructorTrie config policy predecessor key = none := by
  simp only [constructorKey, not_or] at hother
  rcases hother with ⟨hc, hp, hf, hv, hr⟩
  simp [constructorTrie, constructorAuxTrie, bountyRawWrite,
    bountyEmptyRaw, hc, hp, hf, hv, hr]

theorem constructor_trie_collection_namespaces_empty
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) (tag : UInt8) (suffix : BountyBytes)
    (htag : tag ∈ daoCollectionTags) :
    constructorTrie config policy predecessor (tag :: suffix) = none := by
  have hother : ¬ constructorKey (tag :: suffix) := by
    simp [constructorKey, daoCollectionTags,
      daoConfigKey, daoPolicyKey, daoFactoryKey,
      daoVersionKey, daoRootKey] at htag ⊢
    rcases htag with h | h | h | h | h | h <;> subst tag <;> simp
  exact constructor_trie_no_other_keys config policy predecessor
    (tag :: suffix) hother

theorem constructor_trie_config_decodes
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) (hfits : wireConfigFits config) :
    ((constructorTrie config policy predecessor daoConfigKey).bind
      parseWireConfigExact) = some config := by
  rw [(constructor_trie_exact_keys config policy predecessor).1]
  change parseWireConfigExact (encodeWireConfig config) = some config
  exact parse_wire_config_exact_encoded config hfits

theorem constructor_trie_policy_decodes_current
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) (hfits : wirePolicyFits policy) :
    ((constructorTrie config policy predecessor daoPolicyKey).bind
      parseWirePolicyExact) = some (.current policy) := by
  rw [(constructor_trie_exact_keys config policy predecessor).2.1]
  change parseWirePolicyExact
    (encodeWireVersionedPolicy (.current policy)) = some (.current policy)
  exact parse_wire_policy_exact_encoded (.current policy) hfits

end SputnikDAO2
