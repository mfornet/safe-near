import Model.Storage

namespace SputnikFactory.Spec

/-- A tempting but false disjointness assumption: code-hash inputs occupy all
32-byte keys, and DAO membership indexes can have exactly that length. -/
def CodeDaoNamespacesDisjoint : Prop :=
  ∀ (hash : Hash) (account : Account), validAccount account = true →
    codeKey hash ≠ daoIndexKey account

/-- Only the fixed short metadata/header keys are disjoint by length. -/
def FixedKeysDisjoint : Prop :=
  ∀ hash : Hash, codeKey hash ≠ defaultKey ∧ codeKey hash ≠ ownerKey ∧
    codeKey hash ≠ metadataKey ∧ codeKey hash ≠ stateKey

end SputnikFactory.Spec
