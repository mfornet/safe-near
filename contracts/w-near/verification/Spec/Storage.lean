import Spec.Invariants

/-!
# On-chain layout

The view is faithful (every well-formed state is recovered from its storage)
and the registration fee covers the storage an account entry costs.
-/

namespace WNear

/-- The view recovers every well-formed state from its encoding: `encode` is
injective on well-formed states. -/
@[blueprint "spec:project-encode"
  (statement := /-- For every well-formed $s$, $\mathrm{project}(\mathrm{encode}(s)) = s$. -/)]
def ProjectEncode : Prop :=
  ∀ s : State, s.WF → project (encode s) = some s

/-- The storage the contract occupies is at most the `STATE` record plus
`accountStorageUsage` bytes per registered account, i.e. what the collected
registration fees pay for. This holds because `new` measured the entry of a
longest possible (64-byte) account id. -/
@[blueprint "spec:storage-coverage"
  (statement := /-- Under \cref{def:inv}, the storage usage of $\mathrm{encode}(s)$ is at most the bytes of the \texttt{STATE} record plus $|\mathit{registered}| \cdot \mathit{accountStorageUsage}$. -/)]
def StorageCoverage : Prop :=
  ∀ (cfg : Config) (s : State), Inv cfg s →
    storageUsage cfg (encode s)
      ≤ cfg.recordBytes (stateKey, header s) + s.registered.card * s.accountStorageUsage

end WNear
