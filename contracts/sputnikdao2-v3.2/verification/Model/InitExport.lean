import Model.ExportWrapper

namespace SputnikDAO2

/-! Link the two initializer names in the canonical export inventory to
their generated wrapper projections. JSON/Borsh argument decoding for `new`
remains the wrapper's explicit Boolean and wire-value inputs. -/
def runNamedNewExport (raw : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) : Option BountyRawTrie :=
  if findDAOExport "new" != some ⟨"new", .init, false, false⟩ then
    none
  else runNewWrapper raw ctx config policy predecessor

-- Borsh's two unit enum variants encode as one byte. `try_from_slice`
-- rejects unknown discriminants and trailing bytes; absent storage defaults
-- to V1 in `state_version_read`.
def versionReadFromRaw (raw : BountyRawTrie) : VersionRead :=
  match raw daoVersionKey with
  | none => .missing
  | some [0] => .v1
  | some [1] => .v2
  | some _ => .malformed

/-! The migration method reads `STATEVERSION` and deserializes `STATE` as V1
or V2 according to that result. The two Borsh decoders and current-state
encoder are external refinement inputs, but their bytes now come from the
actual raw root key rather than an unrelated context field. -/
def runNamedMigrateExport (raw : BountyRawTrie)
    (attachedDeposit : Nat) (current predecessor : String)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes) :
    Option BountyRawTrie := do
  if findDAOExport "migrate" !=
      some ⟨"migrate", .init, false, true⟩ then none else pure ()
  let rootBytes ← raw daoRootKey
  let ctx : MigrationContext :=
    ⟨current, predecessor, versionReadFromRaw raw,
      decodeV1 rootBytes, decodeV2 rootBytes⟩
  runMigrateWrapper raw attachedDeposit ctx encodeCurrent

end SputnikDAO2
