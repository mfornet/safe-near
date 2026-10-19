import NearVM.Metered

namespace Wasm.Near

/-- Each expanded prefix respects the limit, and every input handle exists. -/
def JoinedPrefixesValid (handles : List PromiseHandle) (limit : Nat) : List Nat → Nat → Prop
  | [], _ => True
  | index :: rest, count => ∃ handle, handles[index]? = some handle ∧
      count + handle.dependencies.length ≤ limit ∧
      JoinedPrefixesValid handles limit rest (count + handle.dependencies.length)

theorem joinedDependenciesError_none_iff (handles : List PromiseHandle) (limit : Nat)
    (indices : List Nat) (count : Nat) :
    joinedDependenciesError handles limit indices count = none ↔ JoinedPrefixesValid handles limit indices count := by
  induction indices generalizing count with
  | nil => simp [joinedDependenciesError, JoinedPrefixesValid]
  | cons index rest ih =>
    cases hget : handles[index]? with
    | none => simp [joinedDependenciesError, JoinedPrefixesValid, hget]
    | some handle =>
      by_cases hlimit : count + handle.dependencies.length > limit
      · simp [joinedDependenciesError, JoinedPrefixesValid, hget, hlimit, Nat.not_le_of_gt hlimit]
      · simp [joinedDependenciesError, JoinedPrefixesValid, hget, hlimit, Nat.le_of_not_gt hlimit, ih]

/-- Successful prefix validation admits exact ordered expansion and bounds its
length, including duplicate dependencies and nested joints. -/
theorem joinedDependenciesError_expands {handles : List PromiseHandle} {limit count : Nat}
    {indices : List Nat} (h : joinedDependenciesError handles limit indices count = none)
    (hcount : count ≤ limit) :
    ∃ dependencies, expandDependencies handles indices = some dependencies ∧ count + dependencies.length ≤ limit := by
  have hvalid := (joinedDependenciesError_none_iff handles limit indices count).mp h
  clear h
  induction indices generalizing count with
  | nil => exact ⟨[], rfl, by simpa using hcount⟩
  | cons index rest ih =>
    obtain ⟨handle, hget, hbound, htail⟩ := hvalid
    obtain ⟨tail, hexpand, hlength⟩ := ih hbound htail
    refine ⟨handle.dependencies ++ tail, ?_, ?_⟩
    · simp only [expandDependencies, hget, hexpand]
      rfl
    · simp only [List.length_append]
      omega

/-- A successful metered join has a non-overflowing input span and a bounded
expanded dependency vector; no output validator is assumed. -/
theorem preInvokeError_join_bounds {st : Store NearState} {ptr count : UInt64} {limit : Nat}
    {graph : PromiseGraph} (hlimit : st.host.config.maxInputDataDependencies = some limit)
    (hgraph : convertPromises st.host.promises = some graph)
    (h : preInvokeError "promise_and" st [.i64 ptr, .i64 count] = none) :
    count.toNat * 8 < 2 ^ 64 ∧ ∃ indices dependencies,
      readU64Array st ptr count.toNat = some indices ∧
      expandDependencies graph.handles indices = some dependencies ∧ dependencies.length ≤ limit := by
  unfold preInvokeError at h
  simp only [beq_self_eq_true, ite_true] at h
  split at h
  · simp at h
  · rename_i hsize
    refine ⟨by omega, ?_⟩
    cases hread : readU64Array st ptr count.toNat with
    | none => simp [hread] at h
    | some indices =>
      simp only [hread, hlimit, hgraph] at h
      obtain ⟨dependencies, hexpand, hbound⟩ := joinedDependenciesError_expands h (Nat.zero_le limit)
      exact ⟨indices, dependencies, rfl, hexpand, by simpa using hbound⟩

end Wasm.Near
