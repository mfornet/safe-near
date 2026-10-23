import NearVM.HostPromises

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
theorem promiseJoinError_bounds {st : HostStore NearState} {ptr count : UInt64} {limit : Nat}
    {graph : PromiseGraph} (hlimit : st.host.config.maxInputDataDependencies = some limit)
    (hgraph : convertPromises st.host.promises = some graph)
    (h : promiseJoinError st [.i64 ptr, .i64 count] = none) :
    count.toNat * 8 < 2 ^ 64 ∧ ∃ indices dependencies,
      readU64Array st ptr count.toNat = some indices ∧
      expandDependencies graph.handles indices = some dependencies ∧ dependencies.length ≤ limit := by
  unfold promiseJoinError at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hsize
    refine ⟨by omega, ?_⟩
    split at h
    · simp at h
    · cases hread : readU64Array st ptr count.toNat with
      | none => simp [hread] at h
      | some indices =>
        cases indices with
        | nil => exact ⟨[], [], rfl, rfl, by simp⟩
        | cons first rest =>
          simp only [hread, hlimit, hgraph] at h
          obtain ⟨dependencies, hexpand, hbound⟩ := joinedDependenciesError_expands h (Nat.zero_le limit)
          exact ⟨first :: rest, dependencies, rfl, hexpand, by simpa using hbound⟩

theorem preInvokeError_arguments_valid {name : String} {st : HostStore NearState} {args : List Value}
    (h : preInvokeError name st args = none) : invocationArgumentError name st args = none := by
  unfold preInvokeError at h
  cases ha : invocationArgumentError name st args with
  | none => rfl
  | some error => simp [ha] at h

theorem preInvokeError_join_bounds {st : HostStore NearState} {ptr count : UInt64} {limit : Nat}
    {graph : PromiseGraph} (hlimit : st.host.config.maxInputDataDependencies = some limit)
    (hgraph : convertPromises st.host.promises = some graph)
    (h : preInvokeError "promise_and" st [.i64 ptr, .i64 count] = none) :
    count.toNat * 8 < 2 ^ 64 ∧ ∃ indices dependencies,
      readU64Array st ptr count.toNat = some indices ∧
      expandDependencies graph.handles indices = some dependencies ∧ dependencies.length ≤ limit := by
  apply promiseJoinError_bounds hlimit hgraph
  have ha := preInvokeError_arguments_valid h
  simpa [invocationArgumentError, storageMutationPlan?] using ha

theorem preInvokeError_join_span_bound {st : HostStore NearState} {ptr count : UInt64}
    (h : preInvokeError "promise_and" st [.i64 ptr, .i64 count] = none) :
    ptr.toNat + count.toNat * 8 ≤ memBytes st := by
  have ha := preInvokeError_arguments_valid h
  have hj : promiseJoinError st [.i64 ptr, .i64 count] = none := by
    simpa [invocationArgumentError, storageMutationPlan?] using ha
  unfold promiseJoinError at hj
  dsimp only at hj
  split at hj
  · simp at hj
  · split at hj
    · simp at hj
    · omega

theorem promiseCapacityError_none_iff {st : HostStore NearState} {limit : Nat}
    (hlimit : st.host.config.maxPromises = some limit) :
    promiseCapacityError st = none ↔ st.host.promises.length + 1 ≤ limit := by
  unfold promiseCapacityError
  rw [hlimit]
  split <;> simp_all

theorem preInvokeError_count_bound {name : String} {st : HostStore NearState} {args : List Value} {limit : Nat}
    (hlimit : st.host.config.maxPromises = some limit) (halloc : allocatesPromise name = true)
    (h : preInvokeError name st args = none) : st.host.promises.length + 1 ≤ limit := by
  have ha := preInvokeError_arguments_valid h
  have hcapacity : promiseCapacityError st = none := by
    unfold preInvokeError at h
    simp only [ha, halloc, ite_true] at h
    cases hc : promiseCapacityError st with
    | none => rfl
    | some error => simp [hc] at h
  exact (promiseCapacityError_none_iff hlimit).mp hcapacity

theorem checked_nextPromiseIdx_fresh {st : HostStore NearState} {limit : Nat}
    (hlimit : st.host.config.maxPromises = some limit) (h : promiseCapacityError st = none)
    (h64 : limit < 2 ^ 64) (p : NearPromise) :
    (nextPromiseIdx st).toNat = st.host.promises.length ∧
      getPromise? st.host.promises (nextPromiseIdx st).toNat = none ∧
      getPromise? (appendPromise st p).host.promises (nextPromiseIdx st).toNat = some p := by
  have hbound := (promiseCapacityError_none_iff hlimit).mp h
  have hindex : (nextPromiseIdx st).toNat = st.host.promises.length := by
    simp only [nextPromiseIdx, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : st.host.promises.length < 2 ^ 64)]
  refine ⟨hindex, ?_, ?_⟩
  · simp [getPromise_eq_getElem?, hindex]
  · simp [appendPromise, getPromise_eq_getElem?, hindex]

end Wasm.Near
