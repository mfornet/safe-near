import NearVM.HostDispatch
import NearVM.InterpreterInvariant

namespace Wasm.Near

/-- The functional host permits any existing non-joint handle as a return.
The separate dependency invariant rules out unsupported yielded handles. -/
def _root_.Wasm.NearPromise.NonJoint : NearPromise → Prop
  | .and _ => False
  | _ => True

/-- A selected return names an existing, non-joint raw promise. -/
def ReturnSelectionValid (ns : NearState) : Prop :=
  ∀ index, ns.returnedPromise = some index →
    ∃ p, getPromise? ns.promises index = some p ∧ p.NonJoint

def HostPreservesSelection (fn : NearHostFn NearState) : Prop :=
  NearHostFn.Preserves ReturnSelectionValid fn

def HostResultSelectionValid := HostResult.Satisfies ReturnSelectionValid

theorem ReturnSelectionValid.of_fields {before after : NearState}
    (hps : after.promises = before.promises) (hreturn : after.returnedPromise = before.returnedPromise)
    (h : ReturnSelectionValid before) : ReturnSelectionValid after := by
  simpa only [ReturnSelectionValid, hps, hreturn] using h

theorem getPromise_append {ps tail : List NearPromise} {index : Nat} {p : NearPromise}
    (h : getPromise? ps index = some p) : getPromise? (ps ++ tail) index = some p := by
  rw [getPromise_eq_getElem?] at h ⊢
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem appendPromise_selection (st : HostStore NearState) (p : NearPromise)
    (h : ReturnSelectionValid st.host) : ReturnSelectionValid (appendPromise st p).host := by
  intro index hreturn
  obtain ⟨old, hget, hsingle⟩ := h index hreturn
  exact ⟨old, getPromise_append hget, hsingle⟩

theorem setPromise_nonJoint {ps result : List NearPromise} {index selected : Nat} {p : NearPromise}
    (hset : setPromise? ps index p = some result) (hp : p.NonJoint)
    (hselected : ∃ old, getPromise? ps selected = some old ∧ old.NonJoint) :
    ∃ new, getPromise? result selected = some new ∧ new.NonJoint := by
  induction ps generalizing index selected result with
  | nil => simp [setPromise?] at hset
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [setPromise?, Option.some.injEq] at hset
      subst result
      cases selected with
      | zero => exact ⟨p, rfl, hp⟩
      | succ selected => exact hselected
    | succ index =>
      obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hset
      subst result
      cases selected with
      | zero => exact hselected
      | succ selected => exact ih (index := index) (selected := selected) hrest hselected

theorem appendPromiseAction_selection {ps result : List NearPromise} {index selected : Nat}
    {action : PromiseAction} (h : appendPromiseAction? ps index action = some result)
    (hselected : ∃ old, getPromise? ps selected = some old ∧ old.NonJoint) :
    ∃ new, getPromise? result selected = some new ∧ new.NonJoint := by
  unfold appendPromiseAction? at h
  cases hget : getPromise? ps index with
  | none => simp [hget] at h
  | some p =>
    cases p with
    | batch account actions => exact setPromise_nonJoint (p := .batch account (actions ++ [action])) (by simpa only [hget] using h) trivial hselected
    | callback base account actions => exact setPromise_nonJoint (p := .callback base account (actions ++ [action])) (by simpa only [hget] using h) trivial hselected
    | and dependencies => simp [hget] at h
    | yielded account actions dataId => exact setPromise_nonJoint (p := .yielded account (actions ++ [action]) dataId) (by simpa only [hget] using h) trivial hselected

theorem appendPromiseActionResult_selection {weight : UInt64} (name : String) (st : HostStore NearState)
    (index : UInt64) (action : PromiseAction) (hwf : ReturnSelectionValid st.host) :
    HostResultSelectionValid (appendPromiseActionResult name st index action weight) := by
  unfold appendPromiseActionResult
  split
  · intro selected hreturn
    exact appendPromiseAction_selection (by assumption) (hwf selected hreturn)
  · exact hwf

theorem checkAccountId_selection (name : String) (st : HostStore NearState) (account : List UInt8)
    (next : Unit → HostResult NearState) (hwf : ReturnSelectionValid st.host)
    (hnext : HostResultSelectionValid (next ())) :
    HostResultSelectionValid (checkAccountId name st account next) := by
  unfold checkAccountId
  split
  · exact hnext
  · exact hwf

theorem checkPublicKey_selection (name : String) (st : HostStore NearState) (key : List UInt8)
    (next : Unit → HostResult NearState) (hwf : ReturnSelectionValid st.host)
    (hnext : HostResultSelectionValid (next ())) :
    HostResultSelectionValid (checkPublicKey name st key next) := by
  unfold checkPublicKey
  split
  · exact hnext
  · exact hwf

theorem checkDataLimit_selection (name label : String) (limit : Option Nat) (size : Nat)
    (st : HostStore NearState) (next : Unit → HostResult NearState) (hwf : ReturnSelectionValid st.host)
    (hnext : HostResultSelectionValid (next ())) {error : Option (Nat → Nat → HostError)} :
    HostResultSelectionValid (checkDataLimit name label limit size st next error) := by
  unfold checkDataLimit
  split
  · exact hnext
  · split <;> exact hwf

theorem disallowInView_selection (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesSelection fn) : HostPreservesSelection (disallowInView name fn) := by
  intro st args hwf
  unfold disallowInView
  dsimp only
  split
  · exact hwf
  · exact hfn st args hwf

theorem checkedSetRegister_selection {st after : HostStore NearState} {register : UInt64} {bytes : List UInt8}
    (h : checkedSetRegister? st register bytes = some after) (hwf : ReturnSelectionValid st.host) :
    ReturnSelectionValid after.host := by
  unfold checkedSetRegister? at h
  split at h
  · cases h
    exact hwf
  · split at h
    · cases h
      exact hwf
    · cases h

theorem writeRegisterResult_selection (name : String) (st : HostStore NearState) (register : UInt64)
    (bytes : List UInt8) (vals : List Value) (hwf : ReturnSelectionValid st.host) :
    HostResultSelectionValid (writeRegisterResult name st register bytes vals) := by
  unfold writeRegisterResult
  split
  · exact checkedSetRegister_selection (by assumption) hwf
  · exact hwf

theorem createBatchPromiseResult_selection (name : String) (st : HostStore NearState) (account : List UInt8)
    (hwf : ReturnSelectionValid st.host) : HostResultSelectionValid (createBatchPromiseResult name st account) := by
  unfold createBatchPromiseResult
  apply checkAccountId_selection _ _ _ _ hwf
  exact appendPromise_selection _ _ hwf

theorem createCallbackPromiseResult_selection (name : String) (st : HostStore NearState) (base : UInt64)
    (account : List UInt8) (hwf : ReturnSelectionValid st.host) :
    HostResultSelectionValid (createCallbackPromiseResult name st base account) := by
  unfold createCallbackPromiseResult
  split
  · apply checkAccountId_selection _ _ _ _ hwf
    exact appendPromise_selection _ _ hwf
  · exact hwf

theorem selectReturnValue_valid (ns : NearState) (bytes : List UInt8) :
    ReturnSelectionValid (ns.selectReturnValue bytes) := by
  intro index h
  cases h

theorem selectReturnPromise_valid {ns : NearState} {index : Nat} {p : NearPromise}
    (h : getPromise? ns.promises index = some p) (hp : p.NonJoint) :
    ReturnSelectionValid (ns.selectReturnPromise index) := by
  intro selected hselected
  have heq : index = selected := Option.some.inj hselected
  subst selected
  exact ⟨p, h, hp⟩

theorem selectReturnPromise_valid_of_not_joint {ns : NearState} {index : Nat} {p : NearPromise}
    (h : getPromise? ns.promises index = some p)
    (hnot : ∀ dependencies, p = .and dependencies → False) :
    ReturnSelectionValid (ns.selectReturnPromise index) := by
  apply selectReturnPromise_valid h
  cases p <;> simp_all [NearPromise.NonJoint]

end Wasm.Near
