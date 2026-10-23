import Spec.Safety

namespace Linkdrop

theorem step_ok_body {s e c out} (h : step s e c = .ok out) :
    body s e c = .ok out := by
  unfold step at h
  repeat' split at h <;> try contradiction
  exact h

theorem set_same (s : State) (k : Key) (v : Option Nat) :
    (s.set k v).accounts k = v := by simp [State.set]

theorem set_other (s : State) (k j : Key) (v : Option Nat) (h : j ≠ k) :
    (s.set k v).accounts j = s.accounts j := by simp [State.set, h]

theorem set_wf {s : State} (hs : s.WF) (hi : s.initialized = true)
    (k : Key) (v : Option Nat) (hv : ∀ n, v = some n → n ≤ maxAmount) :
    (s.set k v).WF := by
  constructor
  · intro j n h
    by_cases hj : j = k
    · subst j; exact hv n (by simpa [State.set] using h)
    · exact hs.1 j n (by simpa [State.set, hj] using h)
  · simp [State.set, hi]


theorem step_initialized {s e c out} (h : step s e c = .ok out)
    (hc : c ≠ .new) : s.initialized = true := by
  unfold step at h
  repeat' split at h <;> try contradiction
  cases hs : s.initialized <;> simp_all

theorem privateAuthorization : Spec.PrivateAuthorization := by
  intro s e c out hc h
  unfold step at h
  repeat' split at h <;> try contradiction
  simp_all

theorem initOnce : Spec.InitOnce := by
  constructor
  · intro s e h hd; simp [step, h, hd, Call.private, Call.payable, Call.view]
  · intro s e out h
    have hb := step_ok_body h
    simp only [body, Except.ok.injEq] at hb
    subst out
    simp

theorem viewsPure : Spec.ViewsPure := by
  intro s e c out hc h
  have hb := step_ok_body h
  cases c <;> simp_all [Call.view, body]
  all_goals split at hb <;> simp_all
  all_goals cases hb; simp

theorem mapAuthorization : Spec.MapAuthorization := by
  intro s e c out k hs h hk
  have hb := step_ok_body h
  cases c <;> simp only [Spec.touchedKey] at hk <;> simp only [body] at hb
  all_goals try simp only [creation, callbackSuccess] at hb
  all_goals repeat' (split at hb <;> simp_all)
  all_goals try simp only [Except.ok.injEq] at hb
  all_goals subst out
  all_goals simp_all [State.set, ne_comm]
  · have hi : s.initialized = false := by
      cases hi : s.initialized <;> simp_all [step, Call.private, Call.payable, Call.view]
      split at h <;> contradiction
    exact (hs.2 hi k).symm

theorem returnSelection : Spec.ReturnSelection := by
  intro s e c out i h hr
  have hb := step_ok_body h
  cases c <;> simp only [body] at hb
  all_goals try simp only [creation, callbackSuccess] at hb
  all_goals repeat' (split at hb <;> simp_all)
  all_goals try simp only [Except.ok.injEq] at hb
  all_goals subst out
  all_goals simp_all
  all_goals omega

theorem callbackArity : Spec.CallbackArity := by
  intro s e c out hc h
  have hb := step_ok_body h
  rcases hc with ⟨a, n, rfl⟩ | ⟨n, rfl⟩
  all_goals
    cases hr : e.results with
    | nil => simp [body, callbackSuccess, hr] at hb
    | cons b rest =>
      cases rest with
      | nil => simp
      | cons b' rest => cases b <;> simp [body, callbackSuccess, hr] at hb

theorem invPreserved : Spec.InvPreserved := by
  intro s e c out hs hd hc h
  have hb := step_ok_body h
  by_cases hnew : c = .new
  · subst c
    simp only [body, Except.ok.injEq] at hb
    subst out
    simp [State.WF]
  have hi := step_initialized h hnew
  cases c <;> simp only [Call.WF] at hc <;> simp only [body] at hb
  all_goals try simp only [creation, callbackSuccess] at hb
  all_goals repeat' (split at hb <;> simp_all)
  all_goals try simp only [Except.ok.injEq] at hb
  all_goals subst out
  all_goals simp_all
  all_goals (apply set_wf hs hi; intros; simp_all)
  all_goals omega

end Linkdrop
