import NearRuntime.Types

/-!
# Incoming receipt schedules

A schedule selects positions in the pending queue at the start of a block.
Positions remain stable while selections are removed, so `[2, 0]` delivers
the original third receipt before the original first receipt. Unselected
receipts retain their relative order. No receipt ids or payloads are forged.
-/

namespace Near

inductive ReceiptSchedule
  | all
  | indices (positions : List Nat)
  deriving Repr, BEq, Inhabited

inductive ScheduleError
  /-- The position does not exist, or was already selected in this block. -/
  | unavailableIndex (position : Nat)
  deriving Repr, BEq, Inhabited

namespace ReceiptSchedule

private def extract (position : Nat) :
    List (Nat × Receipt) → Option (Receipt × List (Nat × Receipt))
  | [] => none
  | (index, receipt) :: rest =>
    if index = position then some (receipt, rest)
    else
      (extract position rest).map fun (selected, remaining) =>
        (selected, (index, receipt) :: remaining)

private def select :
    List Nat → List (Nat × Receipt) → Except ScheduleError (List Receipt × List Receipt)
  | [], available => .ok ([], available.map Prod.snd)
  | position :: positions, available =>
    match extract position available with
    | none => .error (.unavailableIndex position)
    | some (receipt, remaining) =>
      match select positions remaining with
      | .error error => .error error
      | .ok (selected, deferred) => .ok (receipt :: selected, deferred)

/-- Resolve an ordered delivery without changing state. A rejected schedule
never exposes a partially selected queue. -/
def resolve (pending : List Receipt) :
    ReceiptSchedule → Except ScheduleError (List Receipt × List Receipt)
  | .all => .ok (pending, [])
  | .indices positions =>
    select positions (pending.zipIdx.map fun (receipt, index) => (index, receipt))

private theorem extract_perm (position : Nat) (available : List (Nat × Receipt)) (receipt : Receipt)
    (remaining : List (Nat × Receipt))
    (h : extract position available = some (receipt, remaining)) :
    (receipt :: remaining.map Prod.snd).Perm (available.map Prod.snd) := by
  induction available generalizing remaining with
  | nil => simp [extract] at h
  | cons head tail ih =>
    rcases head with ⟨index, value⟩
    by_cases hi : index = position
    · simp [extract, hi] at h
      rcases h with ⟨rfl, rfl⟩
      exact List.Perm.refl _
    · cases he : extract position tail with
      | none => simp [extract, hi, he] at h
      | some pair =>
        rcases pair with ⟨found, rest⟩
        simp [extract, hi, he] at h
        rcases h with ⟨rfl, rfl⟩
        exact (List.Perm.swap ..).trans ((ih rest he).cons value)

private theorem select_perm (positions : List Nat) (available : List (Nat × Receipt))
    (selected deferred : List Receipt) (h : select positions available = .ok (selected, deferred)) :
    (selected ++ deferred).Perm (available.map Prod.snd) := by
  induction positions generalizing available selected deferred with
  | nil =>
    simp [select] at h
    rcases h with ⟨rfl, rfl⟩
    exact List.Perm.refl _
  | cons position positions ih =>
    cases he : extract position available with
    | none => simp [select, he] at h
    | some pair =>
      rcases pair with ⟨receipt, remaining⟩
      cases hs : select positions remaining with
      | error error => simp [select, he, hs] at h
      | ok pair =>
        rcases pair with ⟨chosen, rest⟩
        simp [select, he, hs] at h
        rcases h with ⟨rfl, rfl⟩
        exact
          ((ih remaining chosen rest hs).cons receipt).trans
            (extract_perm position available receipt remaining he)

/-- Every successful schedule partitions the original pending receipts:
delivery order may change, but no receipt is duplicated, dropped or invented. -/
theorem resolve_perm (pending : List Receipt) (schedule : ReceiptSchedule)
    (selected deferred : List Receipt) (h : resolve pending schedule = .ok (selected, deferred)) :
    (selected ++ deferred).Perm pending := by
  cases schedule with
  | all =>
    simp [resolve] at h
    rcases h with ⟨rfl, rfl⟩
    simp
  | indices positions =>
    have hp := select_perm positions _ selected deferred h
    simpa [List.map_map, Function.comp_def] using hp

private theorem extract_sublist (position : Nat) (available : List (Nat × Receipt))
    (receipt : Receipt) (remaining : List (Nat × Receipt))
    (h : extract position available = some (receipt, remaining)) :
    List.Sublist (remaining.map Prod.snd) (available.map Prod.snd) := by
  induction available generalizing remaining with
  | nil => simp [extract] at h
  | cons head tail ih =>
    rcases head with ⟨index, value⟩
    by_cases hi : index = position
    · simp [extract, hi] at h
      rcases h with ⟨rfl, rfl⟩
      exact (List.Sublist.refl _).cons value
    · cases he : extract position tail with
      | none => simp [extract, hi, he] at h
      | some pair =>
        rcases pair with ⟨found, rest⟩
        simp [extract, hi, he] at h
        rcases h with ⟨rfl, rfl⟩
        exact (ih rest he).cons_cons value

private theorem select_sublist (positions : List Nat) (available : List (Nat × Receipt))
    (selected deferred : List Receipt) (h : select positions available = .ok (selected, deferred)) :
    List.Sublist deferred (available.map Prod.snd) := by
  induction positions generalizing available selected deferred with
  | nil =>
    simp [select] at h
    rcases h with ⟨rfl, rfl⟩
    exact List.Sublist.refl _
  | cons position positions ih =>
    cases he : extract position available with
    | none => simp [select, he] at h
    | some pair =>
      rcases pair with ⟨receipt, remaining⟩
      cases hs : select positions remaining with
      | error error => simp [select, he, hs] at h
      | ok pair =>
        rcases pair with ⟨chosen, rest⟩
        simp [select, he, hs] at h
        rcases h with ⟨rfl, rfl⟩
        exact
          (ih remaining chosen rest hs).trans
            (extract_sublist position available receipt remaining he)

/-- Deferral preserves the relative order of all unselected receipts. -/
theorem resolve_deferred_sublist (pending : List Receipt) (schedule : ReceiptSchedule)
    (selected deferred : List Receipt) (h : resolve pending schedule = .ok (selected, deferred)) :
    List.Sublist deferred pending := by
  cases schedule with
  | all =>
    simp [resolve] at h
    rcases h with ⟨rfl, rfl⟩
    exact List.nil_sublist _
  | indices positions =>
    have hp := select_sublist positions _ selected deferred h
    simpa [List.map_map, Function.comp_def] using hp

end ReceiptSchedule

end Near
