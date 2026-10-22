import Model.Views

namespace SputnikDAO2

theorem pageScan_eq_filterMap {α : Type} (lookup : Nat → Option α)
    (start fuel : Nat) :
    pageScan lookup start fuel =
      (List.range' start fuel).filterMap
        (fun id => (lookup id).map (fun value => (id, value))) := by
  induction fuel generalizing start with
  | zero => simp [pageScan]
  | succ n ih =>
      simp only [pageScan, List.range'_succ, List.filterMap_cons]
      rw [ih]
      cases lookup start <;> rfl

theorem pageScan_length_le {α : Type} (lookup : Nat → Option α)
    (start fuel : Nat) : (pageScan lookup start fuel).length ≤ fuel := by
  induction fuel generalizing start with
  | zero => simp [pageScan]
  | succ n ih =>
      simp only [pageScan]
      cases lookup start <;> simp only [List.length_cons]
      · exact Nat.le_trans (ih (start + 1)) (Nat.le_succ n)
      · exact Nat.succ_le_succ (ih (start + 1))

theorem pageScan_member {α : Type} (lookup : Nat → Option α)
    (start fuel id : Nat) (value : α)
    (h : (id, value) ∈ pageScan lookup start fuel) :
    start ≤ id ∧ id < start + fuel ∧ lookup id = some value := by
  induction fuel generalizing start with
  | zero => simp [pageScan] at h
  | succ n ih =>
      simp only [pageScan] at h
      cases hlookup : lookup start with
      | none =>
          simp only [hlookup] at h
          obtain ⟨hl, hu, hv⟩ := ih (start + 1) h
          exact ⟨by omega, by omega, hv⟩
      | some v =>
          simp only [hlookup, List.mem_cons] at h
          rcases h with h | h
          · cases h
            constructor
            · omega
            constructor
            · omega
            · exact hlookup
          · obtain ⟨hl, hu, hv⟩ := ih (start + 1) h
            exact ⟨by omega, by omega, hv⟩

theorem viewPage_overflow {α : Type} (lastId fromIndex limit : Nat)
    (lookup : Nat → Option α) (h : maxU64 < fromIndex + limit) :
    viewPage lastId fromIndex limit lookup = none := by
  simp [viewPage, h]

theorem viewPage_empty_beyond_end {α : Type} (lastId fromIndex limit : Nat)
    (lookup : Nat → Option α)
    (hl : lastId ≤ maxU64) (hf : fromIndex ≤ maxU64)
    (hm : limit ≤ maxU64) (hs : fromIndex + limit ≤ maxU64)
    (he : lastId ≤ fromIndex) :
    viewPage lastId fromIndex limit lookup = some [] := by
  simp [viewPage, show ¬lastId > maxU64 by omega,
    show ¬fromIndex > maxU64 by omega,
    show ¬limit > maxU64 by omega,
    show ¬fromIndex + limit > maxU64 by omega,
    show min lastId (fromIndex + limit) - fromIndex = 0 by omega,
    pageScan]

theorem viewPage_zero_limit {α : Type} (lastId fromIndex : Nat)
    (lookup : Nat → Option α)
    (hl : lastId ≤ maxU64) (hf : fromIndex ≤ maxU64) :
    viewPage lastId fromIndex 0 lookup = some [] := by
  simp [viewPage, show ¬lastId > maxU64 by omega,
    show ¬fromIndex > maxU64 by omega,
    show min lastId fromIndex - fromIndex = 0 by omega, pageScan]

theorem viewPage_member {α : Type} (lastId fromIndex limit : Nat)
    (lookup : Nat → Option α) (page : List (Nat × α))
    (hpage : viewPage lastId fromIndex limit lookup = some page)
    (id : Nat) (value : α) (hmem : (id, value) ∈ page) :
    fromIndex ≤ id ∧ id < lastId ∧ id < fromIndex + limit ∧
      lookup id = some value := by
  unfold viewPage at hpage
  split at hpage
  · contradiction
  · have heq : page = pageScan lookup fromIndex
        (min lastId (fromIndex + limit) - fromIndex) := by
      simpa only [Option.some.injEq] using hpage.symm
    rw [heq] at hmem
    obtain ⟨hl, hu, hv⟩ := pageScan_member lookup fromIndex
      (min lastId (fromIndex + limit) - fromIndex) id value hmem
    have hm : id < min lastId (fromIndex + limit) := by
      have : fromIndex ≤ min lastId (fromIndex + limit) := by omega
      omega
    exact ⟨hl, by omega, by omega, hv⟩

theorem viewPage_length_le_limit {α : Type} (lastId fromIndex limit : Nat)
    (lookup : Nat → Option α) (page : List (Nat × α))
    (hpage : viewPage lastId fromIndex limit lookup = some page) :
    page.length ≤ limit := by
  unfold viewPage at hpage
  split at hpage
  · contradiction
  · have hlen := pageScan_length_le lookup fromIndex
        (min lastId (fromIndex + limit) - fromIndex)
    have heq : page = pageScan lookup fromIndex
        (min lastId (fromIndex + limit) - fromIndex) := by
      simpa only [Option.some.injEq] using hpage.symm
    rw [heq]
    omega

example : viewPage 5 0 4
    (fun id => if id = 1 then some "one" else if id = 3 then some "three" else none) =
    some [(1, "one"), (3, "three")] := by decide

example : viewPage 1 maxU64 1 (fun _ => some "present") = none := by
  apply viewPage_overflow
  unfold maxU64
  omega

theorem viewLockedStorage_bounded (byteCost usage : Nat) :
    viewLockedStorage byteCost usage ≤ maxU128 := by
  exact Nat.min_le_left _ _

theorem viewLockedStorage_exact (byteCost usage : Nat)
    (h : byteCost * usage ≤ maxU128) :
    viewLockedStorage byteCost usage = byteCost * usage := by
  simp [viewLockedStorage, h]

theorem viewLockedStorage_saturated (byteCost usage : Nat)
    (h : maxU128 ≤ byteCost * usage) :
    viewLockedStorage byteCost usage = maxU128 := by
  simp [viewLockedStorage, h]

theorem viewAvailable_sub_total (balance byteCost usage lockedBonds : Nat) :
    viewAvailable balance byteCost usage lockedBonds =
      balance - (viewLockedStorage byteCost usage + lockedBonds) := by
  simp [viewAvailable, Nat.sub_sub]

theorem viewAvailable_exact (balance byteCost usage lockedBonds : Nat)
    (hproduct : byteCost * usage ≤ maxU128)
    (hfunds : byteCost * usage + lockedBonds ≤ balance) :
    viewAvailable balance byteCost usage lockedBonds +
        byteCost * usage + lockedBonds = balance := by
  rw [viewAvailable_sub_total, viewLockedStorage_exact _ _ hproduct]
  omega

theorem viewAvailable_zero (balance byteCost usage lockedBonds : Nat)
    (h : balance ≤ viewLockedStorage byteCost usage + lockedBonds) :
    viewAvailable balance byteCost usage lockedBonds = 0 := by
  rw [viewAvailable_sub_total]
  omega

theorem viewAvailable_le_balance (balance byteCost usage lockedBonds : Nat) :
    viewAvailable balance byteCost usage lockedBonds ≤ balance := by
  rw [viewAvailable_sub_total]
  omega

theorem viewOne_missing {α : Type} (id : Nat) :
    viewOne (α := α) id none = none := by rfl

theorem viewOne_present {α : Type} (id : Nat) (value : α) :
    viewOne id (some value) = some (id, value) := by rfl

theorem viewDefault_missing {α : Type} (default : α) :
    viewDefault default none = default := by rfl

theorem viewDelegationRatio_missing (total : Nat) :
    viewDelegationRatio none total = (0, total) := by rfl

theorem readPolicy_after_upgrade {α : Type} (makeDefault : List String → α)
    (stored : StoredPolicy α) :
    ∃ policy, readPolicy (some (upgradeStoredPolicy makeDefault stored)) = .ok policy := by
  cases stored <;> simp [upgradeStoredPolicy, readPolicy]

theorem readPolicy_current {α : Type} (policy : α) :
    readPolicy (some (.current policy)) = .ok policy := by rfl

theorem readPolicy_legacy {α : Type} (council : List String) :
    readPolicy (α := α) (some (.default council)) = .error .legacy := by rfl

theorem readPolicy_missing {α : Type} :
    readPolicy (α := α) none = .error .missing := by rfl

theorem viewStakingContract_missing :
    viewStakingContract none = "" := by rfl

theorem viewDelegationBalance_missing :
    viewDelegationBalance none = 0 := by rfl

theorem viewBountyClaims_missing {α : Type} :
    viewBountyClaims (α := α) none = [] := by rfl

theorem viewBountyClaimCount_missing :
    viewBountyClaimCount none = 0 := by rfl

theorem readConfig_missing {α : Type} :
    readConfig (α := α) none = none := by rfl

example : viewAvailable 10 3 5 2 = 0 := by decide
example : viewAvailable 30 3 5 2 = 13 := by decide

end SputnikDAO2
