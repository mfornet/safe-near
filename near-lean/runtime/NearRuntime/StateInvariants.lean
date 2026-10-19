import NearRuntime.State

/-! Unique finite maps and balance accounting for the executable state operations.
These are structural map invariants, not yet a full receipt-graph invariant. -/
namespace Near
namespace Assoc

variable {κ α : Type} [BEq κ] [LawfulBEq κ]

def KeysUnique (m : List (κ × α)) : Prop := (m.map Prod.fst).Nodup

def mass (weight : α → Nat) (m : List (κ × α)) : Nat :=
  (m.map fun entry => weight entry.2).sum

omit [LawfulBEq κ] in
theorem keys_erase (m : List (κ × α)) (k : κ) :
    (erase m k).map Prod.fst = (m.map Prod.fst).filter (· != k) := by
  induction m with
  | nil => rfl
  | cons entry rest ih =>
    simp only [erase, List.filter_cons, List.map_cons] at *
    split <;> simp_all

omit [LawfulBEq κ] in
theorem KeysUnique.erase {m : List (κ × α)} (h : KeysUnique m) (k : κ) :
    KeysUnique (Assoc.erase m k) := by
  simpa only [KeysUnique, keys_erase] using h.filter (fun key => key != k)

theorem KeysUnique.insert {m : List (κ × α)} (h : KeysUnique m) (k : κ) (v : α) :
    KeysUnique (Assoc.insert m k v) := by
  change (k :: (Assoc.erase m k).map Prod.fst).Nodup
  apply List.nodup_cons.mpr
  constructor
  · simp [keys_erase]
  · exact h.erase k

omit [BEq κ] [LawfulBEq κ] in
theorem KeysUnique.filter {m : List (κ × α)} (h : KeysUnique m) (p : κ × α → Bool) :
    KeysUnique (m.filter p) :=
  (List.filter_sublist.map Prod.fst).nodup h

theorem lookup_insert_self (m : List (κ × α)) (k : κ) (v : α) :
    lookup (insert m k v) k = some v := by
  simp [lookup, insert]

theorem lookup_erase_ne (m : List (κ × α)) (k q : κ) (hne : k ≠ q) :
    lookup (erase m k) q = lookup m q := by
  induction m with
  | nil => rfl
  | cons entry rest ih =>
    by_cases hk : entry.1 = k <;> by_cases hq : entry.1 = q <;>
      simp_all [erase, lookup]

theorem lookup_insert_ne (m : List (κ × α)) (k q : κ) (v : α) (hne : k ≠ q) :
    lookup (insert m k v) q = lookup m q := by
  have hh : lookup ((k, v) :: erase m k) q = lookup (erase m k) q := by
    simp [lookup, hne]
  exact hh.trans (lookup_erase_ne m k q hne)

theorem lookup_none_of_key_not_mem (m : List (κ × α)) (k : κ)
    (h : k ∉ m.map Prod.fst) : lookup m k = none := by
  cases hf : m.find? (·.1 == k) with
  | none => simp [lookup, hf]
  | some entry =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have hk : entry.1 = k := eq_of_beq hp
    exact False.elim (h (List.mem_map.mpr ⟨entry, hm, hk⟩))

theorem mass_erase_lookup (weight : α → Nat) (m : List (κ × α)) (k : κ)
    (h : KeysUnique m) :
    mass weight (erase m k) + ((lookup m k).map weight).getD 0 = mass weight m := by
  induction m with
  | nil => rfl
  | cons entry rest ih =>
    have hn : entry.1 ∉ rest.map Prod.fst ∧ KeysUnique rest := by
      simpa [KeysUnique] using h
    by_cases he : entry.1 = k
    · subst k
      have hl := lookup_none_of_key_not_mem rest entry.1 hn.1
      have ht := ih hn.2
      simp [hl] at ht
      simp only [mass, erase] at ht
      simp [mass, erase, lookup]
      omega
    · have ht := ih hn.2
      simp [mass, erase, lookup, he] at ht ⊢
      omega

theorem mass_insert_accounting (weight : α → Nat) (m : List (κ × α)) (k : κ) (v : α)
    (h : KeysUnique m) :
    mass weight (insert m k v) + ((lookup m k).map weight).getD 0 = mass weight m + weight v := by
  have he := mass_erase_lookup weight m k h
  change weight v + mass weight (erase m k) + _ = _
  omega

end Assoc

namespace ChainState

def AccountsUnique (st : ChainState) : Prop := Assoc.KeysUnique st.accounts

theorem AccountsUnique.setAccount {st : ChainState} (h : st.AccountsUnique)
    (id : AccountId) (a : Account) : (st.setAccount id a).AccountsUnique :=
  h.insert id a

theorem AccountsUnique.removeAccount {st : ChainState} (h : st.AccountsUnique)
    (id : AccountId) : (st.removeAccount id).AccountsUnique := h.erase id

/-- Uniqueness of every finite-map key domain in the executable state.
Receipt consistency, numeric bounds and identifier freshness are separate obligations. -/
structure MapsUnique (st : ChainState) : Prop where
  accounts : st.AccountsUnique
  accessKeys : Assoc.KeysUnique st.accessKeys
  storage : Assoc.KeysUnique st.storage
  postponed : Assoc.KeysUnique st.postponed
  pendingDataCount : Assoc.KeysUnique st.pendingDataCount
  postponedByData : Assoc.KeysUnique st.postponedByData
  receivedData : Assoc.KeysUnique st.receivedData

theorem MapsUnique.setAccount {st : ChainState} (h : st.MapsUnique) (id : AccountId) (a : Account) :
    (st.setAccount id a).MapsUnique :=
  { h with accounts := h.accounts.setAccount id a }

theorem MapsUnique.setAccessKey {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) (pk : PublicKey) (key : AccessKey) : (st.setAccessKey id pk key).MapsUnique :=
  { h with accessKeys := h.accessKeys.insert (id, pk) key }

theorem MapsUnique.removeAccessKey {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) (pk : PublicKey) : (st.removeAccessKey id pk).MapsUnique :=
  { h with accessKeys := h.accessKeys.erase (id, pk) }

theorem MapsUnique.setContractStorage {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) (entries : List (Bytes × Bytes)) : (st.setContractStorage id entries).MapsUnique :=
  { h with storage := h.storage.insert id entries }

theorem MapsUnique.removeAccount {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) : (st.removeAccount id).MapsUnique :=
  { h with accounts := h.accounts.removeAccount id
           accessKeys := h.accessKeys.filter (fun entry => entry.1.1 != id)
           storage := h.storage.erase id }

theorem MapsUnique.freshId {st : ChainState} (h : st.MapsUnique) : st.freshId.2.MapsUnique :=
  { h with accounts := h.accounts }

theorem account?_setAccount_self (st : ChainState) (id : AccountId) (a : Account) :
    (st.setAccount id a).account? id = some a := Assoc.lookup_insert_self _ _ _

theorem account?_setAccount_ne (st : ChainState) (id other : AccountId) (a : Account)
    (hne : id ≠ other) : (st.setAccount id a).account? other = st.account? other :=
  Assoc.lookup_insert_ne _ _ _ _ hne

theorem totalBalance_setAccount (st : ChainState) (id : AccountId) (a old : Account)
    (h : st.AccountsUnique) (hold : st.account? id = some old) :
    (st.setAccount id a).totalBalance + old.amount + old.locked =
      st.totalBalance + a.amount + a.locked := by
  have hm := Assoc.mass_insert_accounting (fun a : Account => a.amount + a.locked)
    st.accounts id a h
  change Assoc.lookup st.accounts id = some old at hold
  simp only [hold, Option.map_some, Option.getD_some] at hm
  simpa only [totalBalance, setAccount, Assoc.mass, Nat.add_assoc] using hm

theorem totalBalance_removeAccount (st : ChainState) (id : AccountId) (old : Account)
    (h : st.AccountsUnique) (hold : st.account? id = some old) :
    (st.removeAccount id).totalBalance + old.amount + old.locked = st.totalBalance := by
  have hm := Assoc.mass_erase_lookup (fun a : Account => a.amount + a.locked) st.accounts id h
  change Assoc.lookup st.accounts id = some old at hold
  simpa only [hold, Option.map_some, Option.getD_some, totalBalance, removeAccount,
    Assoc.mass, Nat.add_assoc] using hm

end ChainState
end Near
