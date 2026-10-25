import Mathlib.Data.List.Nodup
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

/-- The balance a gas key holds (zero for other keys). -/
def AccessKey.gasBalance (k : AccessKey) : Nat := ((k.permission.gasKeyInfo?).map (·.1)).getD 0

namespace ChainState

/-- Accounts and access keys are unique finite maps, and every access key belongs to an account;
the funds of accounts and of gas keys are sums over these maps. -/
def AccountsUnique (st : ChainState) : Prop :=
  Assoc.KeysUnique st.accounts ∧ Assoc.KeysUnique st.accessKeys ∧
    ∀ e ∈ st.accessKeys, (st.account? e.1.1).isSome = true

theorem AccountsUnique.accounts {st : ChainState} (h : st.AccountsUnique) : Assoc.KeysUnique st.accounts := h.1

theorem AccountsUnique.accessKeys {st : ChainState} (h : st.AccountsUnique) :
    Assoc.KeysUnique st.accessKeys := h.2.1

theorem AccountsUnique.owned {st : ChainState} (h : st.AccountsUnique) :
    ∀ e ∈ st.accessKeys, (st.account? e.1.1).isSome = true := h.2.2

theorem account?_isSome_setAccount (st : ChainState) (id x : AccountId) (a : Account)
    (h : x = id ∨ (st.account? x).isSome = true) : ((st.setAccount id a).account? x).isSome = true := by
  by_cases hx : id = x
  · subst hx
    simp [setAccount, account?, Assoc.lookup_insert_self]
  · have hne := Assoc.lookup_insert_ne st.accounts id x a hx
    have : (st.setAccount id a).account? x = st.account? x := hne
    rw [this]
    rcases h with h | h
    · exact absurd h.symm hx
    · exact h

theorem AccountsUnique.setAccount {st : ChainState} (h : st.AccountsUnique)
    (id : AccountId) (a : Account) : (st.setAccount id a).AccountsUnique :=
  ⟨h.1.insert id a, h.2.1, fun e he => account?_isSome_setAccount st id e.1.1 a (Or.inr (h.2.2 e he))⟩

theorem AccountsUnique.removeAccount {st : ChainState} (h : st.AccountsUnique)
    (id : AccountId) : (st.removeAccount id).AccountsUnique := by
  refine ⟨h.1.erase id, h.2.1.filter (fun entry => entry.1.1 != id), fun e he => ?_⟩
  have hm : e ∈ st.accessKeys := (List.mem_filter.mp he).1
  have hne : (e.1.1 != id) = true := (List.mem_filter.mp he).2
  have hne' : id ≠ e.1.1 := by
    intro heq; subst heq; simp at hne
  have hl : Assoc.lookup (Assoc.erase st.accounts id) e.1.1 = Assoc.lookup st.accounts e.1.1 :=
    Assoc.lookup_erase_ne _ _ _ hne'
  have := h.2.2 e hm
  change (Assoc.lookup (Assoc.erase st.accounts id) e.1.1).isSome = true
  rw [hl]
  exact this

theorem AccountsUnique.setAccessKey {st : ChainState} (h : st.AccountsUnique)
    (id : AccountId) (pk : PublicKey) (key : AccessKey) (hacc : (st.account? id).isSome = true) :
    (st.setAccessKey id pk key).AccountsUnique := by
  refine ⟨h.1, h.2.1.insert (id, pk) key, fun e he => ?_⟩
  change e ∈ Assoc.insert st.accessKeys (id, pk) key at he
  unfold Assoc.insert at he
  rcases List.mem_cons.mp he with heq | hm
  · subst heq; exact hacc
  · exact h.2.2 e (List.mem_filter.mp hm).1

theorem AccountsUnique.removeAccessKey {st : ChainState} (h : st.AccountsUnique)
    (id : AccountId) (pk : PublicKey) : (st.removeAccessKey id pk).AccountsUnique := by
  refine ⟨h.1, h.2.1.erase (id, pk), fun e he => ?_⟩
  change e ∈ Assoc.erase st.accessKeys (id, pk) at he
  exact h.2.2 e (List.mem_filter.mp he).1

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
    (id : AccountId) (pk : PublicKey) (key : AccessKey) (hacc : (st.account? id).isSome = true) :
    (st.setAccessKey id pk key).MapsUnique :=
  { h with accounts := h.accounts.setAccessKey id pk key hacc
           accessKeys := h.accessKeys.insert (id, pk) key }

theorem MapsUnique.removeAccessKey {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) (pk : PublicKey) : (st.removeAccessKey id pk).MapsUnique :=
  { h with accounts := h.accounts.removeAccessKey id pk
           accessKeys := h.accessKeys.erase (id, pk) }

theorem MapsUnique.setContractStorage {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) (entries : List (Bytes × Bytes)) : (st.setContractStorage id entries).MapsUnique :=
  { h with storage := h.storage.insert id entries }

theorem MapsUnique.removeAccount {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) : (st.removeAccount id).MapsUnique :=
  { h with accounts := h.accounts.removeAccount id
           accessKeys := h.accessKeys.filter (fun entry => entry.1.1 != id)
           storage := h.storage.erase id }

theorem MapsUnique.freshId {st : ChainState} (h : st.MapsUnique) : st.freshId.2.MapsUnique :=
  { h with }

theorem account?_setAccount_self (st : ChainState) (id : AccountId) (a : Account) :
    (st.setAccount id a).account? id = some a := Assoc.lookup_insert_self _ _ _

theorem account?_setAccount_ne (st : ChainState) (id other : AccountId) (a : Account)
    (hne : id ≠ other) : (st.setAccount id a).account? other = st.account? other :=
  Assoc.lookup_insert_ne _ _ _ _ hne

theorem gasKeyFunds_eq_mass (st : ChainState) :
    st.gasKeyFunds = Assoc.mass AccessKey.gasBalance st.accessKeys := rfl

@[simp] theorem gasKeyFunds_setAccount (st : ChainState) (id : AccountId) (a : Account) :
    (st.setAccount id a).gasKeyFunds = st.gasKeyFunds := rfl

@[simp] theorem gasKeyFunds_freshId (st : ChainState) : st.freshId.2.gasKeyFunds = st.gasKeyFunds := rfl

theorem gasKeyFunds_setAccessKey (st : ChainState) (id : AccountId) (pk : PublicKey) (k : AccessKey)
    (h : Assoc.KeysUnique st.accessKeys) :
    (st.setAccessKey id pk k).gasKeyFunds + ((st.accessKey? id pk).map AccessKey.gasBalance).getD 0 =
      st.gasKeyFunds + k.gasBalance :=
  Assoc.mass_insert_accounting AccessKey.gasBalance st.accessKeys (id, pk) k h

theorem gasKeyFunds_removeAccessKey (st : ChainState) (id : AccountId) (pk : PublicKey)
    (h : Assoc.KeysUnique st.accessKeys) :
    (st.removeAccessKey id pk).gasKeyFunds + ((st.accessKey? id pk).map AccessKey.gasBalance).getD 0 =
      st.gasKeyFunds :=
  Assoc.mass_erase_lookup AccessKey.gasBalance st.accessKeys (id, pk) h

/-- Removing an account removes exactly the gas key balances it held. -/
theorem gasKeyFunds_removeAccount (st : ChainState) (id : AccountId) :
    (st.removeAccount id).gasKeyFunds + st.gasKeyBalances id = st.gasKeyFunds := by
  unfold gasKeyFunds gasKeyBalances removeAccount
  dsimp only
  have key : ∀ (l : List ((AccountId × PublicKey) × AccessKey)) (acc : Nat),
      (l.filter (·.1.1 == id)).foldl (fun total e => total + ((e.2.permission.gasKeyInfo?).map (·.1)).getD 0) acc
        + ((l.filter (·.1.1 != id)).map fun entry => ((entry.2.permission.gasKeyInfo?).map (·.1)).getD 0).sum
      = acc + (l.map fun entry => ((entry.2.permission.gasKeyInfo?).map (·.1)).getD 0).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons e rest ih =>
      intro acc
      by_cases he : (e.1.1 == id) = true
      · have hne : (e.1.1 != id) = false := by simpa using he
        simp only [List.filter_cons, he, hne, List.map_cons, List.sum_cons]
        have := ih (acc + ((e.2.permission.gasKeyInfo?).map (·.1)).getD 0)
        simp at this ⊢
        omega
      · have hne : (e.1.1 != id) = true := by simpa using he
        simp only [List.filter_cons, he, hne, List.map_cons, List.sum_cons]
        have := ih acc
        simp at this ⊢
        omega
  have := key st.accessKeys 0
  omega

theorem totalBalance_setAccount (st : ChainState) (id : AccountId) (a old : Account)
    (h : st.AccountsUnique) (hold : st.account? id = some old) :
    (st.setAccount id a).totalBalance + old.amount + old.locked =
      st.totalBalance + a.amount + a.locked := by
  have hm := Assoc.mass_insert_accounting (fun a : Account => a.amount + a.locked)
    st.accounts id a h.accounts
  change Assoc.lookup st.accounts id = some old at hold
  simp only [hold, Option.map_some, Option.getD_some] at hm
  have hg := gasKeyFunds_setAccount st id a
  unfold totalBalance
  rw [hg]
  simp only [setAccount, Assoc.mass] at hm ⊢
  omega

/-- Removing an account removes the balances of its gas keys with it. -/
theorem totalBalance_removeAccount (st : ChainState) (id : AccountId) (old : Account)
    (h : st.AccountsUnique) (hold : st.account? id = some old) :
    (st.removeAccount id).totalBalance + old.amount + old.locked + st.gasKeyBalances id = st.totalBalance := by
  have hm := Assoc.mass_erase_lookup (fun a : Account => a.amount + a.locked) st.accounts id h.accounts
  change Assoc.lookup st.accounts id = some old at hold
  simp only [hold, Option.map_some, Option.getD_some] at hm
  have hg := gasKeyFunds_removeAccount st id
  unfold totalBalance
  simp only [removeAccount, Assoc.mass] at hm hg ⊢
  omega

/-- Replacing a key by one that holds the same gas balance moves no funds. -/
theorem totalBalance_setAccessKey_same (st : ChainState) (id : AccountId) (pk : PublicKey) (k key : AccessKey)
    (h : st.AccountsUnique) (hk : st.accessKey? id pk = some key) (hb : k.gasBalance = key.gasBalance) :
    (st.setAccessKey id pk k).totalBalance = st.totalBalance := by
  have hg := gasKeyFunds_setAccessKey st id pk k h.accessKeys
  rw [hk] at hg
  simp only [Option.map_some, Option.getD_some] at hg
  unfold totalBalance
  have hacc : (st.setAccessKey id pk k).accounts = st.accounts := rfl
  rw [hacc]
  omega

/-- Adding a key with no gas balance moves no funds. -/
theorem totalBalance_setAccessKey_new (st : ChainState) (id : AccountId) (pk : PublicKey) (k : AccessKey)
    (h : st.AccountsUnique) (hk : st.accessKey? id pk = none) (hb : k.gasBalance = 0) :
    (st.setAccessKey id pk k).totalBalance = st.totalBalance := by
  have hg := gasKeyFunds_setAccessKey st id pk k h.accessKeys
  rw [hk] at hg
  simp only [Option.map_none, Option.getD_none] at hg
  unfold totalBalance
  have hacc : (st.setAccessKey id pk k).accounts = st.accounts := rfl
  rw [hacc]
  omega

/-- Removing a key takes its gas balance out of the funds. -/
theorem totalBalance_removeAccessKey (st : ChainState) (id : AccountId) (pk : PublicKey) (key : AccessKey)
    (h : st.AccountsUnique) (hk : st.accessKey? id pk = some key) :
    (st.removeAccessKey id pk).totalBalance + key.gasBalance = st.totalBalance := by
  have hg := gasKeyFunds_removeAccessKey st id pk h.accessKeys
  rw [hk] at hg
  simp only [Option.map_some, Option.getD_some] at hg
  unfold totalBalance
  have hacc : (st.removeAccessKey id pk).accounts = st.accounts := rfl
  rw [hacc]
  omega

/-- Balances depend only on the account and access key maps. -/
theorem totalBalance_congr {st st' : ChainState} (h1 : st.accounts = st'.accounts)
    (h2 : st.accessKeys = st'.accessKeys) : st.totalBalance = st'.totalBalance := by
  unfold totalBalance gasKeyFunds
  rw [h1, h2]

theorem AccountsUnique.congr {st st' : ChainState} (h1 : st.accounts = st'.accounts)
    (h2 : st.accessKeys = st'.accessKeys) (h : st.AccountsUnique) : st'.AccountsUnique := by
  unfold AccountsUnique account? at *
  rw [← h1, ← h2]
  exact h

/-- Writing nonce lanes leaves the account and access key maps alone. -/
theorem foldl_setGasKeyNonce_frame (id : AccountId) (pk : PublicKey) (nonce : Nat) (lanes : List Nat)
    (st : ChainState) :
    (lanes.foldl (fun st lane => st.setGasKeyNonce id pk lane nonce) st).accounts = st.accounts ∧
      (lanes.foldl (fun st lane => st.setGasKeyNonce id pk lane nonce) st).accessKeys = st.accessKeys := by
  induction lanes generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons lane rest ih =>
    have := ih (st.setGasKeyNonce id pk lane nonce)
    exact this

theorem totalBalance_removeGasKeyNonces (st : ChainState) (id : AccountId) (pk : PublicKey) :
    (st.removeGasKeyNonces id pk).totalBalance = st.totalBalance := totalBalance_congr rfl rfl

theorem AccountsUnique.removeGasKeyNonces {st : ChainState} (h : st.AccountsUnique) (id : AccountId)
    (pk : PublicKey) : (st.removeGasKeyNonces id pk).AccountsUnique := h

/-- An absent account owns no access key. -/
theorem accessKey_none_of_account_none {st : ChainState} (h : st.AccountsUnique) (id : AccountId)
    (pk : PublicKey) (ha : st.account? id = none) : st.accessKey? id pk = none := by
  unfold accessKey? Assoc.lookup
  cases hf : st.accessKeys.find? (·.1 == (id, pk)) with
  | none => rfl
  | some entry =>
    exfalso
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have heq : entry.1 = (id, pk) := eq_of_beq hp
    have := h.owned entry hm
    rw [heq] at this
    simp [ha] at this

/-- A present access key belongs to an existing account. -/
theorem account_of_accessKey {st : ChainState} (h : st.AccountsUnique) (id : AccountId) (pk : PublicKey)
    (key : AccessKey) (hk : st.accessKey? id pk = some key) : (st.account? id).isSome = true := by
  cases ha : st.account? id with
  | none => rw [accessKey_none_of_account_none h id pk ha] at hk; simp at hk
  | some _ => rfl

theorem accountsUnique_setAccount_new_key {st : ChainState} (h : st.AccountsUnique) (id : AccountId)
    (a : Account) (pk : PublicKey) (key : AccessKey) :
    ((st.setAccount id a).setAccessKey id pk key).AccountsUnique :=
  (h.setAccount id a).setAccessKey id pk key (account?_isSome_setAccount st id id a (Or.inl rfl))

end ChainState
end Near
