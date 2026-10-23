import Model.Boundary.Contract
import Model.Methods
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-!
# The boundary model projects onto the abstract model

`Model/Methods.lean` models linkdrop with abstract keys and a functional map;
`Model/Boundary` models the binary, with public keys and the map in vector
order. Under any injective numbering of public keys, a method of the boundary
model is the abstract method (`body_project`): same failure, same map, same
receipts and same return value. The abstract model's properties
(`Proofs/Safety.lean`, `Proofs/Economics.lean`, ...) are therefore properties
of the model the binary is checked against.

The projection needs the stored keys to be distinct (the boundary `Inv`) and
the signer key to parse; the boundary model's own extras, the metadata
exports and an unparsable signer key, have no abstract counterpart.
-/

namespace Linkdrop.Boundary

open Function

variable (keyId : PublicKey → Key)

/-- The abstract map of a list of entries: the first entry with the key. -/
def lookup (l : List (PublicKey × Nat)) (j : Key) : Option Nat :=
  (l.find? fun e => keyId e.1 == j).map (·.2)

/-- The abstract state of a boundary map. -/
def Map.abs (m : Map) : Linkdrop.State := ⟨true, lookup keyId m.entries⟩

theorem lookup_cons (e : PublicKey × Nat) (l : List (PublicKey × Nat)) (j : Key) :
    lookup keyId (e :: l) j = if keyId e.1 = j then some e.2 else lookup keyId l j := by
  unfold lookup
  by_cases h : keyId e.1 = j <;> simp [h]

private theorem if_neg' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem lookup_none {l : List (PublicKey × Nat)} {j : Key} (h : ∀ e ∈ l, keyId e.1 ≠ j) :
    lookup keyId l j = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [lookup_cons, if_neg' (h e (by simp)), ih fun x hx => h x (by simp [hx])]

/-- Keys distinct (injectively numbered): the lookup ignores the order. -/
theorem lookup_perm (hinj : Injective keyId) {l l' : List (PublicKey × Nat)}
    (hnd : (l.map (·.1)).Nodup) (hp : l.Perm l') (j : Key) : lookup keyId l j = lookup keyId l' j := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    rw [lookup_cons, lookup_cons, ih (List.nodup_cons.mp hnd).2]
  | swap x y l =>
    rw [lookup_cons, lookup_cons, lookup_cons, lookup_cons]
    have hxy : x.1 ≠ y.1 := by
      intro he
      simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd
      exact hnd.1 (Or.inl he.symm)
    by_cases hx : keyId x.1 = j <;> by_cases hy : keyId y.1 = j
    · exact absurd (hinj (hx.trans hy.symm)) hxy
    all_goals simp [hx, hy]
  | trans h₁ _ ih₁ ih₂ =>
    rw [ih₁ hnd, ih₂ (hnd.perm (h₁.map _))]

theorem get_eq_lookup (hinj : Injective keyId) (m : Map) (k : PublicKey) :
    m.get k = lookup keyId m.entries (keyId k) := by
  unfold Map.get lookup
  congr 2
  funext e
  simp [hinj.eq_iff, Subtype.ext_iff]

theorem findIdx_none (m : Map) (k : PublicKey) (h : m.entries.findIdx? (·.1 == k) = none) :
    ∀ e ∈ m.entries, e.1 ≠ k := by
  intro e he hek
  have := List.findIdx?_eq_none_iff.mp h e he
  simp [hek] at this

theorem findIdx_some {m : Map} {k : PublicKey} {i : Nat} (h : m.entries.findIdx? (·.1 == k) = some i) :
    ∃ hi : i < m.entries.length, m.entries[i].1 = k := by
  obtain ⟨hi, hk, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, Subtype.ext (by simpa using hk)⟩

/-- `UnorderedMap::insert` is the abstract update. -/
theorem abs_insert (hinj : Injective keyId) (m : Map) (hnd : (m.entries.map (·.1)).Nodup)
    (k : PublicKey) (v : Nat) : (m.insert k v).abs keyId = (m.abs keyId).set (keyId k) (some v) := by
  unfold Map.insert Map.abs Linkdrop.State.set
  congr 1
  funext j
  dsimp only
  cases hf : m.entries.findIdx? (·.1 == k) with
  | none =>
    have hn := findIdx_none m k hf
    unfold lookup
    simp only [List.find?_append]
    by_cases hj : j = keyId k
    · subst hj
      have : m.entries.find? (fun e => keyId e.1 == keyId k) = none := by
        rw [List.find?_eq_none]
        intro e he
        simpa [hinj.eq_iff] using hn e he
      simp [this]
    · cases h : m.entries.find? (fun e => keyId e.1 == j) <;> simp [Ne.symm hj, hj]
  | some i =>
    obtain ⟨hi, hk⟩ := findIdx_some hf
    have hp := List.set_perm_cons_eraseIdx hi (k, v)
    have hp' := List.getElem_cons_eraseIdx_perm hi
    have hnd' : ((m.entries[i] :: m.entries.eraseIdx i).map (·.1)).Nodup := hnd.perm (hp'.symm.map _)
    have hnd'' : (((k, v) :: m.entries.eraseIdx i).map (·.1)).Nodup := by
      simpa [hk] using hnd'
    rw [lookup_perm keyId hinj (hnd''.perm ((hp.symm.map _))) hp,
      ← lookup_perm keyId hinj hnd' hp' j, lookup_cons, lookup_cons, hk]
    by_cases hj : j = keyId k
    · simp [hj]
    · simp [Ne.symm hj, hj]

/-- Swap removal, up to order, is removal of the entry. -/
theorem swapRemove_perm {l : List (PublicKey × Nat)} {i : Nat} (hi : i < l.length)
    {last : PublicKey × Nat} (hl : l.getLast? = some last) :
    ((l.set i last).dropLast).Perm (l.eraseIdx i) := by
  have hne : l ≠ [] := by rintro rfl; simp at hl
  obtain ⟨init, rfl⟩ : ∃ init, l = init ++ [last] :=
    ⟨l.dropLast, (List.dropLast_append_getLast? last (by simp [hl])).symm⟩
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlast : i = init.length
  · subst hlast
    simp [List.eraseIdx_append_of_length_le]
  · have hlt : i < init.length := by omega
    rw [List.set_append_left _ _ hlt, List.dropLast_append_of_ne_nil (by simp),
      List.dropLast_singleton, List.append_nil, List.eraseIdx_append_of_lt_length hlt]
    exact (List.set_perm_cons_eraseIdx hlt last).trans (List.perm_append_singleton _ _).symm

/-- `UnorderedMap::remove` of a stored key is the abstract removal. -/
theorem abs_remove (hinj : Injective keyId) (m : Map) (hnd : (m.entries.map (·.1)).Nodup)
    (k : PublicKey) (v : Nat) (hget : m.get k = some v) :
    (m.remove k).abs keyId = (m.abs keyId).set (keyId k) none := by
  have hf : m.entries.findIdx? (·.1 == k) ≠ none := by
    intro hn
    have hn := findIdx_none m k hn
    rw [get_eq_lookup keyId hinj, lookup_none keyId fun e he => by simpa [hinj.eq_iff] using hn e he] at hget
    cases hget
  obtain ⟨i, hfi⟩ := Option.ne_none_iff_exists'.mp hf
  obtain ⟨hi, hk⟩ := findIdx_some hfi
  have hne : m.entries ≠ [] := by intro h; simp [h] at hi
  obtain ⟨last, hl⟩ : ∃ last, m.entries.getLast? = some last :=
    ⟨m.entries.getLast hne, List.getLast?_eq_some_getLast hne⟩
  unfold Map.remove Map.abs Linkdrop.State.set
  simp only [hfi, hl]
  congr 1
  funext j
  have hp' := List.getElem_cons_eraseIdx_perm hi
  have hnd' : ((m.entries[i] :: m.entries.eraseIdx i).map (·.1)).Nodup := hnd.perm (hp'.symm.map _)
  have hndE : ((m.entries.eraseIdx i).map (·.1)).Nodup := (List.nodup_cons.mp hnd').2
  have hpr := swapRemove_perm hi hl
  rw [lookup_perm keyId hinj (hndE.perm (hpr.symm.map _)) hpr, ← lookup_perm keyId hinj hnd' hp' j,
    lookup_cons, hk]
  by_cases hj : j = keyId k
  · subst hj
    simp only [ite_true]
    apply lookup_none
    intro e he hek
    have hek := hinj hek
    simp only [List.map_cons, List.nodup_cons, hk] at hnd'
    exact hnd'.1 (List.mem_map.mpr ⟨e, he, hek⟩)
  · simp [Ne.symm hj, hj]

/-! ## Projections -/

def projectResult : Wasm.PromiseResult → Linkdrop.PromiseResult
  | .successful bytes => .successful bytes
  | .failed => .failed
  | .notReady => .notReady

/-- The abstract environment, for a parsed signer key. -/
def Env.project (e : Env) (signer : PublicKey) : Linkdrop.Env where
  current := e.current.val
  predecessor := e.predecessor.val
  signerKey := keyId signer
  deposit := e.deposit
  results := e.results.map projectResult

def LimitedKey.project (k : LimitedKey) : Linkdrop.LimitedKey :=
  ⟨keyId k.key, k.allowance, k.receiver.val, k.methods⟩

def Options.project (o : Options) : Linkdrop.Options where
  fullKeys := o.fullKeys.map (·.map keyId)
  limitedKeys := o.limitedKeys.map (·.map (LimitedKey.project keyId))
  bytes := o.bytes
  base64Bytes := o.base64Bytes
  globalHash := o.globalHash
  globalAccount := o.globalAccount.map (·.val)

/-- The abstract call; the metadata exports have none. -/
def Call.project : Call → Option Linkdrop.Call
  | .new => some .new
  | .send k => some (.send (keyId k))
  | .claim a => some (.claim a.val)
  | .createAndClaim a k => some (.createAndClaim a.val (keyId k))
  | .createAccount a k => some (.createAccount a.val (keyId k))
  | .createAdvanced a o => some (.createAdvanced a.val (o.project keyId))
  | .onCreated p n => some (.onCreated p.val n)
  | .onClaimed n => some (.onClaimed n)
  | .getBalance k => some (.getBalance (keyId k))
  | .getInformation k => some (.getInformation (keyId k))
  | .sourceMetadata | .abi => none

def Action.project : Action → Linkdrop.Action
  | .create => .create
  | .transfer n => .transfer n
  | .fullKey k => .fullKey (keyId k)
  | .limitedKey k allowance receiver methods => .limitedKey (keyId k) allowance receiver.val methods
  | .deleteKey k => .deleteKey (keyId k)
  | .deploy code => .deploy code
  | .globalHash hash => .globalHash hash
  | .globalAccount a => .globalAccount a.val
  | .onCreated p n => .onCreated p.val n Linkdrop.callbackGas Linkdrop.callbackWeight
  | .onClaimed n => .onClaimed n Linkdrop.callbackGas Linkdrop.callbackWeight

/-- Receipts, numbered: a receipt after the previous one waits on it. -/
def projectReceipts (rs : List Receipt) : List Linkdrop.Receipt :=
  rs.zipIdx.map fun (r, i) =>
    ⟨r.receiver.val, r.actions.map (Action.project keyId), if r.afterPrevious then some (i - 1) else none⟩

def Ret.project : Ret → Linkdrop.Return
  | .unit | .bytes _ => .unit
  | .bool b => .boolean b
  | .balance n => .balance n
  | .information n => .information n
  | .promise i => .promise i

/-- Panic sites the abstract model does not tell apart share a panic. -/
def Panic.project : Panic → Linkdrop.Panic
  | .initialized => .initialized
  | .uninitialized => .uninitialized
  | .deposit _ => .deposit
  | .privateCall _ => .privateCall
  | .zeroDeposit => .zeroDeposit
  | .claimMissing | .createAndClaimMissing | .balanceMissing | .informationMissing => .missingKey
  | .noOptions => .noOptions
  | .conflictingOptions => .conflictingOptions
  | .resultCount => .resultCount
  | .trap => .resultNotReady

def projectBody : Result → Except Linkdrop.Panic Linkdrop.Outcome
  | .error p => .error p.project
  | .ok (m, ret, rs) => .ok ⟨m.abs keyId, projectReceipts keyId rs, ret.project⟩

theorem options_project (o : Options) :
    (o.project keyId).present = o.present ∧ (o.project keyId).deployments = o.deployments ∧
      Linkdrop.optionActions (o.project keyId) = o.actions.map (Action.project keyId) := by
  refine ⟨?_, ?_, ?_⟩
  · cases o.fullKeys <;> cases o.limitedKeys <;> cases o.globalAccount <;>
      simp [Options.project, Options.present, Linkdrop.Options.present]
  · cases o.globalAccount <;> simp [Options.project, Options.deployments, Linkdrop.Options.deployments]
  · cases hf : o.fullKeys <;> cases hl : o.limitedKeys <;> cases hb : o.bytes <;> cases hb64 : o.base64Bytes <;>
      cases hh : o.globalHash <;> cases ha : o.globalAccount <;>
      simp [Options.project, Options.actions, Linkdrop.optionActions, Linkdrop.limitedAction,
        LimitedKey.project, Action.project, hf, hl, hb, hb64, hh, ha, Function.comp_def]
    all_goals intro _ _; rfl

theorem promiseSuccess_project (e : Env) (signer : PublicKey) :
    (match promiseSuccess e with
      | .ok b => Except.ok b
      | .error p => .error (Panic.project p)) =
    Linkdrop.callbackSuccess (Env.project keyId e signer) := by
  unfold promiseSuccess Linkdrop.callbackSuccess Env.project
  rcases e with ⟨_, _, _, _, results⟩
  rcases results with _ | ⟨r, _ | ⟨r2, rest⟩⟩
  · rfl
  · cases r <;> rfl
  · cases r <;> cases r2 <;> rfl

/-- **Projection.** For distinct stored keys, an injective key numbering and a
parsed signer key, the boundary method is the abstract method. -/
theorem body_project (hinj : Injective keyId) (m : Map) (hnd : (m.entries.map (·.1)).Nodup)
    (e : Env) (sk : PublicKey) (hsigner : e.signerKey = some sk)
    (c : Call) (ac : Linkdrop.Call) (hc : c.project keyId = some ac) :
    projectBody keyId (body m e c) = Linkdrop.body (m.abs keyId) (e.project keyId sk) ac := by
  have hs : signer e = .ok sk := by simp [Boundary.signer, hsigner]
  have hget (k : PublicKey) : (m.abs keyId).accounts (keyId k) = m.get k :=
    (get_eq_lookup keyId hinj m k).symm
  cases c <;> simp only [Call.project, Option.some.injEq] at hc <;> (first | subst hc | cases hc)
  · simp only [body, Linkdrop.body, projectBody, Map.abs, projectReceipts, Ret.project]
    congr 3
  · rename_i key
    simp only [body, Linkdrop.body, Env.project]
    by_cases hd : e.deposit = 0
    · simp [hd, projectBody, Panic.project]
    · simp [hd, projectBody, hget, abs_insert keyId hinj m hnd, projectReceipts, Action.project,
        Ret.project, keyAllowance, Linkdrop.keyAllowance, keyMethods, maxAmount, Linkdrop.maxAmount]
  · simp only [body, Linkdrop.body, hs, Env.project, hget, bind, Except.bind, pure, Except.pure]
    cases hg : m.get sk with
    | none => simp [projectBody, Panic.project]
    | some v =>
      simp [projectBody, abs_remove keyId hinj m hnd sk v hg, projectReceipts, Action.project,
        Ret.project]
  · simp only [body, Linkdrop.body, hs, Env.project, hget, bind, Except.bind, pure, Except.pure]
    cases hg : m.get sk with
    | none => simp [projectBody, Panic.project]
    | some v =>
      simp [projectBody, abs_remove keyId hinj m hnd sk v hg, projectReceipts, Action.project,
        Ret.project, Linkdrop.creation]
  · simp [body, Linkdrop.body, projectBody, projectReceipts, Action.project, Ret.project, Env.project,
      Linkdrop.creation]
  · rename_i account o
    obtain ⟨hp, hdep, hact⟩ := options_project keyId o
    simp only [body, Linkdrop.body, hp, hdep]
    by_cases h1 : o.present = false
    · simp [h1, projectBody, Panic.project]
    · by_cases h2 : o.deployments > 1
      · simp [h1, h2, projectBody, Panic.project]
      · simp [h1, h2, projectBody, projectReceipts, Action.project, Ret.project, Env.project, hact,
          Linkdrop.creation]
  · rename_i predecessor amount
    have hps := promiseSuccess_project keyId e sk
    simp only [body, Linkdrop.body, bind, Except.bind, pure, Except.pure]
    cases hr : promiseSuccess e with
    | error p => rw [hr] at hps; simp [← hps, projectBody]
    | ok b =>
      rw [hr] at hps
      rw [← hps]
      cases b <;> simp [projectBody, projectReceipts, Action.project, Ret.project]
  · rename_i amount
    have hps := promiseSuccess_project keyId e sk
    simp only [body, Linkdrop.body, bind, Except.bind, pure, Except.pure, hs]
    cases hr : promiseSuccess e with
    | error p => rw [hr] at hps; simp [← hps, projectBody]
    | ok b =>
      rw [hr] at hps
      rw [← hps]
      cases b
      · simp [projectBody, projectReceipts, Ret.project, Env.project, abs_insert keyId hinj m hnd]
      · simp [projectBody, projectReceipts, Action.project, Ret.project, Env.project]
  · simp only [body, Linkdrop.body, hget]
    cases m.get _ <;> simp [projectBody, Panic.project, Ret.project, projectReceipts]
  · simp only [body, Linkdrop.body, hget]
    cases m.get _ <;> simp [projectBody, Panic.project, Ret.project, projectReceipts]

end Linkdrop.Boundary
