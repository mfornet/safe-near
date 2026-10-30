import Bridge.Methods.FtTotalSupply

/-!
# `ft_total_supply` (296): the model's side of `Refines`

`ftTotalSupply_refines_wnear` leaves two hypotheses about the model: `hag` (the model's step
agrees with every final host `post` allows) and `hbound` (the model's gas bound covers loading
and the method's cost). This file discharges `hag` (`hag_wnear`) from what `Refines` provides:
the storage represents the model's state (`Represents`), the context is well formed
(`Context.WF`) and the host reads `S` (`pre`).

* `step_eq`: the model's step on `some S`: the JSON of `S.totalSupply` with no state change, no
  logs and no promises, or the storage-stake failure when the account cannot pay its storage.
* `quote_toString`: decimal digits need no JSON escaping, so `jsonU128 n` is `"` ++ digits ++ `"`;
  `supplyJson_eq_jsonU128`: the binary's return bytes are the model's.
* `finalStorage_hostOf`: the storage the VM hands back unchanged is `raw`.
* `post_field`: the fields `storage_read` and `value_return` leave alone.
* `hag_wnear`: the agreement.
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near NearLogic NearInterface ContractModel
open WNear.Binary.FtTotalSupply

/-! ## The model's step -/

/-- The storage-stake deficit the model computes for a call that keeps `S`. -/
def deficit (ctx : Context) (S : WNear.State) : Nat :=
  stakeDeficit ctx.protocol (WNear.usageAfter ctx (some S) S) (ctx.balance + ctx.attached) ctx.locked

/-- The model's step for `ft_total_supply` on the state `S`. -/
theorem step_eq (cfg : WNear.Config) (ctx : Context) (S : WNear.State) :
    (WNear.wnear cfg).step ctx (some S) .ftTotalSupply =
      if 0 < deficit ctx S then .error { failure := .lackBalanceForState (deficit ctx S), logs := [] }
      else .ok { state := S, ret := .u128 S.totalSupply, logs := [], promises := [] } := by
  rfl

/-! ## The JSON of a `u128` -/

theorem toDigits_digit (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, ∃ d < 10, c = Nat.digitChar d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · intro c hc; simp at hc; exact ⟨n, by omega, hc⟩
    · intro c hc
      simp at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · exact ⟨n % 10, by omega, hc⟩

theorem foldl_singleton (l : List Char) (acc : String) :
    List.foldl (fun r s => r ++ s) acc (l.map String.singleton) = acc ++ String.ofList l := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.foldl_cons, ih, String.append_assoc]
    congr 1
    apply String.toList_inj.1
    simp

theorem join_singleton (l : List Char) : String.join (l.map String.singleton) = String.ofList l := by
  rw [String.join, foldl_singleton]; simp

/-- Decimal digits need no escaping: `quote (toString n)` is `toString n` between quotes. -/
theorem quote_toString (n : Nat) : NearInterface.Json.quote (toString n) = "\"" ++ toString n ++ "\"" := by
  unfold NearInterface.Json.quote
  have e : toString n = String.ofList (Nat.toDigits 10 n) := rfl
  rw [e, String.toList_ofList]
  dsimp only
  congr 2
  rw [← join_singleton]
  congr 1
  apply List.map_congr_left
  intro c hc
  obtain ⟨d, hd, rfl⟩ := toDigits_digit n c hc
  interval_cases d <;> rfl

/-- The bytes of the model's `jsonU128 n`: `jsonOf n`. -/
theorem jsonU128_bytes (n : Nat) : (WNear.jsonU128 n).toUTF8.toList = jsonOf n := by
  rw [WNear.jsonU128, quote_toString, ToVec.json_bytes]
  rfl

/-- The supply in the header of `S` is the one in an equal header of a well-formed `S'`. -/
theorem supply_of_header {S S' : WNear.State} (hS' : S'.WF) (h : WNear.header S = WNear.header S') :
    S.totalSupply % 2 ^ 128 = S'.totalSupply := by
  simp only [WNear.header, List.append_assoc] at h
  have hparts := List.append_cancel_left h
  have hlen : (Borsh.u128 S.totalSupply).length = (Borsh.u128 S'.totalSupply).length := by
    simp only [Borsh.u128, Borsh.leBytes_length]
  have hs := congrArg Memory.decodeLE (List.append_inj_left hparts hlen)
  simp only [Borsh.u128, decodeLE_leBytes] at hs
  have hlt := hS'.totalSupply_lt
  simp only [u128Bound] at hlt
  rw [show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num] at hs
  rw [hs, Nat.mod_eq_of_lt hlt]

/-- The binary's return bytes are the model's. -/
theorem supplyJson_eq_jsonU128 {S S' : WNear.State} (hS' : S'.WF) (h : WNear.header S = WNear.header S') :
    supplyJson S = (WNear.jsonU128 S'.totalSupply).toUTF8.toList := by
  rw [jsonU128_bytes, supplyJson, supply_of_header hS' h]

/-! ## The initial host's storage -/

theorem accountKey_ne_stateKey (a : WNear.AccountId) : WNear.accountKey a ≠ WNear.stateKey := by
  intro h
  have e := congrArg List.length h
  have ha := a.property
  simp only [WNear.isValidAccountId, Bool.and_eq_true, decide_eq_true_eq] at ha
  simp only [WNear.accountKey, WNear.accountsPrefix, WNear.stateKey, Borsh.string, Borsh.bytes,
    Borsh.u32, List.length_append, Borsh.leBytes_length, Borsh.byteArray_toList_length] at e
  have hp : "a".toUTF8.size = 1 := by decide
  have hs : "STATE".toUTF8.size = 5 := by decide
  rw [hp, hs] at e
  change (2 ≤ a.val.toUTF8.size ∧ a.val.toUTF8.size ≤ 64) ∧ _ at ha
  omega

theorem mem_encode_state {s : WNear.State} {v : List UInt8} (h : (WNear.stateKey, v) ∈ WNear.encode s) :
    v = WNear.header s := by
  rcases Finset.mem_insert.mp h with h | h
  · exact congrArg Prod.snd h
  · obtain ⟨a, _, e⟩ := Finset.mem_image.mp h
    exact False.elim (accountKey_ne_stateKey a (congrArg Prod.fst e))

theorem hostOf_storage (ctx : Context) (raw : RawStorage) (k : List UInt8) :
    (hostOf ctx raw).storage k = (raw.toList.find? (·.1 == k)).map (·.2) := rfl

/-- The value the initial host reads under a key of `raw` is the one `raw` holds. -/
theorem hostOf_storage_mem {ctx : Context} {raw : RawStorage} {k : List UInt8} {v : List UInt8}
    (h : (hostOf ctx raw).storage k = some v) : (k, v) ∈ raw := by
  rw [hostOf_storage] at h
  cases hf : raw.toList.find? (·.1 == k) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hp := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    rw [Finset.mem_toList] at hp
    obtain ⟨k', v'⟩ := p
    simp only at hk h
    subst hk h
    exact hp

/-- The storage the VM hands back unchanged is `raw`. -/
theorem finalStorage_hostOf (ctx : Context) (raw : RawStorage)
    (huniq : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v') :
    (finalStorage (hostOf ctx raw)).toFinset = raw := by
  ext ⟨k, v⟩
  simp only [List.mem_toFinset, finalStorage, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨k', -, v', hv, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hostOf_storage_mem hv
  · intro hm
    refine ⟨k, ?_, v, ?_, rfl⟩
    · show k ∈ sortedKeys raw.toList
      rw [sortedKeys, List.mem_mergeSort]
      exact List.mem_map.2 ⟨(k, v), Finset.mem_toList.2 hm, rfl⟩
    · rw [hostOf_storage]
      cases hf : raw.toList.find? (·.1 == k) with
      | none =>
        have := List.find?_eq_none.1 hf (k, v) (Finset.mem_toList.2 hm)
        simp at this
      | some p =>
        have hp := Finset.mem_toList.1 (List.mem_of_find?_eq_some hf)
        have hk := List.find?_some hf
        simp only [beq_iff_eq] at hk
        obtain ⟨k', v'⟩ := p
        simp only at hk
        subst hk
        simp only [Option.map_some, Option.some.injEq]
        exact huniq _ _ _ hp hm

/-! ## The final host -/

/-- A field that erasure, `storage_read`'s register and accounting updates, and the return
selection leave alone is the initial host's. -/
theorem post_field {α : Type} (f : NearState → α) (hf : ∀ x, f (erase x) = f x)
    (hsel : ∀ x b, f (x.selectReturnValue b) = f x) (hreg : ∀ x i v, f (x.setRegister i v) = f x)
    (hacc : ∀ x a, f { x with storageAccounting := a } = f x)
    {S : WNear.State} {h0 e : NearState} (hp : post S h0 e) : f e = f h0 := by
  obtain ⟨st, h1, -, ⟨s2, -, -, he⟩, rfl⟩ := hp
  rw [hf, hsel, erase_field he f hf]
  unfold storageReadRegs
  split
  · split
    · exact hacc _ _
    · rw [hreg]; exact hacc _ _
  · exact hacc _ _

theorem post_returnData {S : WNear.State} {h0 e : NearState} (hp : post S h0 e) :
    e.returnData = some (supplyJson S) := by
  obtain ⟨st, h1, -, -, rfl⟩ := hp
  rfl

/-! ## The agreement -/

open WNear in
/-- **`hag` for `ft_total_supply`.** For a storage that represents `st` (`Represents`) in a well
formed context, where `STATE` holds `S`, the model's step agrees with every final host `post`
allows from the initial host `h0` (up to gas and the recorded proof): the return data is the JSON of the total supply, storage, balance and usage are
unchanged, no logs, and the storage-stake check decides success or failure the same way. -/
theorem hag_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (h0 : NearState) (hh0 : eraseP h0 = eraseP (hostOf ctx raw)) :
    ∀ e, post S h0 e →
      AgreesWith (wnear cfg) ctx raw e ((wnear cfg).step ctx st .ftTotalSupply) := by
  intro e hp
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (eraseP x) = f x) → f h0 = f (hostOf ctx raw) :=
    fun f hfe => eraseP_field hh0 f hfe
  -- the represented state
  cases st with
  | none =>
    have h0 : raw = ∅ := hrep
    rw [hostOf_storage, h0] at hval
    simp at hval
  | some S' =>
    obtain ⟨hinv, hraw⟩ := (show Inv cfg S' ∧ raw = encode S' from hrep)
    have hmem := hostOf_storage_mem hval
    rw [hraw] at hmem
    have hhd : WNear.header S = WNear.header S' := mem_encode_state hmem
    -- the final host's fields
    have hbal : e.context.accountBalance = ctx.balance + ctx.attached :=
      (post_field (fun x => x.context.accountBalance) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.accountBalance) fun _ => rfl)
    have hsu : e.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
      (post_field (fun x => x.context.storageUsage) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.storageUsage) fun _ => rfl)
    have hsto : e.storage = (hostOf ctx raw).storage :=
      (post_field NearState.storage (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storage fun _ => rfl)
    have hkeys : e.storageKeys = (hostOf ctx raw).storageKeys :=
      (post_field NearState.storageKeys (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storageKeys fun _ => rfl)
    have hlogs : e.logs = [] :=
      (post_field NearState.logs (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.logs fun _ => rfl)
    have hfin : finalStorage e = finalStorage (hostOf ctx raw) := by
      simp only [finalStorage, hsto, hkeys]
    have hroom := hwf.usage_room
    have hge := hwf.usage_ge
    have hsuN : e.context.storageUsage.toNat = ctx.storageUsage := by
      rw [hsu, UInt64.toNat_ofNat_of_lt' (by show _ < 2 ^ 64; omega)]
    have hafter : WNear.usageAfter ctx (some S') S' = ctx.storageUsage := by
      simp only [WNear.usageAfter, WNear.storageOf]
      rw [← hraw]
      omega
    have hdef : deficit ctx S' =
        stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked := by
      rw [deficit, hafter, hsuN, hbal]
    erw [step_eq]
    split
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact hpos, by rw [← hdef]; rfl, ?_⟩
      show [] = logsOf e
      simp [logsOf, hlogs]
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact Nat.eq_zero_of_not_pos hpos, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
      · show returnOf e = .value (WNear.jsonU128 S'.totalSupply).toUTF8.toList
        rw [returnOf, post_returnData hp, supplyJson_eq_jsonU128 hinv.toWF hhd]
      · show (finalStorage e).toFinset = encode S'
        rw [hfin, finalStorage_hostOf ctx raw hwf.raw_keys_unique, hraw]
      · exact hbal
      · show e.context.storageUsage.toNat = _ - _ + storageUsageOf ctx.protocol (encode S')
        rw [hsuN, ← hraw]
        omega
      · show logsOf e = []
        simp [logsOf, hlogs]

end WNear.Binary.FtTotalSupplyMethod
