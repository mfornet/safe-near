import Bridge.Methods.HostStorage
import Bridge.Methods.FtTotalSupplyRefines

/-!
# `ft_total_supply` (296): the host reads the model state

`pre_of_ctx` discharges `hpre` and `hpreP` of `ftTotalSupply_refines_v86'` from the context:
when `STATE` holds `header S`, the initial host meets `ReadOk` with the context's trie.

* The trie is canonical, has no witness hashing to zero, and is linked to the host's storage
  through the overlay's view (`Context.WF`, `hostOf_storage_view`).
* The recorded proof has room for the `STATE` lookup: `Context.WF.proof_growth` bounds what
  it may record, and `ProofRoom` for the model's bound leaves room for it (`budget_of_room`,
  `lookup_le_proofBound`). The host recording no proof (`eraseP`) has room trivially.
* The key, register and return limits hold under protocol 86's (`LimitsV86`).
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near NearLogic NearInterface WNear.Binary FtTotalSupply

/-- Protocol 86's limits on storage keys, registers, returned data and the total log length, as
lower bounds. -/
structure LimitsV86 (p : RuntimeConfig) : Prop where
  storageKey : 2048 ≤ p.wasm.limits.maxLengthStorageKey
  register : 104857600 ≤ p.wasm.limits.maxRegisterSize
  returned : 4194304 ≤ p.wasm.limits.maxLengthReturnedData
  totalLog : 16384 ≤ p.wasm.limits.maxTotalLogLength

/-- A host recording the context's proof, within the per-receipt limit, has the room
`ProofRoom` leaves. -/
theorem budget_of_room {ctx : Context} {raw : RawStorage} (hwf : ctx.WF raw) {b : Nat}
    (hroom : ctx.ProofRoom b) (h : NearState) (hs : h.storageProofSize = ctx.storageProofSize)
    (hc : h.config.maxStorageProofSize = ctx.protocol.wasm.limits.perReceiptStorageProofSizeLimit) :
    ProofBudget h ctx.trie b := by
  intro size hsz t c hr hcb
  rw [hs] at hsz
  rw [hc]
  have := hwf.proof_growth size hsz t c hr
  have := hroom size hsz
  omega

theorem lookupProofBoundLen_mono {m n : Nat} (h : m ≤ n) :
    Near.TrieOverlay.lookupProofBoundLen m ≤ Near.TrieOverlay.lookupProofBoundLen n := by
  unfold Near.TrieOverlay.lookupProofBoundLen
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The `STATE` lookup is within the model's proof bound. -/
theorem lookup_le_proofBound (ctx : Context) :
    Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey) ≤
      WNear.proofBound ctx := by
  have hl : (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey).length =
      ctx.current.bytes.length + 7 := by
    have h5 : WNear.stateKey.length = 5 := by rw [← StateRead.stateKey_eq]; rfl
    simp only [Near.TrieOverlay.contractKey, List.length_append, h5, List.length_singleton]
    omega
  have hm := lookupProofBoundLen_mono (show ctx.current.bytes.length + 7 ≤
    2 + ctx.current.bytes.length + WNear.maxStorageKeyBytes by simp [WNear.maxStorageKeyBytes]; omega)
  unfold Near.TrieOverlay.lookupProofBound WNear.proofBound
  rw [hl]
  simp only [WNear.storageAccesses]
  omega

/-- A host equal to the initial one up to gas and the recorded proof, with room for the
`STATE` lookup, reads the model state `S` that `STATE` holds. -/
theorem readOk_of (ctx : Context) (raw : RawStorage) (S : WNear.State) (hwf : ctx.WF raw)
    (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie
      (Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey))) :
    ReadOk h S ctx.trie := by
  have hsto : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  have hacc : h.storageAccounting = some ctx.trie :=
    eraseP_field he NearState.storageAccounting fun _ => rfl
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x => x.context.currentAccountId) fun _ => rfl
  have hlim : ∀ (f : NearConfig → Option Nat) (n m : Nat), f (hostOf ctx raw).config = some m → n ≤ m →
      withinLimit (f h.config) n = true := by
    intro f n m hf hn
    rw [hcfg, hf]
    simpa [withinLimit] using hn
  refine ⟨?_, hacc, ?_, hwf.trie_canonical, hwf.trie_no_zero_hash, ?_, ?_, ?_, ?_⟩
  · rw [hsto]; exact hval
  · exact hlim NearConfig.maxStorageKeyLen 5 _ rfl (by have := hl.storageKey; omega)
  · rw [hsto, hid]
    exact hostOf_storage_view ctx raw hwf WNear.stateKey
  · rw [hid]; exact hproof
  · exact hlim NearConfig.maxRegisterLen 29 _ rfl (by have := hl.register; omega)
  · exact hlim NearConfig.maxReturnLen _ _ rfl (by have := hl.returned; have := supplyJson_length S; omega)

/-- **`hpre` and `hpreP` of `ft_total_supply`**, from the context: when `STATE` holds
`header S`, the initial host reads `S` given room for the model's proof bound, and the host
recording no proof reads `S` always. -/
theorem pre_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) :
    (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) → pre S (erase (hostOf ctx raw))) ∧
      pre S (eraseP (hostOf ctx raw)) := by
  refine ⟨fun hroom => ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩,
    ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩⟩
  · exact (budget_of_room hwf hroom _ rfl rfl).mono (lookup_le_proofBound ctx)
  · intro size hsz
    cases hsz

/-- The initial host reads under a key of `raw` the value `raw` holds. -/
theorem hostOf_storage_of_mem {ctx : Context} {raw : RawStorage} (hwf : ctx.WF raw) {k v : List UInt8}
    (h : (k, v) ∈ raw) : (hostOf ctx raw).storage k = some v := by
  rw [hostOf_storage]
  cases hf : raw.toList.find? (·.1 == k) with
  | none =>
    have := List.find?_eq_none.1 hf (k, v) (Finset.mem_toList.2 h)
    simp at this
  | some p =>
    obtain ⟨k', v'⟩ := p
    have hk : k' = k := by simpa using List.find?_some hf
    subst hk
    have hm := Finset.mem_toList.1 (List.mem_of_find?_eq_some hf)
    simp [hwf.raw_keys_unique _ _ _ hm h]

open ContractModel in
/-- **`ft_total_supply` refines the model on an initialized contract**, with no premise on the
host left: `ftTotalSupply_refines_v86'` with `hpre` and `hpreP` from the context (`pre_of_ctx`),
`STATE` holding the represented state. Left: the code size, `CostsV86` and `LimitsV86`. -/
theorem ftTotalSupply_refines_init (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (S : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (hm : ctx.method = "ft_total_supply") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) .ftTotalSupply
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) .ftTotalSupply ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) .ftTotalSupply) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) .ftTotalSupply) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨-, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  obtain ⟨hpre, hpreP⟩ := pre_of_ctx cfg ctx raw (some S) S hwf hl hval
  exact ftTotalSupply_refines_v86' cfg size codeOf raw (some S) ctx S hp hwf hrep hm hpre hpreP hc hsize

end WNear.Binary.FtTotalSupplyMethod
