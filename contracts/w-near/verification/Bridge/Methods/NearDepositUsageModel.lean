import Bridge.Methods.NearDepositStorageAgreement

/-!
# Storage usage before and after minting

Every balance record is 16 bytes and every header is 29 bytes. Updating an existing
account preserves usage; registering a new predecessor adds exactly its key, value
and per-record overhead.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody WNear.Binary.DepositBody234

/-- Exact usage of the model's encoding, independent of the numeric balances and supply. -/
theorem usageOf_encode (p : RuntimeConfig) (s : WNear.State) :
    storageUsageOf p (WNear.encode s) = 34 + p.fees.numExtraBytesRecord +
      ∑ a ∈ s.registered, ((WNear.accountKey a).length + 16 + p.fees.numExtraBytesRecord) := by
  have hheader : (WNear.stateKey, WNear.header s) ∉
      s.registered.image (fun a => (WNear.accountKey a, WNear.Borsh.u128 (s.balance a))) := by
    intro hm
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp hm
    exact WNear.accountKey_ne_stateKey a (congrArg Prod.fst he)
  unfold storageUsageOf WNear.encode
  rw [Finset.sum_insert hheader]
  rw [Finset.sum_image (fun a _ b _ he => WNear.accountKey_injective (congrArg Prod.fst he))]
  have hkey : WNear.stateKey.length = 5 := by rw [← StateRead.stateKey_eq]; rfl
  simp only [recordBytes, hkey, StateReadModel.header_length, FtTotalSupply.u128_length]

/-- Minting only changes usage when the predecessor's account is newly inserted. -/
theorem usageOf_minted (p : RuntimeConfig) (s : WNear.State) (env : WNear.Env) :
    storageUsageOf p (WNear.encode (mintedOutcome s env).state) = storageUsageOf p (WNear.encode s) +
      if env.predecessor ∈ s.registered then 0
      else (WNear.accountKey env.predecessor).length + 16 + p.fees.numExtraBytesRecord := by
  rw [usageOf_encode, usageOf_encode, mintedState_eq]
  by_cases hr : env.predecessor ∈ s.registered
  · simp only [Finset.insert_eq_of_mem hr, if_pos hr, Nat.add_zero]
  · rw [Finset.sum_insert hr, if_neg hr]
    omega

theorem mintedHeader_length (h : NearState) (s : WNear.State) (reg : Option (UInt64 × UInt64)) :
    (mintedHeader h s reg).length = 29 := by
  simp only [mintedHeader, List.length_append, bytes32, List.length_map, List.length_range,
    StateReadModel.accountsPrefix_length, StorageBalanceBounds.u128Of_length, FtTotalSupply.u64_length]

theorem nv232_length (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) :
    (nv232 h reg xb).length = 16 := by
  rw [nv232_amount, StorageBalanceBounds.u128Of_length]

/-- The method's usage counter follows the same record-size rule without `u64` wraparound. -/
theorem effects_usage {x : Nat} {h h' : NearState} {s : WNear.State} {reg : Option (UInt64 × UInt64)}
    (hp : DepositEffects x h s reg h')
    (hroom : h.context.storageUsage.toNat + (keyOf h).length + 16 + x < 2 ^ 64) :
    h'.context.storageUsage.toNat = h.context.storageUsage.toNat +
      if reg = none then (keyOf h).length + 16 + x else 0 := by
  have hz : zeros.length = 16 := by simp only [zeros, List.length_append, List.length_replicate]
  rw [hp.usage]
  cases reg with
  | some words =>
    simp only [usage232, writeUsage, mintedHeader_length, StateReadModel.header_length,
      Nat.add_sub_cancel, UInt64.ofNat_toNat, Option.some_ne_none, ite_false, Nat.add_zero]
  | none =>
    simp only [usage232, writeUsage, mintedHeader_length, StateReadModel.header_length,
      nv232_length, hz, Nat.add_sub_cancel, ite_true]
    simp only [UInt64.toNat_ofNat_of_lt' hroom]
    omega

/-- The binary's counter is exactly the model boundary's change in encoded storage usage. -/
theorem effects_usage_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (h h' : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hp : DepositEffects ctx.protocol.fees.numExtraBytesRecord h s
      (regOf s (.ofNear ctx.predecessor)) h')
    (hroom : ctx.storageUsage + (85 + ctx.protocol.fees.numExtraBytesRecord) < 2 ^ 64) :
    h'.context.storageUsage.toNat = ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (WNear.encode (mintedOutcome s (.ofContext ctx)).state) := by
  have hu : h.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
    eraseP_field he (fun a => a.context.storageUsage) fun _ => rfl
  have huNat : h.context.storageUsage.toNat = ctx.storageUsage := by
    rw [hu, UInt64.toNat_ofNat_of_lt' (by omega : ctx.storageUsage < 2 ^ 64)]
  have hpBytes := predecessor_properties_of_eraseP ctx raw h he
  have hk : (keyOf h).length ≤ 69 := by
    simp only [keyOf, List.length_append, StateReadModel.accountsPrefix_length, bytes32,
      List.length_map, List.length_range]
    omega
  have hU : h.context.storageUsage.toNat + (keyOf h).length + 16 +
      ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64 := by
    rw [huNat]
    omega
  rw [effects_usage hp hU, huNat, usageOf_minted, ← hraw, keyOf_model ctx raw h he]
  simp only [WNear.Env.ofContext]
  have hge := hwf.usage_ge
  by_cases hr : WNear.AccountId.ofNear ctx.predecessor ∈ s.registered <;>
    simp only [regOf, hr, ite_true, ite_false, Option.some_ne_none, Nat.add_zero] <;> omega

end WNear.Binary.NearDepositMethod
