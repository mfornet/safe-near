import Bridge.Methods.NearDepositEffects

/-!
# The state encoded by a successful deposit

Normalize the model's optional registration to one account update, and match the
binary's header bytes to that exact state.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody

/-- Registration and minting together insert the predecessor and update only its balance. -/
theorem mintedState_eq (s : WNear.State) (env : WNear.Env) :
    (mintedOutcome s env).state =
      { registered := insert env.predecessor s.registered
        balance := Function.update s.balance env.predecessor
          ((modelReg s env.predecessor).getD 0 + amountOf env.attachedDeposit (modelReg s env.predecessor) s.storageMin)
        totalSupply := s.totalSupply + amountOf env.attachedDeposit (modelReg s env.predecessor) s.storageMin
        accountStorageUsage := s.accountStorageUsage } := by
  by_cases hr : env.predecessor ∈ s.registered <;>
    simp [mintedOutcome, WNear.State.setBalance, WNear.State.register, hr]

/-- The final `STATE` write is precisely the header of the model's minted state. -/
theorem mintedHeader_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok) :
    mintedHeader h s (regOf s (.ofNear ctx.predecessor)) = WNear.header (mintedOutcome s (.ofContext ctx)).state := by
  have hc := (caseDep_eq_model ctx raw s hwf hs h he).symm.trans hok
  have hb := (dcase_ok_bounds _ _ _ _ hc).2
  have ht : (FtTotalSupply.loOf s).toNat + 2 ^ 64 * (FtTotalSupply.hiOf s).toNat = s.totalSupply :=
    (FtTotalSupply.val_loOf s).trans (Nat.mod_eq_of_lt hs.totalSupply_lt)
  rw [mintedHeader, ht, amount232_model ctx raw s hwf hs h he hok, u128Of_borsh _ hb,
    mintedState_eq]
  simp only [WNear.header, WNear.Borsh.bytes, StateReadModel.accountsPrefix_length]
  rfl

/-- Outside the header and predecessor record, minting preserves every stored key/value pair. -/
theorem mem_encode_minted_other (s : WNear.State) (env : WNear.Env) (k v : List UInt8)
    (hstate : k ≠ WNear.stateKey) (haccount : k ≠ WNear.accountKey env.predecessor) :
    (k, v) ∈ WNear.encode (mintedOutcome s env).state ↔ (k, v) ∈ WNear.encode s := by
  have different (b : WNear.AccountId) (he : WNear.accountKey b = k) : b ≠ env.predecessor := by
    intro hb
    subst b
    exact haccount he.symm
  have balance (b : WNear.AccountId) (hb : b ≠ env.predecessor) :
      (mintedOutcome s env).state.balance b = s.balance b := by
    rw [mintedState_eq]
    simp only [Function.update_of_ne hb]
  constructor
  · intro hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact False.elim (hstate (congrArg Prod.fst hm))
    · obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hm
      have hbne := different b (congrArg Prod.fst he)
      have hbold : b ∈ s.registered := by
        rw [mintedState_eq] at hb
        exact (Finset.mem_insert.mp hb).resolve_left hbne
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨b, hbold, by simpa only [balance b hbne] using he⟩
  · intro hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact False.elim (hstate (congrArg Prod.fst hm))
    · obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hm
      have hbne := different b (congrArg Prod.fst he)
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨b, ?_, ?_⟩
      · rw [mintedState_eq]
        exact Finset.mem_insert_of_mem hb
      · simpa only [balance b hbne] using he

/-- Exact storage membership after minting: two updated records, every other pair unchanged. -/
theorem mem_encode_minted (s : WNear.State) (env : WNear.Env) (k v : List UInt8) :
    (k, v) ∈ WNear.encode (mintedOutcome s env).state ↔
      if k = WNear.stateKey then v = WNear.header (mintedOutcome s env).state
      else if k = WNear.accountKey env.predecessor then
        v = WNear.Borsh.u128 ((modelReg s env.predecessor).getD 0 +
          amountOf env.attachedDeposit (modelReg s env.predecessor) s.storageMin)
      else (k, v) ∈ WNear.encode s := by
  by_cases hstate : k = WNear.stateKey
  · subst k
    simp only [ite_true, WNear.mem_encode_header]
  · by_cases haccount : k = WNear.accountKey env.predecessor
    · subst k
      rw [WNear.mem_encode_account]
      simp only [hstate, ite_false, ite_true, mintedState_eq, Finset.mem_insert_self,
        Function.update_self, true_and]
    · simp only [hstate, haccount, ite_false]
      exact mem_encode_minted_other s env k v hstate haccount

end WNear.Binary.NearDepositMethod
