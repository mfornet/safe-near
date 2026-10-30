import Bridge.Methods.NearDepositMintModel

/-!
# The successful deposit's final storage is the model's encoding

The effect theorem tracks both values and key membership. Both are needed to show
that the runtime's enumerated `finalStorage` contains exactly the model's records.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody WNear.Binary.DepositBody234
open WNear.Binary.NewBody (Keep keep)

theorem mem_finalStorage (h : NearState) (k v : List UInt8) :
    (k, v) ∈ (finalStorage h).toFinset ↔ k ∈ h.storageKeys ∧ h.storage k = some v := by
  simp only [finalStorage, List.mem_toFinset, List.mem_filterMap, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk, v', hv, rfl, rfl⟩
    exact ⟨hk, hv⟩
  · rintro ⟨hk, hv⟩
    exact ⟨k, hk, v, hv, rfl, rfl⟩

theorem keyOf_model (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) : keyOf h = WNear.accountKey (.ofNear ctx.predecessor) := by
  have hp : h.context.predecessorAccountId = ctx.predecessor.bytes :=
    eraseP_field he (fun x => x.context.predecessorAccountId) fun _ => rfl
  rw [keyOf, hp]
  exact (accountKey_ofNear ctx.predecessor).symm

/-- The enumerated output storage contains the model's updated header and balance, and
every untouched record, with no extra records. -/
theorem effects_storage_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (hraw : raw = WNear.encode s) (h h' : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok) {x : Nat}
    (hp : DepositEffects x h s (regOf s (.ofNear ctx.predecessor)) h') :
    (finalStorage h').toFinset = WNear.encode (mintedOutcome s (.ofContext ctx)).state := by
  have hsto : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  have hkeys : h.storageKeys = (hostOf ctx raw).storageKeys :=
    eraseP_field he NearState.storageKeys fun _ => rfl
  have hinit : (finalStorage h).toFinset = WNear.encode s := by
    simp only [finalStorage, hsto, hkeys]
    exact (FtTotalSupplyMethod.finalStorage_hostOf ctx raw hwf.raw_keys_unique).trans hraw
  ext ⟨k, v⟩
  rw [mem_finalStorage, mem_encode_minted, hp.keys, hp.storage,
    mintedHeader_model ctx raw s hwf hs h he hok, nv232_model ctx raw s hwf hs h he hok,
    keyOf_model ctx raw h he, StateRead.stateKey_eq]
  simp only [WNear.Env.ofContext]
  by_cases hstate : k = WNear.stateKey
  · subst k
    simp only [ite_true, or_true, true_and, Option.some.injEq, eq_comm]
  · by_cases haccount : k = WNear.accountKey (.ofNear ctx.predecessor)
    · subst k
      simp only [hstate, ite_false, ite_true, or_true, or_false, true_and, Option.some.injEq, eq_comm,
        WNear.Env.ofContext]
    · simp only [hstate, haccount, ite_false, or_false]
      rw [← mem_finalStorage, hinit]

/-- A successful deposit creates no promises. -/
theorem effects_noPromises {x : Nat} {h h' : NearState} {s : WNear.State} {reg : Option (UInt64 × UInt64)}
    (hp : DepositEffects x h s reg h') (hn : NoPromises h) : NoPromises h' := by
  exact ⟨(congrArg Keep.promises hp.kept).trans hn.promises,
    (congrArg Keep.returnedPromise hp.kept).trans hn.returned,
    (congrArg Keep.gasWeights hp.kept).trans hn.weights⟩

end WNear.Binary.NearDepositMethod
