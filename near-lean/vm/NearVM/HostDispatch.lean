import Batteries.Data.List.Basic
import NearVM.HostPromises

/-!
Promise dependency preservation for the remaining host functions and the actual
metered dispatch table. Unsupported crypto/yield operations are proved through
their rejection path; this does not validate their functional placeholders.
-/

namespace Wasm.Near

theorem inputFn_preserves : HostPreservesPromises inputFn := by
  intro st args hwf
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem readRegisterFn_preserves : HostPreservesPromises readRegisterFn := by
  intro st args hwf
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem registerLenFn_preserves : HostPreservesPromises registerLenFn := by
  intro st args hwf
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem writeRegisterFn_preserves : HostPreservesPromises writeRegisterFn := by
  intro st args hwf
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem storageWriteFn_preserves : HostPreservesPromises storageWriteFn := by
  intro st args hwf
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)
  all_goals
    simp_all only [HostResult.Satisfies, NearState.setStorage,
      NearState.invalidateIterators]
  all_goals
    rename_i hreg
    rw [checkedSetRegister_promises hreg]
    exact hwf

theorem storageReadFn_preserves : HostPreservesPromises storageReadFn := by
  intro st args hwf
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem storageRemoveFn_preserves : HostPreservesPromises storageRemoveFn := by
  intro st args hwf
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)
  all_goals
    simp_all only [HostResult.Satisfies, NearState.removeStorage,
      NearState.invalidateIterators]
  all_goals
    rename_i hreg
    rw [checkedSetRegister_promises hreg]
    exact hwf

theorem storageHasKeyFn_preserves : HostPreservesPromises storageHasKeyFn := by
  intro st args hwf
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem currentAccountIdFn_preserves : HostPreservesPromises currentAccountIdFn := by
  intro st args hwf
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem predecessorAccountIdFn_preserves : HostPreservesPromises predecessorAccountIdFn := by
  intro st args hwf
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem signerAccountIdFn_preserves : HostPreservesPromises signerAccountIdFn := by
  intro st args hwf
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem signerAccountPkFn_preserves : HostPreservesPromises signerAccountPkFn := by
  intro st args hwf
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem attachedDepositFn_preserves : HostPreservesPromises attachedDepositFn := by
  intro st args hwf
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem blockIndexFn_preserves : HostPreservesPromises blockIndexFn := by
  intro st args hwf
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem blockTimestampFn_preserves : HostPreservesPromises blockTimestampFn := by
  intro st args hwf
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem epochHeightFn_preserves : HostPreservesPromises epochHeightFn := by
  intro st args hwf
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem storageUsageFn_preserves : HostPreservesPromises storageUsageFn := by
  intro st args hwf
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem accountBalanceFn_preserves : HostPreservesPromises accountBalanceFn := by
  intro st args hwf
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem accountLockedBalanceFn_preserves : HostPreservesPromises accountLockedBalanceFn := by
  intro st args hwf
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem prepaidGasFn_preserves : HostPreservesPromises prepaidGasFn := by
  intro st args hwf
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem usedGasFn_preserves : HostPreservesPromises usedGasFn := by
  intro st args hwf
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem randomSeedFn_preserves : HostPreservesPromises randomSeedFn := by
  intro st args hwf
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem logUtf8Fn_preserves : HostPreservesPromises logUtf8Fn := by
  intro st args hwf
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem logUtf16Fn_preserves : HostPreservesPromises logUtf16Fn := by
  intro st args hwf
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem panicMetered_preserves : HostPreservesPromises panicMetered := by
  intro st args hwf
  unfold panicMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem panicUtf8Metered_preserves : HostPreservesPromises panicUtf8Metered := by
  intro st args hwf
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem abortMetered_preserves : HostPreservesPromises abortMetered := by
  intro st args hwf
  unfold abortMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem gasFn_preserves : HostPreservesPromises gasFn := by
  intro st args hwf
  unfold gasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

set_option maxRecDepth 16384 in
/-- Every function published by the runtime's metered registry preserves
creation-order validity, including rejected unsupported and deprecated calls. -/
theorem meteredHostFns_preserves (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesPromises entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals first
      | (intro st args hwf; exact hwf)
      | apply metered_preserves_promises
    all_goals first
      | exact inputFn_preserves
      | exact readRegisterFn_preserves
      | exact registerLenFn_preserves
      | exact writeRegisterFn_preserves
      | exact storageWriteFn_preserves
      | exact storageReadFn_preserves
      | exact storageRemoveFn_preserves
      | exact storageHasKeyFn_preserves
      | exact currentAccountIdFn_preserves
      | exact predecessorAccountIdFn_preserves
      | exact signerAccountIdFn_preserves
      | exact signerAccountPkFn_preserves
      | exact attachedDepositFn_preserves
      | exact blockIndexFn_preserves
      | exact blockTimestampFn_preserves
      | exact epochHeightFn_preserves
      | exact storageUsageFn_preserves
      | exact accountBalanceFn_preserves
      | exact accountLockedBalanceFn_preserves
      | exact prepaidGasFn_preserves
      | exact usedGasFn_preserves
      | exact randomSeedFn_preserves
      | exact logUtf8Fn_preserves
      | exact logUtf16Fn_preserves
      | exact panicMetered_preserves
      | exact panicUtf8Metered_preserves
      | exact abortMetered_preserves
      | exact gasFn_preserves
      | exact promiseCreateFn_preserves
      | exact promiseThenFn_preserves
      | exact promiseAndFn_preserves
      | exact promiseBatchCreateFn_preserves
      | exact promiseBatchThenFn_preserves
      | exact promiseBatchActionCreateAccountFn_preserves
      | exact promiseBatchActionDeployContractFn_preserves
      | exact promiseBatchActionFunctionCallFn_preserves
      | exact promiseBatchActionFunctionCallWeightFn_preserves
      | exact promiseBatchActionTransferFn_preserves
      | exact promiseBatchActionStakeFn_preserves
      | exact promiseBatchActionAddKeyWithFullAccessFn_preserves
      | exact promiseBatchActionAddKeyWithFunctionCallFn_preserves
      | exact promiseBatchActionDeleteKeyFn_preserves
      | exact promiseBatchActionDeleteAccountFn_preserves
      | exact promiseBatchActionUseGlobalContractFn_preserves
      | exact promiseBatchActionUseGlobalContractByAccountIdFn_preserves
      | exact promiseBatchActionDeployGlobalContractFn_preserves
      | exact promiseBatchActionDeployGlobalContractByAccountIdFn_preserves
      | exact promiseBatchActionTransferToGasKeyFn_preserves
      | exact promiseBatchActionAddGasKeyWithFullAccessFn_preserves
      | exact promiseBatchActionAddGasKeyWithFunctionCallFn_preserves
      | exact promiseYieldCreateFn_preserves
      | exact promiseYieldResumeFn_preserves
      | exact chainIdFn_preserves
      | exact valueReturnFn_preserves
      | exact promiseReturnFn_preserves
      | exact promiseResultsCountFn_preserves
      | exact promiseResultFn_preserves
  · subst entry
    exact gasFn_preserves

/-- Resolution cannot introduce a function outside the proved host registry. -/
theorem resolveMeteredImports_preserves (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesPromises fn := by
  induction imports generalizing env with
  | nil =>
    simp only [resolveMeteredImports, Except.ok.injEq] at h
    subst env
    simp
  | cons decl rest ih =>
    cases hf : (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) with
    | none => simp [resolveMeteredImports, hf] at h
    | some entry =>
      obtain ⟨found, fn⟩ := entry
      cases hr : resolveMeteredImports cfg rest with
      | error message => simp [resolveMeteredImports, hf, hr] at h
      | ok tail =>
        simp only [resolveMeteredImports, hf, hr, Except.ok.injEq] at h
        subst env
        intro candidate hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact meteredHostFns_preserves cfg (found, candidate) (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_preserves (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesPromises fn :=
  resolveMeteredImports_preserves cfg m.importDecls env h

/-- Each output slot is the exact first table match for the corresponding
input declaration; resolution preserves import order and multiplicity. -/
theorem resolveMeteredImports_aligned (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    List.Forall₂ (fun decl fn => ∃ entry,
      (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) = some entry ∧
      entry.2 = fn) imports env.funcs := by
  induction imports generalizing env with
  | nil =>
    simp only [resolveMeteredImports, Except.ok.injEq] at h
    subst env
    exact .nil
  | cons decl rest ih =>
    cases hf : (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) with
    | none => simp [resolveMeteredImports, hf] at h
    | some entry =>
      obtain ⟨found, fn⟩ := entry
      cases hr : resolveMeteredImports cfg rest with
      | error message => simp [resolveMeteredImports, hf, hr] at h
      | ok tail =>
        simp only [resolveMeteredImports, hf, hr, Except.ok.injEq] at h
        subst env
        exact .cons ⟨(found, fn), hf, rfl⟩ (ih tail hr)

theorem resolveMetered_length (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) : env.funcs.length = m.importDecls.length := by
  have alignment := resolveMeteredImports_aligned cfg m.importDecls env h
  generalize m.importDecls = imports at alignment ⊢
  generalize env.funcs = funcs at alignment ⊢
  induction alignment with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

end Wasm.Near
