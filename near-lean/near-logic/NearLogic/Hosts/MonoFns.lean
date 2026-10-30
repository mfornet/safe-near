import NearLogic.Hosts.Mono
import NearLogic.Hosts.StorageFnsRelax

/-!
# Host functions only grow the logs

`F_mono : FnMono F` for the functional host functions wNEAR imports and for
the two panics. Only `log_utf8` and `log_utf16` change the logs, by appending
one message (`appendLogResult`).
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A result that starts from logs `L` and execution issue `I`: the logs only grow, and a
return keeps the issue. -/
def MonoR (L : List (List UInt8)) (I : Option ExecutionIssue) (r : HostResult NearState) : Prop :=
  L <+: (resHost r).logs ∧ ∀ vals st', r = .Return vals st' → st'.host.lastExecutionIssue = I

theorem MonoR.trap {L I} (st : HostStore NearState) (msg : String) (h : st.host.logs = L) :
    MonoR L I (.Trap st msg) := ⟨by simp only [resHost, h]; exact List.prefix_refl _, fun _ _ h => by cases h⟩

theorem MonoR.ret {L I} (vals : List Value) (st : HostStore NearState) (hl : L <+: st.host.logs)
    (hi : st.host.lastExecutionIssue = I) : MonoR L I (.Return vals st) :=
  ⟨hl, fun _ _ h => by cases h; exact hi⟩

theorem MonoR.ret_eq {L I} (vals : List Value) (st : HostStore NearState) (hl : st.host.logs = L)
    (hi : st.host.lastExecutionIssue = I) : MonoR L I (.Return vals st) :=
  MonoR.ret _ _ (hl ▸ List.prefix_refl _) hi

theorem checkedSetRegister?_mono (st st' : HostStore NearState) (r : UInt64) (d : List UInt8)
    (h : checkedSetRegister? st r d = some st') :
    st'.host.logs = st.host.logs ∧ st'.host.lastExecutionIssue = st.host.lastExecutionIssue := by
  unfold checkedSetRegister? at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

theorem writeRegisterResult_mono (name : String) (st : HostStore NearState) (regId : UInt64)
    (data : List UInt8) (results : List Value) :
    MonoR st.host.logs st.host.lastExecutionIssue (writeRegisterResult name st regId data results) := by
  unfold writeRegisterResult
  split
  · rename_i st' h
    obtain ⟨h1, h2⟩ := checkedSetRegister?_mono _ _ _ _ h
    exact MonoR.ret_eq _ _ h1 h2
  · exact MonoR.trap _ _ rfl

theorem writeRegisterResult_mono' (name : String) (st0 st : HostStore NearState) (regId : UInt64)
    (data : List UInt8) (results : List Value) (hl : st.host.logs = st0.host.logs)
    (hi : st.host.lastExecutionIssue = st0.host.lastExecutionIssue) :
    MonoR st0.host.logs st0.host.lastExecutionIssue (writeRegisterResult name st regId data results) := by
  rw [← hl, ← hi]; exact writeRegisterResult_mono ..

theorem writeMemBytes_mono (name : String) (st : HostStore NearState) (ptr : UInt64)
    (data : List UInt8) :
    MonoR st.host.logs st.host.lastExecutionIssue (writeMemBytes name st ptr data) := by
  unfold writeMemBytes
  split
  · exact MonoR.trap _ _ rfl
  · exact MonoR.ret_eq _ _ rfl rfl

theorem writeU128_mono (name : String) (st : HostStore NearState) (ptr : UInt64) (n : Nat) :
    MonoR st.host.logs st.host.lastExecutionIssue (writeU128 name st ptr n) := writeMemBytes_mono ..

theorem checkAccountId_mono (name : String) (st : HostStore NearState) (acc : List UInt8)
    (next : Unit → HostResult NearState) (h : MonoR st.host.logs st.host.lastExecutionIssue (next ())) :
    MonoR st.host.logs st.host.lastExecutionIssue (checkAccountId name st acc next) := by
  unfold checkAccountId
  split
  · exact h
  · exact MonoR.trap _ _ rfl

theorem checkPublicKey_mono (name : String) (st : HostStore NearState) (acc : List UInt8)
    (next : Unit → HostResult NearState) (h : MonoR st.host.logs st.host.lastExecutionIssue (next ())) :
    MonoR st.host.logs st.host.lastExecutionIssue (checkPublicKey name st acc next) := by
  unfold checkPublicKey
  split
  · exact h
  · exact MonoR.trap _ _ rfl

theorem checkDataLimit_mono (name label : String) (limit : Option Nat) (n : Nat)
    (st : HostStore NearState) (next : Unit → HostResult NearState)
    (error : Option (Nat → Nat → HostError))
    (h : MonoR st.host.logs st.host.lastExecutionIssue (next ())) :
    MonoR st.host.logs st.host.lastExecutionIssue (checkDataLimit name label limit n st next error) := by
  unfold checkDataLimit
  split
  · exact h
  · split <;> exact MonoR.trap _ _ rfl

theorem appendPromiseActionResult_mono (name : String) (st : HostStore NearState) (idx : UInt64)
    (action : PromiseAction) (weight : UInt64) :
    MonoR st.host.logs st.host.lastExecutionIssue (appendPromiseActionResult name st idx action weight) := by
  unfold appendPromiseActionResult
  split
  · exact MonoR.ret_eq _ _ rfl rfl
  · exact MonoR.trap _ _ rfl

theorem appendLogResult_mono (st : HostStore NearState) (r : Except HostError (List UInt8)) :
    MonoR st.host.logs st.host.lastExecutionIssue (appendLogResult st r) := by
  cases r
  · exact MonoR.trap _ _ rfl
  · exact MonoR.ret _ _ (List.prefix_append _ _) rfl

theorem createBatchPromiseResult_mono (name : String) (st : HostStore NearState) (acc : List UInt8) :
    MonoR st.host.logs st.host.lastExecutionIssue (createBatchPromiseResult name st acc) := by
  unfold createBatchPromiseResult
  exact checkAccountId_mono _ _ _ _ (MonoR.ret_eq _ _ rfl rfl)

theorem createCallbackPromiseResult_mono (name : String) (st : HostStore NearState) (b : UInt64)
    (acc : List UInt8) :
    MonoR st.host.logs st.host.lastExecutionIssue (createCallbackPromiseResult name st b acc) := by
  unfold createCallbackPromiseResult
  split
  · exact checkAccountId_mono _ _ _ _ (MonoR.ret_eq _ _ rfl rfl)
  · exact MonoR.trap _ _ rfl

theorem disallowInView_mono (name : String) (hf : NearHostFn NearState)
    (h : ∀ st args, MonoR st.host.logs st.host.lastExecutionIssue (hf.invoke st args)) :
    FnMono (disallowInView name hf) := by
  intro st args
  have := fun (st : HostStore NearState) args => h st args
  simp only [disallowInView]
  split
  · exact MonoR.trap _ _ rfl
  · exact h st args

macro "msplit" : tactic =>
  `(tactic| (repeat' (first
      | (exact MonoR.trap _ _ rfl)
      | (exact MonoR.ret_eq _ _ rfl rfl)
      | (obtain ⟨h1, h2⟩ := checkedSetRegister?_mono _ _ _ _ ‹checkedSetRegister? _ _ _ = some _›
         exact MonoR.ret_eq _ _ h1 h2)
      | (exact writeRegisterResult_mono _ _ _ _ _)
      | (exact writeRegisterResult_mono' _ _ _ _ _ _ rfl rfl)
      | (exact writeU128_mono _ _ _ _)
      | (exact appendPromiseActionResult_mono _ _ _ _ _)
      | (exact createBatchPromiseResult_mono _ _ _)
      | (exact createCallbackPromiseResult_mono _ _ _ _)
      | (exact appendLogResult_mono _ _)
      | (refine checkAccountId_mono _ _ _ _ ?_)
      | (refine checkPublicKey_mono _ _ _ _ ?_)
      | (refine checkDataLimit_mono _ _ _ _ _ _ _ ?_)
      | split)))

/-- Solve `FnMono` of a host function, wrapped by `disallowInView` or not. -/
macro "msolve" : tactic =>
  `(tactic| (first
      | (refine disallowInView_mono _ _ ?_
         intro st args
         dsimp only
         msplit; done)
      | (intro st args
         dsimp only
         show MonoR st.host.logs st.host.lastExecutionIssue _
         msplit; done)))

theorem readRegisterFn_mono : FnMono readRegisterFn := by
  unfold readRegisterFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem registerLenFn_mono : FnMono registerLenFn := by
  unfold registerLenFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem currentAccountIdFn_mono : FnMono currentAccountIdFn := by
  unfold currentAccountIdFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem signerAccountIdFn_mono : FnMono signerAccountIdFn := by
  unfold signerAccountIdFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem signerAccountPkFn_mono : FnMono signerAccountPkFn := by
  unfold signerAccountPkFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem predecessorAccountIdFn_mono : FnMono predecessorAccountIdFn := by
  unfold predecessorAccountIdFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem inputFn_mono : FnMono inputFn := by
  unfold inputFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem blockIndexFn_mono : FnMono blockIndexFn := by
  unfold blockIndexFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem blockTimestampFn_mono : FnMono blockTimestampFn := by
  unfold blockTimestampFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem epochHeightFn_mono : FnMono epochHeightFn := by
  unfold epochHeightFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem storageUsageFn_mono : FnMono storageUsageFn := by
  unfold storageUsageFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem accountBalanceFn_mono : FnMono accountBalanceFn := by
  unfold accountBalanceFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem accountLockedBalanceFn_mono : FnMono accountLockedBalanceFn := by
  unfold accountLockedBalanceFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem attachedDepositFn_mono : FnMono attachedDepositFn := by
  unfold attachedDepositFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem prepaidGasFn_mono : FnMono prepaidGasFn := by
  unfold prepaidGasFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem usedGasFn_mono : FnMono usedGasFn := by
  unfold usedGasFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem randomSeedFn_mono : FnMono randomSeedFn := by
  unfold randomSeedFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem sha256Fn_mono : FnMono sha256Fn := by
  unfold sha256Fn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem keccak256Fn_mono : FnMono keccak256Fn := by
  unfold keccak256Fn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem keccak512Fn_mono : FnMono keccak512Fn := by
  unfold keccak512Fn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem valueReturnFn_mono : FnMono valueReturnFn := by
  unfold valueReturnFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem logUtf8Fn_mono : FnMono logUtf8Fn := by
  unfold logUtf8Fn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem logUtf16Fn_mono : FnMono logUtf16Fn := by
  unfold logUtf16Fn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseCreateFn_mono : FnMono promiseCreateFn := by
  unfold promiseCreateFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseThenFn_mono : FnMono promiseThenFn := by
  unfold promiseThenFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseAndFn_mono : FnMono promiseAndFn := by
  unfold promiseAndFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchCreateFn_mono : FnMono promiseBatchCreateFn := by
  unfold promiseBatchCreateFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchThenFn_mono : FnMono promiseBatchThenFn := by
  unfold promiseBatchThenFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionCreateAccountFn_mono : FnMono promiseBatchActionCreateAccountFn := by
  unfold promiseBatchActionCreateAccountFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionDeployContractFn_mono : FnMono promiseBatchActionDeployContractFn := by
  unfold promiseBatchActionDeployContractFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionFunctionCallFn_mono : FnMono promiseBatchActionFunctionCallFn := by
  unfold promiseBatchActionFunctionCallFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionTransferFn_mono : FnMono promiseBatchActionTransferFn := by
  unfold promiseBatchActionTransferFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionStakeFn_mono : FnMono promiseBatchActionStakeFn := by
  unfold promiseBatchActionStakeFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionAddKeyWithFullAccessFn_mono : FnMono promiseBatchActionAddKeyWithFullAccessFn := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionAddKeyWithFunctionCallFn_mono : FnMono promiseBatchActionAddKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionDeleteKeyFn_mono : FnMono promiseBatchActionDeleteKeyFn := by
  unfold promiseBatchActionDeleteKeyFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseBatchActionDeleteAccountFn_mono : FnMono promiseBatchActionDeleteAccountFn := by
  unfold promiseBatchActionDeleteAccountFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseResultsCountFn_mono : FnMono promiseResultsCountFn := by
  unfold promiseResultsCountFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseResultFn_mono : FnMono promiseResultFn := by
  unfold promiseResultFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem promiseReturnFn_mono : FnMono promiseReturnFn := by
  unfold promiseReturnFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem validatorStakeFn_mono : FnMono validatorStakeFn := by
  unfold validatorStakeFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem validatorTotalStakeFn_mono : FnMono validatorTotalStakeFn := by
  unfold validatorTotalStakeFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem storageReadFn_mono : FnMono storageReadFn := by
  unfold storageReadFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem storageWriteFn_mono : FnMono storageWriteFn := by
  unfold storageWriteFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem storageRemoveFn_mono : FnMono storageRemoveFn := by
  unfold storageRemoveFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem storageHasKeyFn_mono : FnMono storageHasKeyFn := by
  unfold storageHasKeyFn
  try unfold accountIdRegisterFn
  try unfold publicKeyRegisterFn
  try unfold contextU64Fn
  try unfold contextU128MemFn
  try unfold cryptoHostFn
  msolve

theorem panicMetered_mono : FnMono panicMetered := by
  intro st args
  exact ⟨List.prefix_refl _, fun _ _ h => by cases h⟩

theorem panicUtf8Metered_mono : FnMono panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  dsimp only
  refine ⟨?_, fun _ _ h => by split at h <;> (try split at h) <;> cases h⟩
  split <;> (try split) <;> exact List.prefix_refl _

end NearLogic
