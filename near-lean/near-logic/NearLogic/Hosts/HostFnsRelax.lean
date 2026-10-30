import NearLogic.Hosts.RelaxFns
import NearLogic.Hosts.ValueReturnRelax

/-!
# Functional host functions under raised gas limits

Each functional NEAR host function that wNEAR imports (all but the storage
operations and the panics) commutes with raising the gas limits
(`F_relax`) and keeps them (`F_keep`). Then each metered host respects raised
limits (`relaxFn_*`).
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A host function result keeps the gas limits of `st`. -/
def KeepsLimits (st : HostStore NearState) (r : HostResult NearState) : Prop :=
  ∀ vals st2, r = .Return vals st2 →
    st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt

theorem KeepsLimits.trap (st st' : HostStore NearState) (msg : String) :
    KeepsLimits st (.Trap st' msg) := fun _ _ h => by cases h

theorem KeepsLimits.ret (st : HostStore NearState) (vals : List Value) (st2 : HostStore NearState)
    (h1 : st2.host.gas.prepaid = st.host.gas.prepaid) (h2 : st2.host.gas.maxBurnt = st.host.gas.maxBurnt) :
    KeepsLimits st (.Return vals st2) := fun _ _ h => by
  cases h; exact ⟨h1, h2⟩

@[simp] theorem relaxSt_mem (st : HostStore NearState) (p m : Nat) : (relaxSt st p m).mem = st.mem := rfl
@[simp] theorem relaxSt_registers (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.registers = st.host.registers := rfl
@[simp] theorem relaxSt_context (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.context = st.host.context := rfl
@[simp] theorem relaxSt_promises (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.promises = st.host.promises := rfl
@[simp] theorem relaxSt_promiseResults (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.promiseResults = st.host.promiseResults := rfl
@[simp] theorem relaxSt_randomSeed (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.randomSeed = st.host.randomSeed := rfl
@[simp] theorem relaxSt_logs (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.logs = st.host.logs := rfl
@[simp] theorem relaxSt_gasWeights (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.gasWeights = st.host.gasWeights := rfl
@[simp] theorem memBytes_relaxSt (st : HostStore NearState) (p m : Nat) :
    memBytes (relaxSt st p m) = memBytes st := rfl
@[simp] theorem nextPromiseIdx_relaxSt (st : HostStore NearState) (p m : Nat) :
    nextPromiseIdx (relaxSt st p m) = nextPromiseIdx st := rfl
@[simp] theorem promiseIndexValid_relaxSt (st : HostStore NearState) (p m : Nat) (i : Nat) :
    promiseIndexValid (relaxSt st p m) i = promiseIndexValid st i := rfl
@[simp] theorem readU128Mem_relaxSt (st : HostStore NearState) (p m : Nat) (ptr : UInt64) :
    readU128Mem (relaxSt st p m) ptr = readU128Mem st ptr := rfl

/-- Split a conditional or match on both sides of a goal until they agree. -/
macro "rsplit" : tactic =>
  `(tactic| (repeat' (first | rfl | contradiction | split | (simp only [*, ↓reduceIte, if_true, if_false]))))

/-! ## Helpers -/

theorem checkedSetRegister?_relax (st : HostStore NearState) (regId : UInt64) (data : List UInt8) (p m : Nat) :
    checkedSetRegister? (relaxSt st p m) regId data = (checkedSetRegister? st regId data).map (relaxSt · p m) := by
  unfold checkedSetRegister?
  simp only [config_relaxSt]
  split
  · rfl
  · by_cases h2 : withinLimit st.host.config.maxRegisterLen data.length = true
    · simp only [h2]; rfl
    · simp only [h2]; rfl

theorem writeRegisterResult_relax (name : String) (st : HostStore NearState) (regId : UInt64)
    (data : List UInt8) (results : List Value) (p m : Nat) :
    writeRegisterResult name (relaxSt st p m) regId data results =
      (writeRegisterResult name st regId data results).relax p m := by
  unfold writeRegisterResult
  rw [checkedSetRegister?_relax]
  cases checkedSetRegister? st regId data <;> rfl

theorem writeRegisterResult_keep (name : String) (st : HostStore NearState) (regId : UInt64)
    (data : List UInt8) (results : List Value) :
    KeepsLimits st (writeRegisterResult name st regId data results) := by
  unfold writeRegisterResult checkedSetRegister?
  split
  · rename_i st' h
    split at h
    · cases h; exact KeepsLimits.ret _ _ _ rfl rfl
    · split at h
      · cases h; exact KeepsLimits.ret _ _ _ rfl rfl
      · cases h
  · exact KeepsLimits.trap _ _ _

theorem writeMemBytes_relax (name : String) (st : HostStore NearState) (ptr : UInt64)
    (data : List UInt8) (p m : Nat) :
    writeMemBytes name (relaxSt st p m) ptr data = (writeMemBytes name st ptr data).relax p m := by
  unfold writeMemBytes
  simp only [memBytes_relaxSt]
  rsplit

theorem writeU128_relax (name : String) (st : HostStore NearState) (ptr : UInt64)
    (n : Nat) (p m : Nat) :
    writeU128 name (relaxSt st p m) ptr n = (writeU128 name st ptr n).relax p m :=
  writeMemBytes_relax ..

theorem writeMemBytes_keep (name : String) (st : HostStore NearState) (ptr : UInt64)
    (data : List UInt8) : KeepsLimits st (writeMemBytes name st ptr data) := by
  unfold writeMemBytes
  split
  · exact KeepsLimits.trap _ _ _
  · exact KeepsLimits.ret _ _ _ rfl rfl

theorem writeU128_keep (name : String) (st : HostStore NearState) (ptr : UInt64) (n : Nat) :
    KeepsLimits st (writeU128 name st ptr n) :=
  fun v s h => writeMemBytes_keep _ _ _ _ v s h

theorem checkAccountId_relax (name : String) (st : HostStore NearState) (acc : List UInt8)
    (next next' : Unit → HostResult NearState) (p m : Nat)
    (hn : next' () = (next ()).relax p m) :
    checkAccountId name (relaxSt st p m) acc next' =
      (checkAccountId name st acc next).relax p m := by
  unfold checkAccountId
  simp only [config_relaxSt]
  split
  · rename_i h; simp only [h, ↓reduceIte]; exact hn
  · rename_i h; simp only [h, ↓reduceIte]; rfl

theorem checkPublicKey_relax (name : String) (st : HostStore NearState) (acc : List UInt8)
    (next next' : Unit → HostResult NearState) (p m : Nat)
    (hn : next' () = (next ()).relax p m) :
    checkPublicKey name (relaxSt st p m) acc next' =
      (checkPublicKey name st acc next).relax p m := by
  unfold checkPublicKey
  simp only [config_relaxSt]
  split
  · rename_i h; simp only [h, ↓reduceIte]; exact hn
  · rename_i h; simp only [h, ↓reduceIte]; rfl

theorem checkAccountId_keep (name : String) (st : HostStore NearState) (acc : List UInt8)
    (next : Unit → HostResult NearState) (h : KeepsLimits st (next ())) :
    KeepsLimits st (checkAccountId name st acc next) := by
  unfold checkAccountId
  split
  · exact h
  · exact KeepsLimits.trap _ _ _

theorem checkPublicKey_keep (name : String) (st : HostStore NearState) (acc : List UInt8)
    (next : Unit → HostResult NearState) (h : KeepsLimits st (next ())) :
    KeepsLimits st (checkPublicKey name st acc next) := by
  unfold checkPublicKey
  split
  · exact h
  · exact KeepsLimits.trap _ _ _

theorem disallowInView_relax (name : String) (hf : NearHostFn NearState)
    (h : ∀ st args p m, hf.invoke (relaxSt st p m) args = (hf.invoke st args).relax p m)
    (st : HostStore NearState) (args : List Value) (p m : Nat) :
    (disallowInView name hf).invoke (relaxSt st p m) args = ((disallowInView name hf).invoke st args).relax p m := by
  simp only [disallowInView, relaxSt_context]
  by_cases hv : st.host.context.isView = true
  · simp only [hv, ↓reduceIte]; rfl
  · simp only [hv, ↓reduceIte]; exact h st args p m

theorem disallowInView_keep (name : String) (hf : NearHostFn NearState)
    (h : ∀ st args vals st2, hf.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt)
    (st : HostStore NearState) (args : List Value) (vals st2) :
    (disallowInView name hf).invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  simp only [disallowInView]
  split
  · intro h; cases h
  · exact h st args vals st2

theorem appendPromiseActionResult_relax (name : String) (st : HostStore NearState) (idx : UInt64)
    (action : PromiseAction) (weight : UInt64) (p m : Nat) :
    appendPromiseActionResult name (relaxSt st p m) idx action weight =
      (appendPromiseActionResult name st idx action weight).relax p m := by
  unfold appendPromiseActionResult
  simp only [relaxSt_promises, relaxSt_gasWeights]
  split
  · rfl
  · rfl

theorem appendPromiseActionResult_keep (name : String) (st : HostStore NearState) (idx : UInt64)
    (action : PromiseAction) (weight : UInt64) :
    KeepsLimits st (appendPromiseActionResult name st idx action weight) := by
  unfold appendPromiseActionResult
  split
  · exact KeepsLimits.ret _ _ _ rfl rfl
  · exact KeepsLimits.trap _ _ _

theorem appendLogResult_relax (st : HostStore NearState) (r : Except HostError (List UInt8)) (p m : Nat) :
    appendLogResult (relaxSt st p m) r = (appendLogResult st r).relax p m := by
  cases r <;> rfl

theorem appendLogResult_keep (st : HostStore NearState) (r : Except HostError (List UInt8)) :
    KeepsLimits st (appendLogResult st r) := by
  cases r
  · exact KeepsLimits.trap _ _ _
  · exact KeepsLimits.ret _ _ _ rfl rfl

theorem logUtf8Read_relax (st : HostStore NearState) (len ptr : UInt64) (p m : Nat) :
    logUtf8Read (relaxSt st p m) len ptr = logUtf8Read st len ptr := by
  simp only [logUtf8Read, readUtf8String, scanNulBytes_relax]; rfl

theorem logUtf16Read_relax (st : HostStore NearState) (len ptr : UInt64) (p m : Nat) :
    logUtf16Read (relaxSt st p m) len ptr = logUtf16Read st len ptr := by
  simp only [logUtf16Read, readUtf16String, scanNulUnits_relax]; rfl

theorem readFunctionCallAction?_relax (st : HostStore NearState) (a b c d e f : UInt64) (p m : Nat) :
    readFunctionCallAction? (relaxSt st p m) a b c d e f = readFunctionCallAction? st a b c d e f := rfl

theorem createBatchPromiseResult_relax (name : String) (st : HostStore NearState) (acc : List UInt8) (p m : Nat) :
    createBatchPromiseResult name (relaxSt st p m) acc = (createBatchPromiseResult name st acc).relax p m := by
  unfold createBatchPromiseResult
  exact checkAccountId_relax _ _ _ _ _ _ _ rfl

theorem createBatchPromiseResult_keep (name : String) (st : HostStore NearState) (acc : List UInt8) :
    KeepsLimits st (createBatchPromiseResult name st acc) := by
  unfold createBatchPromiseResult
  exact checkAccountId_keep _ _ _ _ (KeepsLimits.ret _ _ _ rfl rfl)

theorem createCallbackPromiseResult_relax (name : String) (st : HostStore NearState) (b : UInt64)
    (acc : List UInt8) (p m : Nat) :
    createCallbackPromiseResult name (relaxSt st p m) b acc =
      (createCallbackPromiseResult name st b acc).relax p m := by
  unfold createCallbackPromiseResult
  simp only [promiseIndexValid_relaxSt]
  by_cases h : promiseIndexValid st b.toNat = true
  · simp only [h, ↓reduceIte]; exact checkAccountId_relax _ _ _ _ _ _ _ rfl
  · simp only [h, ↓reduceIte]; rfl

theorem createCallbackPromiseResult_keep (name : String) (st : HostStore NearState) (b : UInt64)
    (acc : List UInt8) : KeepsLimits st (createCallbackPromiseResult name st b acc) := by
  unfold createCallbackPromiseResult
  split
  · exact checkAccountId_keep _ _ _ _ (KeepsLimits.ret _ _ _ rfl rfl)
  · exact KeepsLimits.trap _ _ _

/-! ## Registers and context -/

theorem inputFn_relax : ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    inputFn.invoke (relaxSt st p m) args = (inputFn.invoke st args).relax p m := by
  intro st args p m
  unfold inputFn
  dsimp only
  split
  · exact writeRegisterResult_relax ..
  · rfl

theorem inputFn_keep : ∀ (st : HostStore NearState) (args : List Value) vals st2,
    inputFn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  intro st args vals st2
  unfold inputFn
  dsimp only
  split
  · exact writeRegisterResult_keep _ _ _ _ _ vals st2
  · exact KeepsLimits.trap _ _ _ vals st2

theorem randomSeedFn_relax : ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    randomSeedFn.invoke (relaxSt st p m) args = (randomSeedFn.invoke st args).relax p m := by
  intro st args p m
  unfold randomSeedFn
  dsimp only
  split
  · exact writeRegisterResult_relax ..
  · rfl

theorem randomSeedFn_keep : ∀ (st : HostStore NearState) (args : List Value) vals st2,
    randomSeedFn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  intro st args vals st2
  unfold randomSeedFn
  dsimp only
  split
  · exact writeRegisterResult_keep _ _ _ _ _ vals st2
  · exact KeepsLimits.trap _ _ _ vals st2

theorem readRegisterFn_relax : ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    readRegisterFn.invoke (relaxSt st p m) args = (readRegisterFn.invoke st args).relax p m := by
  intro st args p m
  unfold readRegisterFn
  dsimp only
  simp only [relaxSt_registers, memBytes_relaxSt]
  rsplit

theorem readRegisterFn_keep : ∀ (st : HostStore NearState) (args : List Value) vals st2,
    readRegisterFn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  intro st args vals st2
  unfold readRegisterFn
  dsimp only
  split <;> try (intro h; cases h; done)
  split <;> try (intro h; cases h; done)
  split <;> intro h <;> cases h
  exact ⟨rfl, rfl⟩

theorem registerLenFn_relax : ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    registerLenFn.invoke (relaxSt st p m) args = (registerLenFn.invoke st args).relax p m := by
  intro st args p m
  unfold registerLenFn
  dsimp only
  simp only [relaxSt_registers]
  rsplit

theorem registerLenFn_keep : ∀ (st : HostStore NearState) (args : List Value) vals st2,
    registerLenFn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  intro st args vals st2
  unfold registerLenFn
  dsimp only
  split <;> try (intro h; cases h; done)
  split <;> intro h <;> cases h <;> exact ⟨rfl, rfl⟩

/-- The statement `_relax` of a host function. -/
def RelaxComm (f : NearHostFn NearState) : Prop :=
  ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    f.invoke (relaxSt st p m) args = (f.invoke st args).relax p m

/-- The statement `_keep` of a host function. -/
def KeepGas (f : NearHostFn NearState) : Prop :=
  ∀ (st : HostStore NearState) (args : List Value) vals st2,
    f.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt

theorem accountIdRegisterFn_relax (name : String) (select : NearContext → List UInt8) :
    RelaxComm (accountIdRegisterFn name select) := by
  intro st args p m
  unfold accountIdRegisterFn
  dsimp only
  split
  · exact checkAccountId_relax _ _ _ _ _ _ _ (writeRegisterResult_relax ..)
  · rfl

theorem accountIdRegisterFn_keep (name : String) (select : NearContext → List UInt8) :
    KeepGas (accountIdRegisterFn name select) := by
  intro st args vals st2
  unfold accountIdRegisterFn
  dsimp only
  split
  · exact checkAccountId_keep _ _ _ _ (writeRegisterResult_keep _ _ _ _ _) vals st2
  · exact KeepsLimits.trap _ _ _ vals st2

theorem publicKeyRegisterFn_relax (name : String) (select : NearContext → List UInt8) :
    RelaxComm (publicKeyRegisterFn name select) := by
  intro st args p m
  unfold publicKeyRegisterFn
  dsimp only
  split
  · exact checkPublicKey_relax _ _ _ _ _ _ _ (writeRegisterResult_relax ..)
  · rfl

theorem publicKeyRegisterFn_keep (name : String) (select : NearContext → List UInt8) :
    KeepGas (publicKeyRegisterFn name select) := by
  intro st args vals st2
  unfold publicKeyRegisterFn
  dsimp only
  split
  · exact checkPublicKey_keep _ _ _ _ (writeRegisterResult_keep _ _ _ _ _) vals st2
  · exact KeepsLimits.trap _ _ _ vals st2

theorem contextU64Fn_relax (name : String) (select : NearContext → UInt64) :
    RelaxComm (contextU64Fn name select) := by
  intro st args p m
  unfold contextU64Fn
  dsimp only
  rsplit

theorem contextU64Fn_keep (name : String) (select : NearContext → UInt64) :
    KeepGas (contextU64Fn name select) := by
  intro st args vals st2
  unfold contextU64Fn
  dsimp only
  split <;> intro h <;> cases h
  exact ⟨rfl, rfl⟩

theorem contextU128MemFn_relax (name : String) (select : NearContext → Nat) :
    RelaxComm (contextU128MemFn name select) := by
  intro st args p m
  unfold contextU128MemFn
  dsimp only
  split
  · exact writeU128_relax ..
  · rfl

theorem contextU128MemFn_keep (name : String) (select : NearContext → Nat) :
    KeepGas (contextU128MemFn name select) := by
  intro st args vals st2
  unfold contextU128MemFn
  dsimp only
  split
  · exact writeU128_keep _ _ _ _ vals st2
  · exact KeepsLimits.trap _ _ _ vals st2

theorem currentAccountIdFn_relax : RelaxComm currentAccountIdFn := accountIdRegisterFn_relax _ _
theorem currentAccountIdFn_keep : KeepGas currentAccountIdFn := accountIdRegisterFn_keep _ _
theorem signerAccountIdFn_relax : RelaxComm signerAccountIdFn :=
  disallowInView_relax _ _ (accountIdRegisterFn_relax _ _)
theorem signerAccountIdFn_keep : KeepGas signerAccountIdFn :=
  disallowInView_keep _ _ (accountIdRegisterFn_keep _ _)
theorem predecessorAccountIdFn_relax : RelaxComm predecessorAccountIdFn :=
  disallowInView_relax _ _ (accountIdRegisterFn_relax _ _)
theorem predecessorAccountIdFn_keep : KeepGas predecessorAccountIdFn :=
  disallowInView_keep _ _ (accountIdRegisterFn_keep _ _)
theorem signerAccountPkFn_relax : RelaxComm signerAccountPkFn :=
  disallowInView_relax _ _ (publicKeyRegisterFn_relax _ _)
theorem signerAccountPkFn_keep : KeepGas signerAccountPkFn :=
  disallowInView_keep _ _ (publicKeyRegisterFn_keep _ _)
theorem blockIndexFn_relax : RelaxComm blockIndexFn := contextU64Fn_relax _ _
theorem blockIndexFn_keep : KeepGas blockIndexFn := contextU64Fn_keep _ _
theorem blockTimestampFn_relax : RelaxComm blockTimestampFn := contextU64Fn_relax _ _
theorem blockTimestampFn_keep : KeepGas blockTimestampFn := contextU64Fn_keep _ _
theorem epochHeightFn_relax : RelaxComm epochHeightFn := contextU64Fn_relax _ _
theorem epochHeightFn_keep : KeepGas epochHeightFn := contextU64Fn_keep _ _
theorem storageUsageFn_relax : RelaxComm storageUsageFn := contextU64Fn_relax _ _
theorem storageUsageFn_keep : KeepGas storageUsageFn := contextU64Fn_keep _ _
theorem accountBalanceFn_relax : RelaxComm accountBalanceFn := contextU128MemFn_relax _ _
theorem accountBalanceFn_keep : KeepGas accountBalanceFn := contextU128MemFn_keep _ _
theorem accountLockedBalanceFn_relax : RelaxComm accountLockedBalanceFn := contextU128MemFn_relax _ _
theorem accountLockedBalanceFn_keep : KeepGas accountLockedBalanceFn := contextU128MemFn_keep _ _
theorem attachedDepositFn_relax : RelaxComm attachedDepositFn :=
  disallowInView_relax _ _ (contextU128MemFn_relax _ _)
theorem attachedDepositFn_keep : KeepGas attachedDepositFn :=
  disallowInView_keep _ _ (contextU128MemFn_keep _ _)
theorem prepaidGasFn_relax : RelaxComm prepaidGasFn := disallowInView_relax _ _ (contextU64Fn_relax _ _)
theorem prepaidGasFn_keep : KeepGas prepaidGasFn := disallowInView_keep _ _ (contextU64Fn_keep _ _)
theorem usedGasFn_relax : RelaxComm usedGasFn := disallowInView_relax _ _ (contextU64Fn_relax _ _)
theorem usedGasFn_keep : KeepGas usedGasFn := disallowInView_keep _ _ (contextU64Fn_keep _ _)
theorem validatorTotalStakeFn_relax : RelaxComm validatorTotalStakeFn := contextU128MemFn_relax _ _
theorem validatorTotalStakeFn_keep : KeepGas validatorTotalStakeFn := contextU128MemFn_keep _ _

theorem validatorStakeFn_relax : RelaxComm validatorStakeFn := by
  intro st args p m
  unfold validatorStakeFn
  dsimp only
  split
  · simp only [getMemOrReg_relaxSt]
    split
    · rfl
    · exact checkAccountId_relax _ _ _ _ _ _ _ (writeU128_relax ..)
  · rfl

theorem validatorStakeFn_keep : KeepGas validatorStakeFn := by
  intro st args vals st2
  unfold validatorStakeFn
  dsimp only
  split
  · split
    · exact KeepsLimits.trap _ _ _ vals st2
    · exact checkAccountId_keep _ _ _ _ (writeU128_keep _ _ _ _) vals st2
  · exact KeepsLimits.trap _ _ _ vals st2

/-- Split a conditional or match, and use the relax lemmas of the helpers, until both sides agree. -/
macro "prsplit" : tactic =>
  `(tactic| (repeat' (first
      | (simp only [getMemOrReg_relaxSt, readFunctionCallAction?_relax, readU128Mem_relaxSt,
          readU64Array_relax, config_relaxSt, relaxSt_promises, promiseIndexValid_relaxSt,
          relaxSt_promiseResults, relaxSt_logs, relaxSt_mem, relaxSt_registers])
      | rfl
      | contradiction
      | (exact appendPromiseActionResult_relax ..)
      | (exact writeRegisterResult_relax ..)
      | (exact writeU128_relax ..)
      | (exact createBatchPromiseResult_relax ..)
      | (exact createCallbackPromiseResult_relax ..)
      | (exact appendLogResult_relax ..)
      | (refine checkAccountId_relax _ _ _ _ _ _ _ ?_)
      | (refine checkPublicKey_relax _ _ _ _ _ _ _ ?_)
      | split
      | (simp only [*, ↓reduceIte, if_true, if_false]))))

/-- Split until each result is a trap or a return that keeps the limits. -/
macro "pksplit" : tactic =>
  `(tactic| (repeat' (first
      | (exact KeepsLimits.trap _ _ _)
      | (exact KeepsLimits.ret _ _ _ rfl rfl)
      | (exact appendPromiseActionResult_keep _ _ _ _ _)
      | (exact writeRegisterResult_keep _ _ _ _ _)
      | (exact writeU128_keep _ _ _ _)
      | (exact createBatchPromiseResult_keep _ _ _)
      | (exact createCallbackPromiseResult_keep _ _ _ _)
      | (exact appendLogResult_keep _ _)
      | (refine checkAccountId_keep _ _ _ _ ?_)
      | (refine checkPublicKey_keep _ _ _ _ ?_)
      | split)))

theorem KeepGas.of_keepsLimits {f : NearHostFn NearState}
    (h : ∀ st args, KeepsLimits st (f.invoke st args)) : KeepGas f :=
  fun st args vals st2 hh => h st args vals st2 hh

/-! ## Promises -/

theorem promiseCreateFn_relax : RelaxComm promiseCreateFn := by
  unfold promiseCreateFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseCreateFn_keep : KeepGas promiseCreateFn := by
  unfold promiseCreateFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit


theorem promiseThenFn_relax : RelaxComm promiseThenFn := by
  unfold promiseThenFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseThenFn_keep : KeepGas promiseThenFn := by
  unfold promiseThenFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseAndFn_relax : RelaxComm promiseAndFn := by
  unfold promiseAndFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseAndFn_keep : KeepGas promiseAndFn := by
  unfold promiseAndFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchCreateFn_relax : RelaxComm promiseBatchCreateFn := by
  unfold promiseBatchCreateFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchCreateFn_keep : KeepGas promiseBatchCreateFn := by
  unfold promiseBatchCreateFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchThenFn_relax : RelaxComm promiseBatchThenFn := by
  unfold promiseBatchThenFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchThenFn_keep : KeepGas promiseBatchThenFn := by
  unfold promiseBatchThenFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionCreateAccountFn_relax : RelaxComm promiseBatchActionCreateAccountFn := by
  unfold promiseBatchActionCreateAccountFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionCreateAccountFn_keep : KeepGas promiseBatchActionCreateAccountFn := by
  unfold promiseBatchActionCreateAccountFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionDeployContractFn_relax : RelaxComm promiseBatchActionDeployContractFn := by
  unfold promiseBatchActionDeployContractFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionDeployContractFn_keep : KeepGas promiseBatchActionDeployContractFn := by
  unfold promiseBatchActionDeployContractFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionFunctionCallFn_relax : RelaxComm promiseBatchActionFunctionCallFn := by
  unfold promiseBatchActionFunctionCallFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionFunctionCallFn_keep : KeepGas promiseBatchActionFunctionCallFn := by
  unfold promiseBatchActionFunctionCallFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionTransferFn_relax : RelaxComm promiseBatchActionTransferFn := by
  unfold promiseBatchActionTransferFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionTransferFn_keep : KeepGas promiseBatchActionTransferFn := by
  unfold promiseBatchActionTransferFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionStakeFn_relax : RelaxComm promiseBatchActionStakeFn := by
  unfold promiseBatchActionStakeFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionStakeFn_keep : KeepGas promiseBatchActionStakeFn := by
  unfold promiseBatchActionStakeFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionAddKeyWithFullAccessFn_relax : RelaxComm promiseBatchActionAddKeyWithFullAccessFn := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionAddKeyWithFullAccessFn_keep : KeepGas promiseBatchActionAddKeyWithFullAccessFn := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionAddKeyWithFunctionCallFn_relax : RelaxComm promiseBatchActionAddKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionAddKeyWithFunctionCallFn_keep : KeepGas promiseBatchActionAddKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionDeleteKeyFn_relax : RelaxComm promiseBatchActionDeleteKeyFn := by
  unfold promiseBatchActionDeleteKeyFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionDeleteKeyFn_keep : KeepGas promiseBatchActionDeleteKeyFn := by
  unfold promiseBatchActionDeleteKeyFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseBatchActionDeleteAccountFn_relax : RelaxComm promiseBatchActionDeleteAccountFn := by
  unfold promiseBatchActionDeleteAccountFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseBatchActionDeleteAccountFn_keep : KeepGas promiseBatchActionDeleteAccountFn := by
  unfold promiseBatchActionDeleteAccountFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseReturnFn_relax : RelaxComm promiseReturnFn := by
  unfold promiseReturnFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseReturnFn_keep : KeepGas promiseReturnFn := by
  unfold promiseReturnFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseResultFn_relax : RelaxComm promiseResultFn := by
  unfold promiseResultFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  prsplit

theorem promiseResultFn_keep : KeepGas promiseResultFn := by
  unfold promiseResultFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  pksplit

theorem promiseResultsCountFn_relax : RelaxComm promiseResultsCountFn := by
  intro st args p m
  unfold promiseResultsCountFn
  dsimp only
  prsplit

theorem promiseResultsCountFn_keep : KeepGas promiseResultsCountFn := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold promiseResultsCountFn
  dsimp only
  pksplit


/-! ## `value_return`, logs, hashes -/

theorem valueReturnFn_keep : KeepGas valueReturnFn := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold valueReturnFn
  dsimp only
  split
  · split
    · exact KeepsLimits.trap _ _ _
    · unfold checkDataLimit
      split
      · exact KeepsLimits.ret _ _ _ rfl rfl
      · split <;> exact KeepsLimits.trap _ _ _
  · exact KeepsLimits.trap _ _ _

theorem logUtf8Fn_relax : RelaxComm logUtf8Fn := by
  intro st args p m
  unfold logUtf8Fn
  dsimp only
  split
  · rw [logUtf8Read_relax]; exact appendLogResult_relax ..
  · rfl

theorem logUtf8Fn_keep : KeepGas logUtf8Fn := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold logUtf8Fn
  dsimp only
  split
  · exact appendLogResult_keep _ _
  · exact KeepsLimits.trap _ _ _

theorem logUtf16Fn_relax : RelaxComm logUtf16Fn := by
  intro st args p m
  unfold logUtf16Fn
  dsimp only
  split
  · rw [logUtf16Read_relax]; exact appendLogResult_relax ..
  · rfl

theorem logUtf16Fn_keep : KeepGas logUtf16Fn := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold logUtf16Fn
  dsimp only
  split
  · exact appendLogResult_keep _ _
  · exact KeepsLimits.trap _ _ _

theorem cryptoHostFn_relax (name : String) (params results : List ValType)
    (h : ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
      cryptoEval name (relaxSt st p m) args = cryptoEval name st args) :
    RelaxComm (cryptoHostFn name params results) := by
  intro st args p m
  unfold cryptoHostFn
  dsimp only
  rw [h]
  split
  · rfl
  · rename_i plan _
    split
    · rfl
    · simp only [config_relaxSt]
      repeat' (first
        | rfl
        | contradiction
        | (exact writeRegisterResult_relax name
            { st with host := { st.host with registerWrite := some _ } } _ _ _ p m)
        | split
        | (simp only [*, ↓reduceIte]))


theorem cryptoHostFn_keep (name : String) (params results : List ValType) :
    KeepGas (cryptoHostFn name params results) := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold cryptoHostFn
  dsimp only
  repeat' (first
    | (exact KeepsLimits.trap _ _ _)
    | (exact KeepsLimits.ret _ _ _ rfl rfl)
    | (exact writeRegisterResult_keep _ _ _ _ _)
    | split)

theorem sha256Fn_relax : RelaxComm sha256Fn :=
  cryptoHostFn_relax _ _ _ (fun _ _ _ _ => rfl)
theorem sha256Fn_keep : KeepGas sha256Fn := cryptoHostFn_keep _ _ _
theorem keccak256Fn_relax : RelaxComm keccak256Fn :=
  cryptoHostFn_relax _ _ _ (fun _ _ _ _ => rfl)
theorem keccak256Fn_keep : KeepGas keccak256Fn := cryptoHostFn_keep _ _ _
theorem keccak512Fn_relax : RelaxComm keccak512Fn :=
  cryptoHostFn_relax _ _ _ (fun _ _ _ _ => rfl)
theorem keccak512Fn_keep : KeepGas keccak512Fn := cryptoHostFn_keep _ _ _


/-! ## Metered hosts -/

theorem relaxFn_readRegister (extra : Nat) : RelaxFn (metered extra "read_register" readRegisterFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) readRegisterFn (by decide) readRegisterFn_relax readRegisterFn_keep

theorem relaxFn_registerLen (extra : Nat) : RelaxFn (metered extra "register_len" registerLenFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) registerLenFn (by decide) registerLenFn_relax registerLenFn_keep

theorem relaxFn_currentAccountId (extra : Nat) : RelaxFn (metered extra "current_account_id" currentAccountIdFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) currentAccountIdFn (by decide) currentAccountIdFn_relax currentAccountIdFn_keep

theorem relaxFn_signerAccountId (extra : Nat) : RelaxFn (metered extra "signer_account_id" signerAccountIdFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) signerAccountIdFn (by decide) signerAccountIdFn_relax signerAccountIdFn_keep

theorem relaxFn_signerAccountPk (extra : Nat) : RelaxFn (metered extra "signer_account_pk" signerAccountPkFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) signerAccountPkFn (by decide) signerAccountPkFn_relax signerAccountPkFn_keep

theorem relaxFn_predecessorAccountId (extra : Nat) : RelaxFn (metered extra "predecessor_account_id" predecessorAccountIdFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) predecessorAccountIdFn (by decide) predecessorAccountIdFn_relax predecessorAccountIdFn_keep

theorem relaxFn_input (extra : Nat) : RelaxFn (metered extra "input" inputFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) inputFn (by decide) inputFn_relax inputFn_keep

theorem relaxFn_blockIndex (extra : Nat) : RelaxFn (metered extra "block_index" blockIndexFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) blockIndexFn (by decide) blockIndexFn_relax blockIndexFn_keep

theorem relaxFn_blockTimestamp (extra : Nat) : RelaxFn (metered extra "block_timestamp" blockTimestampFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) blockTimestampFn (by decide) blockTimestampFn_relax blockTimestampFn_keep

theorem relaxFn_epochHeight (extra : Nat) : RelaxFn (metered extra "epoch_height" epochHeightFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) epochHeightFn (by decide) epochHeightFn_relax epochHeightFn_keep

theorem relaxFn_storageUsage (extra : Nat) : RelaxFn (metered extra "storage_usage" storageUsageFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) storageUsageFn (by decide) storageUsageFn_relax storageUsageFn_keep

theorem relaxFn_accountBalance (extra : Nat) : RelaxFn (metered extra "account_balance" accountBalanceFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) accountBalanceFn (by decide) accountBalanceFn_relax accountBalanceFn_keep

theorem relaxFn_accountLockedBalance (extra : Nat) : RelaxFn (metered extra "account_locked_balance" accountLockedBalanceFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) accountLockedBalanceFn (by decide) accountLockedBalanceFn_relax accountLockedBalanceFn_keep

theorem relaxFn_attachedDeposit (extra : Nat) : RelaxFn (metered extra "attached_deposit" attachedDepositFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) attachedDepositFn (by decide) attachedDepositFn_relax attachedDepositFn_keep

theorem relaxFn_prepaidGas (extra : Nat) : RelaxFn (metered extra "prepaid_gas" prepaidGasFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) prepaidGasFn (by decide) prepaidGasFn_relax prepaidGasFn_keep

theorem relaxFn_usedGas (extra : Nat) : RelaxFn (metered extra "used_gas" usedGasFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) usedGasFn (by decide) usedGasFn_relax usedGasFn_keep

theorem relaxFn_randomSeed (extra : Nat) : RelaxFn (metered extra "random_seed" randomSeedFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) randomSeedFn (by decide) randomSeedFn_relax randomSeedFn_keep

theorem relaxFn_sha256 (extra : Nat) : RelaxFn (metered extra "sha256" sha256Fn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) sha256Fn (by decide) sha256Fn_relax sha256Fn_keep

theorem relaxFn_keccak256 (extra : Nat) : RelaxFn (metered extra "keccak256" keccak256Fn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) keccak256Fn (by decide) keccak256Fn_relax keccak256Fn_keep

theorem relaxFn_keccak512 (extra : Nat) : RelaxFn (metered extra "keccak512" keccak512Fn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) keccak512Fn (by decide) keccak512Fn_relax keccak512Fn_keep

theorem relaxFn_valueReturn (extra : Nat) : RelaxFn (metered extra "value_return" valueReturnFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) valueReturnFn (by decide) valueReturnFn_relax valueReturnFn_keep

theorem relaxFn_logUtf8 (extra : Nat) : RelaxFn (metered extra "log_utf8" logUtf8Fn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) logUtf8Fn (by decide) logUtf8Fn_relax logUtf8Fn_keep

theorem relaxFn_logUtf16 (extra : Nat) : RelaxFn (metered extra "log_utf16" logUtf16Fn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) logUtf16Fn (by decide) logUtf16Fn_relax logUtf16Fn_keep

theorem relaxFn_promiseCreate (extra : Nat) : RelaxFn (metered extra "promise_create" promiseCreateFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseCreateFn (by decide) promiseCreateFn_relax promiseCreateFn_keep

theorem relaxFn_promiseThen (extra : Nat) : RelaxFn (metered extra "promise_then" promiseThenFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseThenFn (by decide) promiseThenFn_relax promiseThenFn_keep

theorem relaxFn_promiseAnd (extra : Nat) : RelaxFn (metered extra "promise_and" promiseAndFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseAndFn (by decide) promiseAndFn_relax promiseAndFn_keep

theorem relaxFn_promiseBatchCreate (extra : Nat) : RelaxFn (metered extra "promise_batch_create" promiseBatchCreateFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchCreateFn (by decide) promiseBatchCreateFn_relax promiseBatchCreateFn_keep

theorem relaxFn_promiseBatchThen (extra : Nat) : RelaxFn (metered extra "promise_batch_then" promiseBatchThenFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchThenFn (by decide) promiseBatchThenFn_relax promiseBatchThenFn_keep

theorem relaxFn_promiseBatchActionCreateAccount (extra : Nat) : RelaxFn (metered extra "promise_batch_action_create_account" promiseBatchActionCreateAccountFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionCreateAccountFn (by decide) promiseBatchActionCreateAccountFn_relax promiseBatchActionCreateAccountFn_keep

theorem relaxFn_promiseBatchActionDeployContract (extra : Nat) : RelaxFn (metered extra "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionDeployContractFn (by decide) promiseBatchActionDeployContractFn_relax promiseBatchActionDeployContractFn_keep

theorem relaxFn_promiseBatchActionFunctionCall (extra : Nat) : RelaxFn (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionFunctionCallFn (by decide) promiseBatchActionFunctionCallFn_relax promiseBatchActionFunctionCallFn_keep

theorem relaxFn_promiseBatchActionTransfer (extra : Nat) : RelaxFn (metered extra "promise_batch_action_transfer" promiseBatchActionTransferFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionTransferFn (by decide) promiseBatchActionTransferFn_relax promiseBatchActionTransferFn_keep

theorem relaxFn_promiseBatchActionStake (extra : Nat) : RelaxFn (metered extra "promise_batch_action_stake" promiseBatchActionStakeFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionStakeFn (by decide) promiseBatchActionStakeFn_relax promiseBatchActionStakeFn_keep

theorem relaxFn_promiseBatchActionAddKeyWithFullAccess (extra : Nat) : RelaxFn (metered extra "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionAddKeyWithFullAccessFn (by decide) promiseBatchActionAddKeyWithFullAccessFn_relax promiseBatchActionAddKeyWithFullAccessFn_keep

theorem relaxFn_promiseBatchActionAddKeyWithFunctionCall (extra : Nat) : RelaxFn (metered extra "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionAddKeyWithFunctionCallFn (by decide) promiseBatchActionAddKeyWithFunctionCallFn_relax promiseBatchActionAddKeyWithFunctionCallFn_keep

theorem relaxFn_promiseBatchActionDeleteKey (extra : Nat) : RelaxFn (metered extra "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionDeleteKeyFn (by decide) promiseBatchActionDeleteKeyFn_relax promiseBatchActionDeleteKeyFn_keep

theorem relaxFn_promiseBatchActionDeleteAccount (extra : Nat) : RelaxFn (metered extra "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseBatchActionDeleteAccountFn (by decide) promiseBatchActionDeleteAccountFn_relax promiseBatchActionDeleteAccountFn_keep

theorem relaxFn_promiseResultsCount (extra : Nat) : RelaxFn (metered extra "promise_results_count" promiseResultsCountFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseResultsCountFn (by decide) promiseResultsCountFn_relax promiseResultsCountFn_keep

theorem relaxFn_promiseResult (extra : Nat) : RelaxFn (metered extra "promise_result" promiseResultFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseResultFn (by decide) promiseResultFn_relax promiseResultFn_keep

theorem relaxFn_promiseReturn (extra : Nat) : RelaxFn (metered extra "promise_return" promiseReturnFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) promiseReturnFn (by decide) promiseReturnFn_relax promiseReturnFn_keep

theorem relaxFn_validatorStake (extra : Nat) : RelaxFn (metered extra "validator_stake" validatorStakeFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) validatorStakeFn (by decide) validatorStakeFn_relax validatorStakeFn_keep

theorem relaxFn_validatorTotalStake (extra : Nat) : RelaxFn (metered extra "validator_total_stake" validatorTotalStakeFn).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) validatorTotalStakeFn (by decide) validatorTotalStakeFn_relax validatorTotalStakeFn_keep


end NearLogic
