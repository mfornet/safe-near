import NearVM.Metered

namespace Wasm.Near

/-- Validation accepts only successful amount/method/argument reads and a
nonempty method. The bytes remain opaque, including register-backed input. -/
theorem functionCallPlan_valid_inputs {st : Store NearState} {input : FunctionCallInputs} {sir : Bool}
    (h : (functionCallPlan st input sir).error = none) :
    ∃ amount method arguments,
      readU128Mem st input.amountPtr = some amount ∧
      getMemOrReg st input.methodPtr input.methodLen = some method ∧ method ≠ [] ∧
      getMemOrReg st input.argsPtr input.argsLen = some arguments := by
  cases ha : readU128Mem st input.amountPtr with
  | none => simp [functionCallPlan, ha] at h
  | some amount =>
    cases hm : getMemOrReg st input.methodPtr input.methodLen with
    | none => simp [functionCallPlan, ha, hm] at h
    | some method =>
      by_cases hempty : method.isEmpty = true
      · simp [functionCallPlan, ha, hm, hempty] at h
      · cases hargs : getMemOrReg st input.argsPtr input.argsLen with
        | none => simp [functionCallPlan, ha, hm, hempty, hargs] at h
        | some arguments =>
          refine ⟨amount, method, arguments, rfl, rfl, ?_, rfl⟩
          intro heq
          subst method
          simp at hempty

theorem functionCallTargetError_none_iff (st : Store NearState) (index : Nat) :
    functionCallTargetError st index = none ↔ (promiseReceiver? st index).isSome = true := by
  unfold functionCallTargetError promiseReceiver?
  cases hget : getPromise? st.host.promises index with
  | none => simp
  | some p => cases p <;> simp

theorem functionCallPlan_valid_target {st : Store NearState} {input : FunctionCallInputs} {sir : Bool}
    (h : (functionCallPlan st input sir).error = none) {index : Nat} (htarget : input.target = some index) :
    (promiseReceiver? st index).isSome = true := by
  obtain ⟨amount, method, arguments, ha, hm, hnonempty, hargs⟩ := functionCallPlan_valid_inputs h
  have hempty : method.isEmpty = false := by
    cases method <;> simp_all
  apply (functionCallTargetError_none_iff st index).mp
  cases he : functionCallTargetError st index with
  | none => rfl
  | some error => simp [functionCallPlan, ha, hm, hempty, hargs, htarget, he] at h

/-- The functional host builds the same action from the validated raw bytes,
amount and gas; validation introduces no contract-specific encoding. -/
theorem functionCallPlan_valid_action {st : Store NearState} {input : FunctionCallInputs} {sir : Bool}
    (h : (functionCallPlan st input sir).error = none) :
    ∃ amount method arguments,
      readFunctionCallAction? st input.methodLen input.methodPtr input.argsLen input.argsPtr input.amountPtr input.gas =
        some (.functionCall method arguments amount input.gas) ∧ method ≠ [] := by
  obtain ⟨amount, method, arguments, ha, hm, hnonempty, hargs⟩ := functionCallPlan_valid_inputs h
  exact ⟨amount, method, arguments, by simp [readFunctionCallAction?, ha, hm, hargs], hnonempty⟩

theorem preInvokeError_functionCall_valid {name : String} {st : Store NearState} {args : List Value}
    (h : preInvokeError name st args = none) : functionCallInputError name st args = none := by
  unfold preInvokeError at h
  cases ha : invocationArgumentError name st args with
  | some error => simp [ha] at h
  | none =>
    simp only [ha] at h
    cases hc : (if allocatesPromise name then promiseCapacityError st else none) with
    | some error => simp [hc] at h
    | none => simpa only [hc] using h

theorem preInvokeError_functionCall_action {name : String} {st : Store NearState} {args : List Value}
    {input : FunctionCallInputs} (hinputs : functionCallInputs? name args = some input)
    (h : preInvokeError name st args = none) :
    ∃ amount method arguments,
      readFunctionCallAction? st input.methodLen input.methodPtr input.argsLen input.argsPtr input.amountPtr input.gas =
        some (.functionCall method arguments amount input.gas) ∧ method ≠ [] := by
  have he := preInvokeError_functionCall_valid h
  simp only [functionCallInputError, hinputs] at he
  exact functionCallPlan_valid_action he

end Wasm.Near
