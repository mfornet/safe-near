import Binary.Instance
import NearVM.Run

/-!
# What `runAttempt` does with `contract.wasm`

`runAttempt_wnear`: on an exported method of `contract.wasm`, under a
protocol whose limits accept the module and whose memory limits are v86's,
loading fails for gas before anything runs, or the method runs from
`startW`, its first frame on the instantiated store `wStore`.
-/

namespace WNear.Binary

open Wasm Wasm.Near

/-- nearcore's preparation replaces the memory with the protocol's. -/
theorem prepare_wNear (cfg : RuntimeConfig) (hmin : cfg.wasm.limits.initialMemoryPages = 1024)
    (hmax : cfg.wasm.limits.maxMemoryPages = 2048) : prepareMemory cfg wNearModule = wPrepared := by
  simp only [prepareMemory, wPrepared, hmin, hmax]

/-- The host functions nearcore links only under a protocol feature. -/
def gatedHosts : List String :=
  ["promise_batch_action_deploy_global_contract", "promise_batch_action_deploy_global_contract_by_account_id",
   "promise_batch_action_use_global_contract", "promise_batch_action_use_global_contract_by_account_id",
   "chain_id", "p256_verify", "promise_batch_action_transfer_to_gas_key",
   "promise_batch_action_add_gas_key_with_full_access", "promise_batch_action_add_gas_key_with_function_call",
   "promise_yield_create_with_id", "promise_yield_resume_with_yield_id"]

theorem disabledHost_false (cfg : RuntimeConfig) {name : String} (h : name ∉ gatedHosts) :
    disabledHost cfg name = false := by
  simp only [gatedHosts, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp [disabledHost, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem imports_ungated : (wPrepared.importDecls.all fun d => !gatedHosts.contains d.name) = true := by
  kernel_rfl

/-- `contract.wasm` imports no gated host function. -/
theorem disabled_wPrepared (cfg : RuntimeConfig) :
    wPrepared.importDecls.any (fun decl => decl.module == "env" && disabledHost cfg decl.name) = false := by
  rw [List.any_eq_false]
  intro d hd
  have := List.all_eq_true.mp imports_ungated d hd
  rw [disabledHost_false cfg (by simpa using this)]
  simp

/-- The first frame of function `i`, as `Exec.startWasm` builds it. -/
noncomputable def wFrame (i : Nat) : CallFrame :=
  let f := funcs[i - 48]!
  { locals := #[] ++ (f.locals.map ValType.default).toArray, inst := 0,
    arity := types[f.type]!.results.length, height := 0, labels := [], code := f.body }

/-- The configuration an exported function `i` starts in, from the host `h`. -/
noncomputable def startW (cfg : RuntimeConfig) (h : NearState) (i : Nat) : Config NearState :=
  { store := wStore cfg h, thread := { stack := #[], frames := [wFrame i] }, limits := execLimits }

theorem wHosts_length (cfg : RuntimeConfig) : (wHosts cfg).length = 48 := rfl

theorem funcs_size : funcs.size = 907 := by
  rw [← Array.length_toList, ← zip_codes, List.length_zipWith, ← funcTypes_toList]
  kernel_rfl

theorem startWasm_wStore (cfg : RuntimeConfig) (h : NearState) {i : Nat} (h1 : 48 ≤ i) (h2 : i < 955) :
    Exec.startWasm (wStore cfg h) execLimits i [] = some (startW cfg h i) := by
  have hi : i - 48 < funcs.size := by rw [funcs_size]; omega
  have hf : (wStore cfg h).funcs[i]? = some (.wasm types[funcs[i - 48]!.type]! 0 funcs[i - 48]!) := by
    simp only [wStore]
    rw [Array.getElem?_append_right (by simp [wHosts_length]; omega)]
    simp only [List.size_toArray, List.length_map, wHosts_length, List.getElem?_toArray, List.getElem?_map,
      Array.getElem?_toList, Array.getElem?_eq_getElem hi, Option.map_some, getElem!_pos funcs (i - 48) hi]
  unfold Exec.startWasm
  rw [hf]
  rfl

theorem wInst_funcAddr {i : Nat} (h : i < 955) : wInst.funcAddrs[i]! = i := by
  simp [wInst, getElem!_pos, h]

/-- **`runAttempt` on an exported method.** Loading fails for gas before
anything runs, or the method's function `i` runs from `startW`. -/
theorem runAttempt_wnear (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) (fuel i : Nat)
    (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955) :
    (∃ e, (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).2 = some e ∧
      runAttempt cfg wNearModule size method ctx storage fuel =
        VMOutcome.failedBefore ctx storage
          (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1.gas.burnt (.hostError e)
          (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1.gasProfile) ∨
    ((applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).2 = none ∧
      runAttempt cfg wNearModule size method ctx storage fuel =
        outcomeOfExecution ctx storage
          (runInitialized cfg.wasm fuel
            (.next (startW cfg (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1 i))).1
          (runInitialized cfg.wasm fuel
            (.next (startW cfg (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1 i))).2) := by
  obtain ⟨vm, hv, hvm⟩ := validate_wPrepared
  generalize hl : applyCharges (ctx.toNearState cfg storage) (loadingCharges size) = l
  obtain ⟨host1, err⟩ := l
  cases err with
  | some e =>
    left
    refine ⟨e, rfl, ?_⟩
    simp [runAttempt, hname, hlimit, hl]
  | none =>
    right
    refine ⟨rfl, ?_⟩
    have hstart : (prepareMemory cfg wNearModule).start = none := by rw [prepare_wNear cfg hmin hmax]; rfl
    have hexp' : wPrepared.exportFunc? method = some i := hexp
    have hft' : wPrepared.funcType? i = some { params := [], results := [] } := hft
    have halloc : HostEnv.allocate (Store.empty host1) { funcs := wHosts cfg } =
        ({ funcs := ((wHosts cfg).map fun fn => FuncInst.host fn.toHostFn).toArray, host := host1 },
          (List.range 48).map ExternVal.func) := allocate_wHosts cfg host1
    simp only [runAttempt, hname, hlimit, hl]
    rw [prepare_wNear cfg hmin hmax]
    rw [prepare_wNear cfg hmin hmax] at hstart
    simp only [hv, hstart, disabled_wPrepared, hexp', hft', resolve_wPrepared, halloc,
      instantiate_wPrepared cfg host1 vm hvm, wInst_funcAddr h2, startWasm_wStore cfg host1 h1 h2]
    rfl

end WNear.Binary
