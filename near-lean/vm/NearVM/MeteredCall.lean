import NearVM.MeteredRules
import NearVM.MeteredHosts.Input

/-!
# Metered direct host calls

These rules resolve the function through the caller's module and the actual
store, invoke its `NearHostFn` contract, commit memory and host state, and retain
the caller's stack base and frames. Host calls do not pay Wasm activation gas.
-/

namespace Wasm.Near.MeteredLogic

private theorem popN_args (base args : List Value) :
    Exec.popN (base ++ args).toArray args.length = (base.toArray, args) := by
  simp only [Exec.popN, Prod.mk.injEq]
  constructor
  · apply Array.toList_inj.mp
    simp
  · apply List.ext_getElem
    · simp
    · intro index hleft hright
      simp

/-- Committing a host's memory never changes the host state it returned. -/
theorem commitHost_host (store : Store NearState) (mi : ModuleInst)
    (host : NearState) (mem : Memory) :
    (Exec.commitHost store (some mi) host (some mem)).host = host := by
  simp only [Exec.commitHost, Store.setMemOf]
  cases mi.memAddrs[0]? <;> rfl

/-- The direct call's actual operational semantics, including argument removal,
return values, host effects, and the caller's selected memory. -/
theorem step_call_host (store : Store NearState) (limits : ExecLimits)
    (base args results : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (index addr : Nat) (mi : ModuleInst) (fn : NearHostFn NearState)
    (after : HostStore NearState)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn))
    (hargs : args.length = fn.params.length)
    (hinvoke : fn.invoke ⟨(store.memOf mi).getD (Memory.new 0 none), store.host⟩ args =
      .Return results after) :
    Exec.step (atCode store limits (base ++ args).toArray frame callers (.call index :: code)) =
      .next (atCode (Exec.commitHost store (some mi) after.host (some after.mem)) limits
        (base ++ results).toArray frame callers code) := by
  have hp := popN_args base args
  rw [hargs] at hp
  simp [Exec.step, atCode, Exec.instr, Exec.Effect.call, getElem!_def, hmodule, haddr,
    Exec.enter, hfn, NearHostFn.toHostFn, hp, hinvoke]

/-- Compose a host contract and its gas bound with a caller continuation.
The ordinary call opcode is charged first; the host's own cost and promise
reservations are supplied by its semantic contract, then unused credits pass on. -/
theorem wp_call_host (cfg : WasmConfig) (fuel hostCost rest : Nat)
    (store : Store NearState) (limits : ExecLimits) (base args results : List Value)
    (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (mi : ModuleInst) (fn : NearHostFn NearState) (after : HostStore NearState)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn))
    (hargs : args.length = fn.params.length)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (hostCost + rest)))
    (hinvoke : fn.invoke
      ⟨(store.memOf mi).getD (Memory.new 0 none), (chargedStore store cfg.regularOpCost).host⟩ args =
        .Return results after)
    (hburn : after.host.gas.burnt ≤ (chargedStore store cfg.regularOpCost).host.gas.burnt + hostCost)
    (hused : after.host.gas.used ≤ (chargedStore store cfg.regularOpCost).host.gas.used + hostCost)
    (hrest : after.host.gas.Credits rest)
    (post : Post)
    (hnext : WP cfg fuel
      (.next (atCode (Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi)
        after.host (some after.mem)) limits (base ++ results).toArray frame callers code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits (base ++ args).toArray frame callers (.call index :: code)))
      (cfg.regularOpCost + (hostCost + rest)) post := by
  let c := atCode store limits (base ++ args).toArray frame callers (.call index :: code)
  let charged := atCode (chargedStore store cfg.regularOpCost) limits (base ++ args).toArray
    frame callers (.call index :: code)
  let next := atCode (Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi)
    after.host (some after.mem)) limits (base ++ results).toArray frame callers code
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [nextInstructionGas, c, atCode, Config.nextInstr?, linearInstruction, loopBackedge]
  have hop := Pays.chargeConfig c cfg.regularOpCost (hostCost + rest) hcredits
  have hstep : Exec.step charged = .next next :=
    step_call_host (chargedStore store cfg.regularOpCost) limits base args results frame callers code
      index addr mi fn after hmodule haddr hfn hargs hinvoke
  have hhost : Pays (.next charged) (hostCost + rest) (.next next) rest := by
    simp only [Pays, charged, next, StepResult.host, atCode, commitHost_host]
    exact ⟨by omega, by omega, by omega, hrest⟩
  apply wp_next (c := c) (charged := charged) (next := .next next) hcredits ?_ ?_
    (hop.2.trans hhost) hnext
  · rw [hcost]
    exact Prod.ext rfl hop.1
  · rw [hstep]
    have hf : frameTransitionGas cfg charged (.next next) = 0 := by
      simp [frameTransitionGas, charged, next, Config.callDepth, atCode]
    rw [hf]
    exact chargeWasm_zero _ (hnext.1.mono (Nat.zero_le rest))

/-- The input host's view after the caller's call-opcode charge. -/
def inputBefore (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) :
    HostStore NearState :=
  ⟨(store.memOf mi).getD (Memory.new 0 none), (chargedStore store cfg.regularOpCost).host⟩

/-- The exact successful register update from the metered input contract. -/
def inputAfter (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (register : UInt64) : HostStore NearState :=
  let before := inputBefore cfg store mi
  let paid := MeteredHosts.Input.paid before
  ⟨paid.mem, paid.host.setRegister register.toNat before.host.context.input⟩

def inputCallStore (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (register : UInt64) : Store NearState :=
  let after := inputAfter cfg store mi register
  Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) after.host (some after.mem)

/-- Calling actual metered `env.input` consumes its register-id argument and
resumes the same caller with the input in that register. Its two host charges
and call-opcode charge are discharged from credits, for arbitrary input bytes. -/
theorem wp_call_input (cfg : WasmConfig) (extra fuel rest : Nat)
    (store : Store NearState) (limits : ExecLimits) (base : List Value)
    (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (mi : ModuleInst) (register : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (metered extra "input" inputFn).toHostFn))
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = true)
    (hcredits : store.host.gas.Credits
      (cfg.regularOpCost + (MeteredHosts.Input.cost store.host + rest)))
    (post : Post)
    (hnext : WP cfg fuel
      (.next (atCode (inputCallStore cfg store mi register) limits base.toArray frame callers code))
      rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits (base ++ [Value.i64 register]).toArray frame callers (.call index :: code)))
      (cfg.regularOpCost + (MeteredHosts.Input.cost store.host + rest)) post := by
  have hc := Pays.chargeConfig
    (atCode store limits #[] frame callers []) cfg.regularOpCost
    (MeteredHosts.Input.cost store.host + rest) hcredits
  have hinputcredits : (inputBefore cfg store mi).host.gas.Credits
      (MeteredHosts.Input.cost (inputBefore cfg store mi).host + rest) := hc.2.2.2.2
  obtain ⟨hinvoke, _, _, hburn, hpromises, hrest⟩ :=
    MeteredHosts.Input.contract extra (inputBefore cfg store mi) register rest hinputcredits
      hregister hlimit
  apply wp_call_host cfg fuel (MeteredHosts.Input.cost store.host) rest store limits base
    [Value.i64 register] [] frame callers code index addr mi (metered extra "input" inputFn)
    (inputAfter cfg store mi register) hmodule haddr hfn rfl hcredits hinvoke
  · exact Nat.le_of_eq hburn
  · change (inputAfter cfg store mi register).host.gas.burnt +
        (inputAfter cfg store mi register).host.gas.promises ≤
      (chargedStore store cfg.regularOpCost).host.gas.burnt +
        (chargedStore store cfg.regularOpCost).host.gas.promises + MeteredHosts.Input.cost store.host
    change (inputAfter cfg store mi register).host.gas.burnt =
      (chargedStore store cfg.regularOpCost).host.gas.burnt + MeteredHosts.Input.cost store.host at hburn
    change (inputAfter cfg store mi register).host.gas.promises =
      (chargedStore store cfg.regularOpCost).host.gas.promises at hpromises
    omega
  · exact hrest
  · simpa only [List.append_nil, inputCallStore] using hnext

end Wasm.Near.MeteredLogic
