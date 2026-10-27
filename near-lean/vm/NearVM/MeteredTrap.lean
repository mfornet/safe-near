import NearVM.MeteredCall

/-!
# Direct host-call traps

A trapping host commits its returned memory and host state before terminating
Wasm execution. Its own billing is paid together with the call opcode, exactly
as on a normal return. Protocol classification of the trap belongs to the
boundary and is not hidden in this machine-level rule.
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

/-- A host's trap terminates the caller and commits the exact host post-state. -/
theorem step_call_host_trap (store : Store NearState) (limits : ExecLimits)
    (base args : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (index addr : Nat) (mi : ModuleInst) (fn : NearHostFn NearState)
    (after : HostStore NearState) (message : String)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn))
    (hargs : args.length = fn.params.length)
    (hinvoke : fn.invoke ⟨(store.memOf mi).getD (Memory.new 0 none), store.host⟩ args =
      .Trap after message) :
    Exec.step (atCode store limits (base ++ args).toArray frame callers (.call index :: code)) =
      .trap (.host message) (Exec.commitHost store (some mi) after.host (some after.mem)) := by
  have hp := popN_args base args
  rw [hargs] at hp
  simp [Exec.step, atCode, Exec.instr, Exec.Effect.call, getElem!_def, hmodule, haddr,
    Exec.enter, hfn, NearHostFn.toHostFn, hp, hinvoke]

/-- The call opcode and host billing frame residual credits on a trap too. -/
theorem wp_call_host_trap (cfg : WasmConfig) (fuel hostCost rest : Nat)
    (store : Store NearState) (limits : ExecLimits) (base args : List Value)
    (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (mi : ModuleInst) (fn : NearHostFn NearState)
    (after : HostStore NearState) (message : String)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn))
    (hargs : args.length = fn.params.length)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (hostCost + rest)))
    (hinvoke : fn.invoke
      ⟨(store.memOf mi).getD (Memory.new 0 none), (chargedStore store cfg.regularOpCost).host⟩ args =
        .Trap after message)
    (hburn : after.host.gas.burnt ≤ (chargedStore store cfg.regularOpCost).host.gas.burnt + hostCost)
    (hused : after.host.gas.used ≤ (chargedStore store cfg.regularOpCost).host.gas.used + hostCost)
    (hrest : after.host.gas.Credits rest) :
    WP cfg (fuel + 1)
      (.next (atCode store limits (base ++ args).toArray frame callers (.call index :: code)))
      (cfg.regularOpCost + (hostCost + rest))
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host message) (Exec.commitHost (chargedStore store cfg.regularOpCost)
          (some mi) after.host (some after.mem)) ∧ error = none) := by
  let c := atCode store limits (base ++ args).toArray frame callers (.call index :: code)
  let charged := atCode (chargedStore store cfg.regularOpCost) limits (base ++ args).toArray
    frame callers (.call index :: code)
  let next : Machine := .trap (.host message)
    (Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) after.host (some after.mem))
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [nextInstructionGas, c, atCode, Config.nextInstr?, linearInstruction, loopBackedge]
  have hop := Pays.chargeConfig c cfg.regularOpCost (hostCost + rest) hcredits
  have hstep : Exec.step charged = next :=
    step_call_host_trap (chargedStore store cfg.regularOpCost) limits base args frame callers code
      index addr mi fn after message hmodule haddr hfn hargs hinvoke
  have hhost : Pays (.next charged) (hostCost + rest) next rest := by
    simp only [Pays, charged, next, StepResult.host, atCode, commitHost_host]
    exact ⟨by omega, by omega, by omega, hrest⟩
  have hnext : WP cfg fuel next rest
      (fun remaining final error => remaining = rest ∧ final = next ∧ error = none) := by
    apply wp_trap cfg fuel (.host message)
      (Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) after.host (some after.mem)) rest
    · simpa only [commitHost_host] using hrest
    · exact ⟨rfl, rfl, rfl⟩
  apply wp_next (c := c) (charged := charged) (next := next) hcredits ?_ ?_
    (hop.2.trans hhost) hnext
  · rw [hcost]
    exact Prod.ext rfl hop.1
  · rw [hstep]
    have hf : frameTransitionGas cfg charged next = 0 := rfl
    rw [hf]
    apply chargeWasm_zero
    simpa only [next, StepResult.host, commitHost_host] using hrest.mono (Nat.zero_le rest)

end Wasm.Near.MeteredLogic
