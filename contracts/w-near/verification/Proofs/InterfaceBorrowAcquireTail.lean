import Proofs.InterfaceBorrow

/-! The record-writing and stack-restoring tail of actual exclusive acquisition. -/
namespace WNear.Proofs.InterfaceBorrow
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

def acquireTailStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out cell : UInt32) (memory : Memory) : Store NearState :=
  setGlobal (paid (recordStore s op memoryIndex out cell memory) op 4) globalIndex (.i32 sp)

/-- The actual twelve-opcode tail, proved over an arbitrary pre-store. This
keeps the acquisition guard's concrete nested calls outside its conversion proof. -/
theorem wp_acquireTail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp out cell : UInt32) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (global : GlobalInst) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hcell : frame.locals[1]? = some (.i32 cell))
    (hborrow : frame.locals[4]? = some (.i32 cell))
    (hscratch : frame.locals[3]? = some (.i32 (sp - 16)))
    (hm : s.modules[frame.inst]? = some mi) (hgi : mi.globalAddrs[0]? = some globalIndex)
    (hg : s.globals[globalIndex]? = some global)
    (hmi : mi.memAddrs[0]? = some memoryIndex) (hmem : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hob : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (acquireTailStore s cfg.regularOpCost globalIndex memoryIndex sp out cell memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnAcquire.acquireTail ++ code))) (12 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let recorded := recordStore s op memoryIndex out cell memory
  have resource := recordStore_resources s op memoryIndex out cell memory
  have hm' : recorded.modules[frame.inst]? = some mi := by
    have projection := congrArg (fun t => t.modules[frame.inst]?) resource
    simp only at projection
    rw [← projection] at hm
    exact hm
  have hg' : recorded.globals[globalIndex]? = some global := by
    have projection := congrArg (fun t => t.globals[globalIndex]?) resource
    simp only at projection
    rw [← projection] at hg
    exact hg
  have credits := (recordStore_gas s op memoryIndex (4 * op + rest) out cell memory
    (hc.mono (by dsimp [op]; omega))).2.2
  have restoreRule := ValueReturnBorrow.wp_restore cfg fuel rest recorded limits stack frame callers code mi globalIndex
    global (sp - 16) 3 post hscratch hm' hgi hg' credits
  have restoreNext : WP cfg fuel (.next (atCode (setGlobal (paid recorded op 4) globalIndex (.i32 sp))
      limits stack frame callers code)) rest post := by
    simpa only [acquireTailStore, recorded, op] using hnext
  have restore := restoreRule (by simpa only [UInt32.sub_add_cancel] using restoreNext)
  have recordRule := wp_record cfg (fuel + 4) (4 * op + rest) s limits stack frame callers
    ([.local_get 3, .i32_const 16, .i32_binop .add, .global_set 0] ++ code)
    out cell mi memoryIndex memory post hout hcell hborrow hm hmi hmem hwf hob
    (hc.mono (by dsimp [op]; omega))
  have result := recordRule restore
  rw [show 8 * cfg.regularOpCost + (4 * op + rest) = 12 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.ValueReturnAcquire.acquireTail, List.cons_append, List.nil_append,
    Nat.add_assoc, Nat.reduceAdd] using result

theorem acquireTailStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out cell : UInt32) (memory : Memory) (hc : s.host.gas.Credits (12 * op + rest)) :
    (acquireTailStore s op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 12 * op ∧
    (acquireTailStore s op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
    (acquireTailStore s op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
  let recorded := recordStore s op memoryIndex out cell memory
  have hr := recordStore_gas s op memoryIndex (4 * op + rest) out cell memory (hc.mono (by omega))
  have hp := paid_gas recorded op 4 rest hr.2.2
  have cp := paid_credits recorded op 4 rest hr.2.2
  refine ⟨?_, hp.2.trans hr.2.1, cp⟩
  change (paid recorded op 4).host.gas.burnt = _
  rw [hp.1, hr.1]; omega

end WNear.Proofs.InterfaceBorrow
