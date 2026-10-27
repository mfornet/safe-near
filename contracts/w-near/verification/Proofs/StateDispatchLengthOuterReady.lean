import Proofs.StateDispatchLengthOuterState

/-! Original-array resources derive every array premise at the actual f440 call. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] reserved inputStore arguments
set_option maxRecDepth 16384

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem paid_fields (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem store_fields (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt64) :
    fields (storeI64 s index address memory value) = fields s := rfl
private theorem global_fields (s : Store NearState) (index : Nat) (value : Value) : fields (setGlobal s index value) = fields s := rfl

theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).funcs = s.funcs ∧ (arguments s op p).modules = s.modules ∧ (arguments s op p).tables = s.tables := by
  have h : fields (arguments s op p) = fields s := by
    simp only [arguments,paid_fields,inputStore,store_fields,reserved,global_fields]
  have a := congrArg (fun x => x.1) h
  have b := congrArg (fun x => x.2.1) h
  have c := congrArg (fun x => x.2.2) h
  simp only [fields] at a b c
  exact ⟨a,b,c⟩

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.inner.memoryIndex]? = some p.memory) (hn : Native p) :
    (arguments s op p).mems[p.inner.memoryIndex]? = some p.inner.memory := by
  have mr : (paid (reserved s op p) op 3).mems[p.inner.memoryIndex]? = some p.memory := by
    simpa only [paid_mems,reserved,setGlobal] using hm
  rw [arguments,paid_mems,inputStore,hn.memory_eq]
  exact storeI64_memory _ p.inner.memoryIndex ((scratch p).toNat+8) p.memory p.register mr

theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.inner.globalIndex]? = some p.global) (hn : Native p) :
    (arguments s op p).globals[p.inner.globalIndex]? = some p.inner.global := by
  have h : (reserved s op p).globals[p.inner.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simp only [reserved,setGlobal,paid_globals]
    simp [Array.getElem?_modify,hg]
  simpa only [arguments,paid_globals,inputStore,storeI64_globals,hn.global_eq] using h

theorem arguments_credits (s : Store NearState) (op : Nat) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (13*op+rest)) : (arguments s op p).host.gas.Credits rest := by
  have b0 : 5*op+(8*op+rest) ≤13*op+rest := by omega
  have b1 : 3*op+(5*op+rest) ≤8*op+rest := by omega
  have cr : (reserved s op p).host.gas.Credits (8*op+rest) := by unfold reserved;exact paid_credits s op 5 _ (hc.mono b0)
  have ci : (inputStore s op p).host.gas.Credits (5*op+rest) := by unfold inputStore;rw [storeI64_host];exact paid_credits _ op 3 _ (cr.mono b1)
  unfold arguments
  exact paid_credits (inputStore s op p) op 5 rest ci

private def view (seed host : NearState) := {host with gas := seed.gas,gasProfile := seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host = view seed s.host := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt64) :
    view seed (storeI64 s index address memory value).host = view seed s.host := rfl
private theorem view_global (seed : NearState) (s : Store NearState) (index : Nat) (value : Value) : view seed (setGlobal s index value).host = view seed s.host := rfl

theorem arguments_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(arguments s op p).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  change view s.host (arguments s op p).host = s.host
  simp only [arguments,view_paid,inputStore,view_store,reserved,view_global]
  rfl

theorem Ready.callee (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra height : Nat) (hr : Ready s limits frame callers p extra) (tail : Expr) :
    StateDispatchLength.Ready (arguments s cfg.regularOpCost p) limits (StateDispatchLength.leafFrame frame.inst height p.inner)
      ({reservedFrame frame p with code := tail}::callers) p.inner extra := by
  let a := arguments s cfg.regularOpCost p
  let leaf := StateDispatchLength.leafFrame frame.inst height p.inner
  have fs := arguments_fields s cfg.regularOpCost p
  have cd := hr.code.transport s a p.inner frame.inst extra fs.1 fs.2.1 fs.2.2
  have pc : StateDispatchPrefix.Ready a limits leaf ({reservedFrame frame p with code := tail}::callers) p.inner.toLayout 2 := {
    code := cd.prefixCode
    interfaceLocal := rfl
    localSize := by simp [leaf,StateDispatchLength.leafFrame]
    slotNe := by decide
    memory := arguments_memory s cfg.regularOpCost p hr.memory hr.native
    global := arguments_global s cfg.regularOpCost p hr.global hr.native
    sp := by rw [hr.native.global_eq,hr.native.sp_eq]
    memoryWf := by
      rw [hr.native.memory_eq]
      exact (writeI64_spec p.memory ((scratch p).toNat+8) p.register hr.memoryWf (by have:=hr.inputWriteBound;omega)).1
    interfaceBound := hr.native.interfaceBound
    interfaceRead := hr.native.interfaceRead
    threadBound := hr.native.threadBound
    threadStatus := hr.native.threadStatus
    cellBound := hr.native.cellBound
    acquireOutBound := hr.native.acquireOutBound
    countAccepted := hr.native.countAccepted
    depth := by simpa only [List.length_cons] using hr.depth }
  exact ⟨cd,pc,rfl,by simp [StateDispatchLength.leafFrame],hr.native.highBound,hr.native.lowBound,hr.native.selectBound,
    hr.native.selectedNonzero,hr.native.selectedBound,hr.native.inputBound,hr.native.vtableBound,hr.native.releaseBound,hr.native.counterBound⟩
end WNear.Proofs.StateDispatchLengthOuter
