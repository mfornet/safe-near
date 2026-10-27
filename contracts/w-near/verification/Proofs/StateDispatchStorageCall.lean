import Proofs.StateDispatchStorageBody
import NearVM.MeteredWasmCall

/-! Actual typed f459 call from original initialized interface resources. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode StateDispatchLength.acquired StateDispatchLength.high StateDispatchLength.low checked arguments returned finalStore
set_option maxRecDepth 16384

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.interface,.i32 p.input,.i32 0,.i64 0,.i64 0],inst,arity := 1,height,labels := [],code := []}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (12 * op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  finalStore cfg (entered s cfg.regularOpCost) p ctx key value

theorem Ready.charge (s : Store NearState) (amount : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (hr : Ready s limits frame callers p extra) :
    Ready (chargedStore s amount) limits frame callers p extra := by
  have pc := hr.prefixReady
  have newPrefix : StateDispatchPrefix.Ready (chargedStore s amount) limits frame callers p.toLayout 2 := {
    code := pc.code.transport s (chargedStore s amount) p.toLayout frame.inst rfl rfl rfl
    interfaceLocal := pc.interfaceLocal
    localSize := pc.localSize
    slotNe := pc.slotNe
    memory := pc.memory
    global := pc.global
    sp := pc.sp
    memoryWf := pc.memoryWf
    interfaceBound := pc.interfaceBound
    interfaceRead := pc.interfaceRead
    threadBound := pc.threadBound
    threadStatus := pc.threadStatus
    cellBound := pc.cellBound
    acquireOutBound := pc.acquireOutBound
    countAccepted := pc.countAccepted
    depth := pc.depth }
  exact ⟨hr.code.transport s (chargedStore s amount) p frame.inst extra rfl rfl rfl,newPrefix,hr.inputLocal,hr.localSize,
    hr.highBound,hr.lowBound,hr.selectBound,hr.selectedNonzero,hr.cellBound,hr.inputBound,hr.vtableBound,hr.releaseBound,hr.counterBound⟩

private theorem tail_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key value : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hm : s.mems[p.memoryIndex]? = some (lowMemory p))
    (hr : StorageReadCalls.Ready ⟨lowMemory p,s.host⟩ ctx raw storage (keyLen p) (keyPtr p) 0 key value)
    (hc : s.host.gas.Credits (104 * cfg.regularOpCost + fee s p ctx key value + rest)) :
    (StateDispatchStorageTail.after cfg s p ctx key value).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have b0 : 10 * op + (94 * op + fee s p ctx key value + rest) ≤ 104 * cfg.regularOpCost + fee s p ctx key value + rest := by dsimp [op]; omega
  have b1 : 17 * op + fee s p ctx key value + (77 * op + rest) ≤ 94 * op + fee s p ctx key value + rest := by omega
  have b2 : 43 * op + (34 * op + rest) ≤ 77 * op + rest := by omega
  let a := StateDispatchStorageTail.arguments s op
  have ca := paid_credits s op 10 (94 * op + fee s p ctx key value + rest) (hc.mono b0)
  have hfee : fee a p ctx key value = fee s p ctx key value := by
    simpa only [a,StateDispatchStorageTail.arguments,fee] using StateReadStorage.cost_paid s op 10 (lowMemory p) ctx.trie (keyLen p) (keyPtr p) 0 key value
  have hostCredits : a.host.gas.Credits (17 * cfg.regularOpCost + fee a p ctx key value + (77 * op + rest)) := by
    rw [hfee]; exact ca.mono b1
  have ha : a.mems[p.memoryIndex]? = some (lowMemory p) := by simpa only [a,StateDispatchStorageTail.arguments,paid,chargedStore] using hm
  have ra := StateReadStorage.ready_paid s op 10 (lowMemory p) ctx raw storage (keyLen p) (keyPtr p) 0 key value hr
  have ch := StateDispatchStorageGas.host_credits cfg a p.mi p.memoryIndex (lowMemory p) ctx raw storage (keyLen p) (keyPtr p) 0 key value (77 * op + rest) hi ha ra hostCredits
  have cc := StateDispatchStorageGas.cleanup_credits (StateDispatchStorageTail.returned cfg s p ctx key value) op p.memoryIndex (34 * op + rest)
    (counter p) (lowMemory p) (ch.mono b2)
  exact StateDispatchStorageGas.finish_credits (StateDispatchStorageTail.cleaned cfg s p ctx key value) op p.globalIndex rest (scratch p) cc

theorem final_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key value : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hm : s.mems[p.memoryIndex]? = some p.memory)
    (hr : StorageReadCalls.Ready ⟨lowMemory p,s.host⟩ ctx raw storage (keyLen p) (keyPtr p) 0 key value)
    (hc : s.host.gas.Credits (248 * cfg.regularOpCost + fee s p ctx key value + rest)) :
    (finalStore cfg s p ctx key value).host.gas.Credits rest := by
  unfold finalStore
  exact tail_credits cfg (checked s cfg.regularOpCost p) p ctx raw storage key value rest hi (checked_memory s cfg.regularOpCost p hm)
    (ready_of_host_mask s.host (checked s cfg.regularOpCost p).host (lowMemory p) ctx raw storage (keyLen p) (keyPtr p) 0 key value (checked_host s cfg.regularOpCost p) hr)
    (checked_credits cfg s p ctx key value rest hc)

/-- Complete actual f459 call: twelve-unit activation, initialized lookup and
borrow, storage_read dispatch, release, accepted f432, and normal return. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key value : List UInt8) (post : Post)
    (hr : Ready s limits (leafFrame frame.inst base.length p) ({frame with code} :: callers) p extra)
    (hi : p.mi.funcAddrs[459]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.StateDispatchStorage.signature frame.inst WNear.Binary.StateDispatchStorage.function))
    (hcanonical : StorageReadCalls.Ready ⟨lowMemory p,s.host⟩ ctx raw storage (keyLen p) (keyPtr p) 0 key value)
    (hc : s.host.gas.Credits (261 * cfg.regularOpCost + fee s p ctx key value + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p ctx key value) limits
      (base ++ [Value.i64 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 169) (.next (atCode s limits (base ++ [Value.i32 p.interface,.i32 p.input]).toArray frame callers (.call 459 :: code)))
      (261 * cfg.regularOpCost + fee s p ctx key value + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  let result : UInt64 := 1
  have b0 : op + (12 * op + (248 * op + fee s p ctx key value + rest)) ≤ 261 * cfg.regularOpCost + fee s p ctx key value + rest := by dsimp [op]; omega
  have d1 : callers.length + 1 < limits.maxCallDepth := by have := hr.prefixReady.depth; simp only [List.length_cons] at *; omega
  have c0 := (GasCounter.burn_credits s.host.gas op (12 * op + (248 * op + fee s p ctx key value + rest)) (hc.mono b0)).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (12 * op) (248 * op + fee s p ctx key value + rest) c0).2.2.2
  have feeActive : fee active p ctx key value = fee s p ctx key value := by
    simpa only [active,entered,StateReadStorage.entered,fee] using StateReadStorage.cost_entered s op (lowMemory p) ctx.trie (keyLen p) (keyPtr p) 0 key value
  have ca : active.host.gas.Credits (248 * cfg.regularOpCost + fee active p ctx key value + rest) := by
    rw [feeActive]
    exact c1
  have ra := (hr.charge s op limits leaf (saved :: callers) p extra).charge (chargedStore s op) (12 * op) limits leaf (saved :: callers) p extra
  have canonicalActive : StorageReadCalls.Ready ⟨lowMemory p,active.host⟩ ctx raw storage (keyLen p) (keyPtr p) 0 key value :=
    StateReadStorage.ready_entered s op (lowMemory p) ctx raw storage (keyLen p) (keyPtr p) 0 key value hcanonical
  have cf := final_credits cfg active p ctx raw storage key value rest hr.code.prefixCode.memoryIndex hr.prefixReady.memory canonicalActive ca
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s p ctx key value) limits (base ++ [Value.i64 result]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,result] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s p ctx key value) limits base [.i64 result] (finalFrame leaf p) saved callers post rfl rfl rfl cf ln
  have stackEq : (base ++ [Value.i64 result]).toArray = base.toArray.push (.i64 result) := by apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel + 1) (.next (atCode (finalStore cfg active p ctx key value) limits
      (base.toArray.push (.i64 1)) (finalFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [callAfter,active,stackEq] using left
  have body := wp_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] p ctx raw storage key value post ra canonicalActive ca bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 167) (248 * op + fee s p ctx key value + rest) s limits base [.i32 p.interface,.i32 p.input]
    frame callers code 459 address p.mi WNear.Binary.StateDispatchStorage.signature frame.inst WNear.Binary.StateDispatchStorage.function post hr.code.prefixCode.module hi hf rfl d1
  have ac : activationGas op (wasmLocals WNear.Binary.StateDispatchStorage.function [.i32 p.interface,.i32 p.input]) = 12 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateDispatchStorage.function,ValType.default]
  rw [ac] at cr
  have arrays : #[Value.i32 p.interface,Value.i32 p.input] ++ #[Value.i32 0,Value.i64 0,Value.i64 0] =
      #[Value.i32 p.interface,Value.i32 p.input,Value.i32 0,Value.i64 0,Value.i64 0] := by apply Array.toList_inj.mp; simp
  have next : WP cfg ((fuel + 1) + 167) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDispatchStorage.signature frame.inst
      WNear.Binary.StateDispatchStorage.function [.i32 p.interface,.i32 p.input])) (248 * op + fee s p ctx key value + rest) post := by
    simpa only [feeActive,op,wasmCallee,wasmLocals,WNear.Binary.StateDispatchStorage.function,WNear.Binary.StateDispatchStorage.signature,
      leaf,leafFrame,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,ValType.default,arrays] using body
  have proof := cr (hc.mono b0) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (12 * op + (248 * op + (fee s p ctx key value + rest))) = 261 * cfg.regularOpCost + (fee s p ctx key value + rest) by dsimp [op]; omega] using proof
end WNear.Proofs.StateDispatchStorage
