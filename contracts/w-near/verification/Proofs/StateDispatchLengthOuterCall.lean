import Proofs.StateDispatchLengthOuterBody
import NearVM.MeteredWasmCall

/-! Actual typed f524, with its proved nested dispatcher and option stores. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode arguments looked finalStore
set_option maxRecDepth 16384

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.out,.i64 p.register,.i32 0],inst,arity:=0,height,labels:=[],code:=[]}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) := finalStore cfg (entered s cfg.regularOpCost) p

theorem Ready.charge (s : Store NearState) (amount : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (hr : Ready s limits frame callers p extra) :
    Ready (chargedStore s amount) limits frame callers p extra := by
  exact ⟨hr.code.transport s (chargedStore s amount) p.inner frame.inst extra rfl rfl rfl,hr.native,
    hr.outLocal,hr.registerLocal,hr.localSize,hr.memory,hr.global,hr.sp,hr.memoryWf,hr.outBound,hr.inputWriteBound,
    hr.lengthIndex,hr.lengthFunction,hr.depth⟩

theorem final_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (279*cfg.regularOpCost+s.host.extCosts.cost "base"+rest)) :
    (finalStore cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have cut : 13*op+(266*op+s.host.extCosts.cost "base"+rest) ≤279*cfg.regularOpCost+s.host.extCosts.cost "base"+rest := by dsimp [op];omega
  have cut1 : op+(12*op+(241*op+s.host.extCosts.cost "base"+(12*op+rest))) ≤266*op+s.host.extCosts.cost "base"+rest := by omega
  let a := arguments s op p
  have ca := arguments_credits s op p (266*op+s.host.extCosts.cost "base"+rest) (hc.mono cut)
  have c0 := (GasCounter.burn_credits a.host.gas op (12*op+(241*op+s.host.extCosts.cost "base"+(12*op+rest))) (ca.mono cut1)).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore a op).host.gas (12*op) (241*op+s.host.extCosts.cost "base"+(12*op+rest)) c0).2.2.2
  have ce : (StateDispatchLength.entered a op).host.gas.Credits (241*cfg.regularOpCost+(StateDispatchLength.entered a op).host.extCosts.cost "base"+(12*op+rest)) := by
    simpa only [StateDispatchLength.entered,chargedStore,chargeHost,arguments_base,a,op] using c1
  have cl := StateDispatchLength.final_credits cfg (StateDispatchLength.entered a op) p.inner (12*op+rest) ce
  have rem : (looked cfg s p).host.gas.Credits (12*op+rest) := by
    simpa only [looked,StateDispatchLength.callAfter,a,op] using cl
  unfold finalStore
  exact StateDispatchLengthOuterTail.after_credits (looked cfg s p) op p.inner.memoryIndex p.inner.globalIndex rest
    (StateDispatchLength.finalMemory p.inner) p.out (scratch p) (resultValue s p) rem

/-- Full actual f524 call. The native premises describe original data and
explicit input/callee memory expressions, with all call execution proved. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hr : Ready s limits (leafFrame frame.inst base.length p) ({frame with code}::callers) p extra)
    (hi : p.inner.mi.funcAddrs[524]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.StateDispatchLengthOuter.signature frame.inst WNear.Binary.StateDispatchLengthOuter.function))
    (hc : s.host.gas.Credits (290*cfg.regularOpCost+s.host.extCosts.cost "base"+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+191) (.next (atCode s limits (base++[Value.i32 p.out,.i64 p.register]).toArray frame callers (.call 524::code)))
      (290*cfg.regularOpCost+s.host.extCosts.cost "base"+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have cut : op+(10*op+(279*op+s.host.extCosts.cost "base"+rest)) ≤290*cfg.regularOpCost+s.host.extCosts.cost "base"+rest := by dsimp [op];omega
  have depth : callers.length+1<limits.maxCallDepth := by have:=hr.depth;simp only [List.length_cons] at *;omega
  have c0 := (GasCounter.burn_credits s.host.gas op (10*op+(279*op+s.host.extCosts.cost "base"+rest)) (hc.mono cut)).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (10*op) (279*op+s.host.extCosts.cost "base"+rest) c0).2.2.2
  have ca : active.host.gas.Credits (279*cfg.regularOpCost+active.host.extCosts.cost "base"+rest) := by simpa only [active,entered,chargedStore,chargeHost,op] using c1
  have ra := (hr.charge s op limits leaf (saved::callers) p extra).charge (chargedStore s op) (10*op) limits leaf (saved::callers) p extra
  have cf := final_credits cfg active p rest ca
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s p) limits (base++[]).toArray saved callers saved.code)) rest post := by simpa only [saved,atCode,List.append_nil] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s p) limits base [] (finalFrame leaf p (resultValue active p)) saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel+1) (.next (atCode (finalStore cfg active p) limits base.toArray (finalFrame leaf p (resultValue active p)) (saved::callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using left
  have body := wp_body cfg extra (fuel+1) rest active limits base leaf (saved::callers) [] p post ra ca bn
  have cr := wp_call_wasm cfg ((fuel+1)+189) (279*op+s.host.extCosts.cost "base"+rest) s limits base [.i32 p.out,.i64 p.register]
    frame callers code 524 address p.inner.mi WNear.Binary.StateDispatchLengthOuter.signature frame.inst WNear.Binary.StateDispatchLengthOuter.function post hr.code.prefixCode.module hi hf rfl depth
  have activation : activationGas op (wasmLocals WNear.Binary.StateDispatchLengthOuter.function [.i32 p.out,.i64 p.register])=10*op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateDispatchLengthOuter.function,ValType.default]
  rw [activation] at cr
  have arrays : #[Value.i32 p.out,Value.i64 p.register]++#[Value.i32 0]=#[Value.i32 p.out,Value.i64 p.register,Value.i32 0] := by apply Array.toList_inj.mp;simp
  have next : WP cfg ((fuel+1)+189) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDispatchLengthOuter.signature frame.inst
      WNear.Binary.StateDispatchLengthOuter.function [.i32 p.out,.i64 p.register])) (279*op+s.host.extCosts.cost "base"+rest) post := by
    have fee : active.host.extCosts=s.host.extCosts := rfl
    simpa only [fee,op,wasmCallee,wasmLocals,WNear.Binary.StateDispatchLengthOuter.function,WNear.Binary.StateDispatchLengthOuter.signature,
      leaf,leafFrame,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,ValType.default,arrays] using body
  have proof := cr (hc.mono cut) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(10*op+(279*op+(s.host.extCosts.cost "base"+rest)))=290*cfg.regularOpCost+(s.host.extCosts.cost "base"+rest) by dsimp [op];omega] using proof
end WNear.Proofs.StateDispatchLengthOuter
