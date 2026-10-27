import Proofs.StateDispatchLengthOuterPrefix
import Proofs.StateDispatchLengthOuterReady
import Proofs.StateDispatchLengthOuterTail
import Proofs.StateDispatchLengthCallFrame

/-! Complete actual f524 body, using the actual proved f440 and option stores. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode reserved inputStore arguments
set_option maxRecDepth 16384

def resultValue (s : Store NearState) (p : Layout) := StateReadRegister.lengthValue s (StateDispatchLength.register p.inner)
def looked (cfg : WasmConfig) (s : Store NearState) (p : Layout) := StateDispatchLength.callAfter cfg (arguments s cfg.regularOpCost p) p.inner

def finalStore (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDispatchLengthOuterTail.after (looked cfg s p) cfg.regularOpCost p.inner.memoryIndex p.inner.globalIndex
    (StateDispatchLength.finalMemory p.inner) p.out (scratch p) (resultValue s p)
def finalFrame (frame : CallFrame) (p : Layout) (result : UInt64) := StateDispatchLengthOuterTail.finalFrame (reservedFrame frame p) result

 theorem arguments_result (s : Store NearState) (op : Nat) (p : Layout) :
    StateReadRegister.lengthValue (arguments s op p) (StateDispatchLength.register p.inner) = resultValue s p := by
  have h := congrArg NearState.registers (arguments_host s op p)
  simp only at h
  simp only [resultValue,StateReadRegister.lengthValue,h]

 theorem arguments_base (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).host.extCosts.cost "base" = s.host.extCosts.cost "base" := by
  have h := congrArg NearState.extCosts (arguments_host s op p)
  simp only at h
  rw [h]

/-- f524's original resources derive its register-word write, real f440 call,
then both option-record stores and stack restoration. -/
theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : Expr) (p : Layout) (post : Post)
    (hr : Ready s limits frame callers p extra)
    (hc : s.host.gas.Credits (279*cfg.regularOpCost+s.host.extCosts.cost "base"+rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s p) limits base.toArray (finalFrame frame p (resultValue s p)) callers suffix)) rest post) :
    WP cfg (fuel+189) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDispatchLengthOuter.body++suffix)))
      (279*cfg.regularOpCost+s.host.extCosts.cost "base"+rest) post := by
  let op := cfg.regularOpCost
  have cut : 13*op+(266*op+s.host.extCosts.cost "base"+rest) ≤279*cfg.regularOpCost+s.host.extCosts.cost "base"+rest := by dsimp [op];omega
  have calleeCut : 254*op+s.host.extCosts.cost "base"+(12*op+rest) ≤266*op+s.host.extCosts.cost "base"+rest := by omega
  let a := arguments s op p
  let rf := reservedFrame frame p
  let r := resultValue s p
  let b := base++[Value.i32 p.out]
  let tail := WNear.Binary.StateDispatchLengthOuter.tail++suffix
  have ca := arguments_credits s op p (266*op+s.host.extCosts.cost "base"+rest) (hc.mono cut)
  have innerReady := hr.callee cfg s limits frame callers p extra b.length tail
  have af := arguments_fields s op p
  have aFunc : a.funcs[440]? = some (.wasm WNear.Binary.StateDispatchLength.signature frame.inst WNear.Binary.StateDispatchLength.function) := by
    have e : a.funcs=s.funcs := af.1
    rw [e];exact hr.lengthFunction
  have amem := arguments_memory s op p hr.memory hr.native
  have aglobal := arguments_global s op p hr.global hr.native
  have asp : p.inner.global.value=.i32 p.inner.sp := by rw [hr.native.global_eq,hr.native.sp_eq]
  have hostBudget : a.host.gas.Credits (254*cfg.regularOpCost+a.host.extCosts.cost "base"+(12*op+rest)) := by
    rw [arguments_base]
    exact ca.mono calleeCut
  have rem : (looked cfg s p).host.gas.Credits (12*op+rest) := by
    have first := (GasCounter.burn_credits a.host.gas op (12*op+(241*op+a.host.extCosts.cost "base"+(12*op+rest))) (hostBudget.mono (by dsimp [op];omega))).2.2.2
    have second := (GasCounter.burn_credits (chargedStore a op).host.gas (12*op) (241*op+a.host.extCosts.cost "base"+(12*op+rest)) first).2.2.2
    apply StateDispatchLength.final_credits cfg (StateDispatchLength.entered a op) p.inner (12*op+rest)
    simpa only [StateDispatchLength.entered,chargedStore,chargeHost,op] using second
  have hm : (looked cfg s p).mems[p.inner.memoryIndex]? = some (StateDispatchLength.finalMemory p.inner) :=
    StateDispatchLength.callAfter_memory cfg a p.inner hr.code.prefixCode.memoryIndex amem
  have fields := StateDispatchLength.callAfter_fields cfg a p.inner
  have hmCode : (looked cfg s p).modules[frame.inst]? = some p.inner.mi := by
    have e : (looked cfg s p).modules=a.modules := fields.2.1
    rw [e];exact innerReady.code.prefixCode.module
  have hg : (looked cfg s p).globals[p.inner.globalIndex]? = some p.inner.global := by
    have e : (looked cfg s p).globals=a.globals := StateDispatchLength.callAfter_globals cfg a p.inner aglobal asp
    rw [e];exact aglobal
  have mspec := innerReady.finalMemory_specs a limits (StateDispatchLength.leafFrame frame.inst b.length p.inner) ({rf with code:=tail}::callers) p.inner extra
  have inputSpec := writeI64_spec p.memory ((scratch p).toNat+8) p.register hr.memoryWf (by have:=hr.inputWriteBound;omega)
  have outBound : p.out.toNat+16 ≤(StateDispatchLength.finalMemory p.inner).byteSize := by
    rw [mspec.2.1,hr.native.memory_eq]
    exact hr.outBound.trans_eq inputSpec.2.1.symm
  have rf0 : rf.locals[0]? = some (.i32 p.out) := by simpa [rf,reservedFrame] using hr.outLocal
  have rf2 : rf.locals[2]? = some (.i32 (scratch p)) := by simp [rf,reservedFrame,show 2<frame.locals.size by have:=hr.localSize;omega]
  have tn : WP cfg fuel (.next (atCode (StateDispatchLengthOuterTail.after (looked cfg s p) op p.inner.memoryIndex p.inner.globalIndex
      (StateDispatchLength.finalMemory p.inner) p.out (scratch p) r) limits base.toArray (StateDispatchLengthOuterTail.finalFrame rf r) callers suffix)) rest post := by
    simpa only [finalStore,finalFrame,rf,r,op] using hnext
  have tailProof := StateDispatchLengthOuterTail.wp_tail cfg fuel rest (looked cfg s p) limits base.toArray rf callers suffix p.inner.mi p.inner.memoryIndex p.inner.globalIndex
    (StateDispatchLength.finalMemory p.inner) p.inner.global p.out (scratch p) r post rf0 rf2 (by simpa [rf,reservedFrame] using (show 1<frame.locals.size by have:=hr.localSize;omega))
    hmCode hr.code.prefixCode.memoryIndex hm hr.code.prefixCode.globalIndex hg mspec.1 outBound rem tn
  have stackEq : (b++[Value.i64 r]).toArray=(base.toArray.push (.i32 p.out)).push (.i64 r) := by apply Array.toList_inj.mp;simp [b]
  have callNext : WP cfg (fuel+12) (.next (atCode (StateDispatchLength.callAfter cfg a p.inner) limits
      (b++[Value.i64 (StateReadRegister.lengthValue a (StateDispatchLength.register p.inner))]).toArray rf callers tail)) (12*op+rest) post := by
    simpa only [arguments_result,stackEq,looked,a,r,tail,WNear.Binary.StateDispatchLengthOuter.tail,
      StateDispatchLengthOuterTail.code,StateDispatchLengthOuterTail.optionCode,u64Max,op,List.cons_append,List.nil_append] using tailProof
  have call := StateDispatchLength.wp_call cfg extra (fuel+12) (12*op+rest) a limits b rf callers tail p.inner 440 post innerReady hr.lengthIndex aFunc hostBudget callNext
  have prefixNext : WP cfg (fuel+176) (.next (atCode a limits
      (base++[Value.i32 p.out,.i32 1055020,.i32 (scratch p+8)]).toArray rf callers (.call 440::tail))) (266*op+s.host.extCosts.cost "base"+rest) post := by
    simpa only [b,List.append_assoc,List.cons_append,List.nil_append,hr.native.interface_eq,hr.native.input_eq,arguments_base,a,Nat.add_assoc,Nat.reduceAdd,
      show 254*cfg.regularOpCost+(s.host.extCosts.cost "base"+(12*op+rest))=266*op+(s.host.extCosts.cost "base"+rest) by dsimp [op];omega] using call
  have first := wp_prefix cfg extra (fuel+176) (266*op+s.host.extCosts.cost "base"+rest) s limits base frame callers (.call 440::tail) p post hr (hc.mono cut) prefixNext
  simpa only [WNear.Binary.StateDispatchLengthOuter.body,tail,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 13*cfg.regularOpCost+(266*op+(s.host.extCosts.cost "base"+rest))=279*cfg.regularOpCost+(s.host.extCosts.cost "base"+rest) by dsimp [op];omega] using first
end WNear.Proofs.StateDispatchLengthOuter
