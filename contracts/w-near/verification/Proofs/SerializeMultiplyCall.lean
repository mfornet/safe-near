import Proofs.SerializeMultiplyBody
import NearVM.MeteredWasmCall

/-! Full actual f954 typed invocation: no host/callee callback is supplied. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode after lowStore
set_option maxRecDepth 16384

def args (w : Words) : List Value := [.i32 w.out,.i64 w.aLo,.i64 w.aHi,.i64 w.bLo,.i64 w.bHi]
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (20*op)
def callAfter (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :=
  after (entered s op) op index memory w

theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (w : Words) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]?=some mi) (hfi : mi.funcAddrs[954]?=some address)
    (hfn : s.funcs[address]?=some (.wasm WNear.Binary.SerializeMultiply.signature frame.inst WNear.Binary.SerializeMultiply.function))
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb : w.out.toNat+16 ≤ memory.byteSize)
    (hd : callers.length+1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (81*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index memory w) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+62) (.next (atCode s limits (base++args w).toArray frame callers (.call 954::code)))
      (81*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals:=wasmLocals WNear.Binary.SerializeMultiply.function (args w),inst:=frame.inst,arity:=0,height:=base.length,labels:=[],code:=[]}
  let saved := {frame with code}
  have cut : op+(20*op+(60*op+rest)) ≤ 81*cfg.regularOpCost+rest := by dsimp [op]; omega
  have c0 := GasCounter.burn_credits s.host.gas op _ (hc.mono cut)
  have c1 := GasCounter.burn_credits (chargedStore s op).host.gas (20*op) _ c0.2.2.2
  have ca : active.host.gas.Credits (60*op+rest) := c1.2.2.2
  have cf := after_credits active op index rest memory w ca
  have ln : WP cfg fuel (.next (atCode (callAfter s op index memory w) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter s op index memory w) limits base [] (finalFrame leaf w) saved callers post
    rfl rfl rfl cf ln
  have nextBody : WP cfg (fuel+1) (.next (atCode (after active op index memory w) limits base.toArray (finalFrame leaf w) (saved::callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using leave
  have hmodule : active.modules[leaf.inst]?=some mi := by simpa only [active,entered,chargedStore,leaf] using hm
  have hmemory : active.mems[index]?=some memory := by simpa only [active,entered,chargedStore] using hmem
  have h0 : leaf.locals[0]?=some (.i32 w.out) := by simp [leaf,wasmLocals,WNear.Binary.SerializeMultiply.function,args]
  have h1 : leaf.locals[1]?=some (.i64 w.aLo) := by simp [leaf,wasmLocals,WNear.Binary.SerializeMultiply.function,args]
  have h2 : leaf.locals[2]?=some (.i64 w.aHi) := by simp [leaf,wasmLocals,WNear.Binary.SerializeMultiply.function,args]
  have h3 : leaf.locals[3]?=some (.i64 w.bLo) := by simp [leaf,wasmLocals,WNear.Binary.SerializeMultiply.function,args]
  have h4 : leaf.locals[4]?=some (.i64 w.bHi) := by simp [leaf,wasmLocals,WNear.Binary.SerializeMultiply.function,args]
  have hs : 12 ≤ leaf.locals.size := by simp [leaf,wasmLocals,WNear.Binary.SerializeMultiply.function,args]
  have body := wp_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] w mi index memory post
    h0 h1 h2 h3 h4 hs hmodule hi hmemory hw hb ca nextBody
  have rule := wp_call_wasm cfg ((fuel+1)+60) (60*op+rest) s limits base (args w) frame callers code 954 address mi
    WNear.Binary.SerializeMultiply.signature frame.inst WNear.Binary.SerializeMultiply.function post hm hfi hfn rfl hd
  have activation := WNear.Binary.SerializeMultiply.activation op w.out w.aLo w.aHi w.bLo w.bHi
  change activationGas op (wasmLocals WNear.Binary.SerializeMultiply.function (args w))=20*op at activation
  rw [activation] at rule
  have bn : WP cfg ((fuel+1)+60) (.next (wasmCallee active limits base frame callers code WNear.Binary.SerializeMultiply.signature frame.inst
      WNear.Binary.SerializeMultiply.function (args w))) (60*op+rest) post := by
    simpa only [wasmCallee,WNear.Binary.SerializeMultiply.function,WNear.Binary.SerializeMultiply.signature,
      leaf,saved,atCode,List.length_nil,List.append_nil] using body
  have result := rule (hc.mono cut) bn
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(20*op+(60*op+rest))=81*cfg.regularOpCost+rest by dsimp [op]; omega] using result

end WNear.Proofs.SerializeMultiply
