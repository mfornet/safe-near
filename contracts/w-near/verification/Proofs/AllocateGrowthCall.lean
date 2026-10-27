import Proofs.AllocateGrowthBody
import NearVM.MeteredWasmCall

/-! Actual typed f577 successful memory-growth call, including explicit return. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode after
set_option maxRecDepth 16384

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after cfg (entered s cfg.regularOpCost) p
def leafFrame (inst height : Nat) (p : Layout) (context : UInt32) : CallFrame :=
  {locals:=#[.i32 p.record,.i32 context,.i32 p.words,.i32 p.alignment,.i32 0],inst,arity:=0,height,labels:=[],code:=[]}

/-- All actual helper calls and the linear memory-growth charge are included.
The unused context argument is arbitrary; native premises concern original data. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (context : UInt32) (address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hi : p.mi.funcAddrs[577]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateGrowth.signature frame.inst WNear.Binary.AllocateGrowth.function))
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (178*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+137) (.next (atCode s limits (base++[Value.i32 p.record,.i32 context,.i32 p.words,.i32 p.alignment]).toArray
      frame callers (.call 577::code))) (178*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (delta p)
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p context
  let saved := {frame with code}
  have c0 := StorePair.charged_credits s op (11*op+(166*op+fee+rest)) (hc.mono (by dsimp [op,fee];omega))
  have ca : active.host.gas.Credits (166*op+fee+rest) := StorePair.charged_credits (chargedStore s op) (11*op) _ c0
  have codeActive : Code active leaf.inst p := by
    exact hcode.transport s active frame.inst p (by simp only [active,entered,chargedStore]) (by simp only [active,entered,chargedStore])
  have memActive : active.mems[p.memoryIndex]?=some p.memory := by simpa only [active,entered,chargedStore] using hm
  have next : WP cfg fuel (.next (atCode (after cfg active p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [callAfter,active,saved,atCode,op] using hnext
  have body := wp_body cfg fuel rest active limits base leaf saved callers [] p post hn codeActive rfl rfl rfl
    (by simp [leaf,leafFrame]) rfl rfl memActive hd ca next
  have cr := wp_call_wasm cfg (fuel+136) (166*op+fee+rest) s limits base [.i32 p.record,.i32 context,.i32 p.words,.i32 p.alignment]
    frame callers code 577 address p.mi WNear.Binary.AllocateGrowth.signature frame.inst WNear.Binary.AllocateGrowth.function post hcode.module hi hf rfl (by omega)
  have activation : activationGas op (wasmLocals WNear.Binary.AllocateGrowth.function [.i32 p.record,.i32 context,.i32 p.words,.i32 p.alignment])=11*op := by
    simp [activationGas,wasmLocals,WNear.Binary.AllocateGrowth.function,ValType.default]
  rw [activation] at cr
  have arrays : #[Value.i32 p.record,Value.i32 context,Value.i32 p.words,Value.i32 p.alignment]++#[Value.i32 0]=
      (leafFrame frame.inst base.length p context).locals := by apply Array.toList_inj.mp;simp [leafFrame]
  have enteredNext : WP cfg (fuel+136) (.next (wasmCallee active limits base frame callers code WNear.Binary.AllocateGrowth.signature frame.inst
      WNear.Binary.AllocateGrowth.function [.i32 p.record,.i32 context,.i32 p.words,.i32 p.alignment])) (166*op+fee+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateGrowth.function,WNear.Binary.AllocateGrowth.signature,leaf,leafFrame,saved,atCode,
      List.map_cons,List.map_nil,List.append_nil,List.length_nil,ValType.default,arrays,op,fee] using body
  have result := cr (hc.mono (by dsimp [op,fee];omega)) enteredNext
  have cost : cfg.regularOpCost+(11*op+(166*op+fee+rest))=178*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest := by dsimp [op,fee];omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocateGrowth
