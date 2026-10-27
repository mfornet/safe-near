import Proofs.ZeroFillBody
import NearVM.MeteredWasmCall

/-! Typed direct call of the actual symbolic f952 memset implementation. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode loopAfter loopFrameAfter
set_option maxRecDepth 16384

def leafFrame (inst height : Nat) (ptr value len : UInt32) : CallFrame :=
  {locals:=#[.i32 ptr,.i32 value,.i32 len,.i32 0],inst,arity:=1,height,labels:=[],code:=[]}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :=
  after (entered s op) op index memory ptr value len

theorem finalFrame_shape (frame : CallFrame) (ptr len : UInt32) :
    (finalFrame frame ptr len).arity=frame.arity ∧
    (finalFrame frame ptr len).height=frame.height ∧
    (finalFrame frame ptr len).labels=frame.labels := by
  by_cases hz : len=0
  · simp only [finalFrame,ite_eq_left hz, and_self]
  · have h := loopFrameAfter_shape (startFrame frame ptr) ptr len len.toNat
    simpa only [finalFrame,ite_eq_right hz,positiveFrame,startFrame] using ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem callAfter_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (ptr value len : UInt32)
    (hc : s.host.gas.Credits ((bodyCost len+11)*op+rest)) :
    (callAfter s op index memory ptr value len).host.gas.Credits rest := by
  have cut : op+(10*op+(bodyCost len*op+rest))≤(bodyCost len+11)*op+rest := by simp only [Nat.add_mul]; omega
  have c0 := (GasCounter.burn_credits s.host.gas op _ (hc.mono cut)).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (10*op) _ c0).2.2.2
  exact after_credits (entered s op) op index rest memory ptr value len c1

/-- Actual local f952: opcode and activation, symbolic loop, and normal pointer return. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr value len : UInt32) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[952]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function))
    (hindex : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hw : memory.wf) (hb : ptr.toNat+len.toNat≤memory.byteSize) (hwidth : ptr.toNat+len.toNat≤2^32)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost len+11)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index memory ptr value len) limits
      (base++[Value.i32 ptr]).toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps len+2) (.next (atCode s limits (base++[Value.i32 ptr,.i32 value,.i32 len]).toArray frame callers (.call 952::code)))
      ((bodyCost len+11)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length ptr value len
  let saved := {frame with code}
  have cut : op+(10*op+(bodyCost len*op+rest))≤(bodyCost len+11)*cfg.regularOpCost+rest := by dsimp [op]; simp only [Nat.add_mul]; omega
  have c0 := (GasCounter.burn_credits s.host.gas op _ (hc.mono cut)).2.2.2
  have ca := (GasCounter.burn_credits (chargedStore s op).host.gas (10*op) _ c0).2.2.2
  have cf := after_credits active op index rest memory ptr value len ca
  have shape := finalFrame_shape leaf ptr len
  have ln : WP cfg fuel (.next (atCode (callAfter s op index memory ptr value len) limits (base++[Value.i32 ptr]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter s op index memory ptr value len) limits base [.i32 ptr]
    (finalFrame leaf ptr len) saved callers post (by simpa only [leaf,leafFrame,List.length_cons,List.length_nil] using shape.1.symm) (by simpa only [leaf,leafFrame] using shape.2.1) (by simpa only [leaf,leafFrame] using shape.2.2) cf ln
  have arrayEq : (base++[Value.i32 ptr]).toArray=base.toArray.push (.i32 ptr) := by
    apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel+1) (.next (atCode (after active op index memory ptr value len) limits
      (base.toArray.push (.i32 ptr)) (finalFrame leaf ptr len) (saved::callers) [])) rest post := by
    simpa only [callAfter,active,arrayEq] using left
  have moduleActive : active.modules[leaf.inst]? = some mi := by simpa only [active,entered,chargedStore,leaf,leafFrame] using hm
  have memoryActive : active.mems[index]? = some memory := by simpa only [active,entered,chargedStore] using hmem
  have body := wp_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] ptr value len mi index memory post
    rfl rfl rfl (by simp [leaf,leafFrame]) moduleActive hindex memoryActive hw hb hwidth ca bn
  have cr := wp_call_wasm cfg ((fuel+1)+bodySteps len) (bodyCost len*op+rest) s limits base [.i32 ptr,.i32 value,.i32 len]
    frame callers code 952 address mi WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function post hm hi hf rfl hd
  have activation : activationGas op (wasmLocals WNear.Binary.ZeroFill.function [.i32 ptr,.i32 value,.i32 len])=10*op := by
    simp [activationGas,wasmLocals,WNear.Binary.ZeroFill.function,ValType.default]
  rw [activation] at cr
  have arrays : #[Value.i32 ptr,Value.i32 value,Value.i32 len]++#[Value.i32 0]=#[Value.i32 ptr,Value.i32 value,Value.i32 len,Value.i32 0] := by
    apply Array.toList_inj.mp; simp
  have next : WP cfg ((fuel+1)+bodySteps len) (.next (wasmCallee active limits base frame callers code WNear.Binary.ZeroFill.signature frame.inst
      WNear.Binary.ZeroFill.function [.i32 ptr,.i32 value,.i32 len])) (bodyCost len*op+rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.ZeroFill.function,WNear.Binary.ZeroFill.signature,
      leaf,leafFrame,saved,atCode,List.map_cons,List.map_nil,List.append_nil,List.length_cons,List.length_nil,ValType.default,arrays] using body
  have result := cr (hc.mono cut) next
  have cost : cfg.regularOpCost+(10*op+(bodyCost len*op+rest))=(bodyCost len+11)*cfg.regularOpCost+rest := by
    dsimp [op]; simp only [Nat.add_mul]; omega
  rw [cost] at result
  have fuelEq : ((fuel+1)+bodySteps len)+1=fuel+bodySteps len+2 := by omega
  rw [fuelEq] at result
  exact result
end WNear.Proofs.ZeroFill
