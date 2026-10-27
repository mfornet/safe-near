import Proofs.ZeroFillCall

/-! The deployed zero-length memset path never accesses memory. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def emptyAfter (s : Store NearState) (op : Nat) := paid (entered s op) op 4

/-- Zero-length f952 returns its arbitrary pointer without any memory resource
or address bound. Both caller opcode and ten-unit activation are included. -/
theorem wp_call_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr value : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.funcAddrs[952]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function))
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (15*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (emptyAfter s cfg.regularOpCost) limits
      (base++[Value.i32 ptr]).toArray frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits (base++[Value.i32 ptr,.i32 value,.i32 0]).toArray frame callers (.call 952::code)))
      (15*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length ptr value 0
  let saved := {frame with code}
  have cut : op+(10*op+(4*op+rest))≤15*cfg.regularOpCost+rest := by dsimp [op];omega
  have c0 := (GasCounter.burn_credits s.host.gas op _ (hc.mono cut)).2.2.2
  have ca := (GasCounter.burn_credits (chargedStore s op).host.gas (10*op) _ c0).2.2.2
  have cf := paid_credits active op 4 rest ca
  have ln : WP cfg fuel (.next (atCode (emptyAfter s op) limits (base++[Value.i32 ptr]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have left := wp_leave_wasm cfg fuel rest (emptyAfter s op) limits base [.i32 ptr] leaf saved callers post rfl rfl rfl cf ln
  have arr : (base++[Value.i32 ptr]).toArray=base.toArray.push (.i32 ptr) := by apply Array.toList_inj.mp;simp
  have bn : WP cfg (fuel+1) (.next (atCode (paid active op 4) limits (base.toArray.push (.i32 ptr)) leaf (saved::callers) [])) rest post := by
    simpa only [emptyAfter,active,arr] using left
  have body := wp_body_zero cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] ptr post rfl rfl ca bn
  have cr := wp_call_wasm cfg ((fuel+1)+5) (4*op+rest) s limits base [.i32 ptr,.i32 value,.i32 0]
    frame callers code 952 address mi WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function post hm hi hf rfl hd
  have activation : activationGas op (wasmLocals WNear.Binary.ZeroFill.function [.i32 ptr,.i32 value,.i32 0])=10*op := by
    simp [activationGas,wasmLocals,WNear.Binary.ZeroFill.function,ValType.default]
  rw [activation] at cr
  have arrays : #[Value.i32 ptr,Value.i32 value,Value.i32 0]++#[Value.i32 0]=#[Value.i32 ptr,Value.i32 value,Value.i32 0,Value.i32 0] := by
    apply Array.toList_inj.mp;simp
  have next : WP cfg ((fuel+1)+5) (.next (wasmCallee active limits base frame callers code WNear.Binary.ZeroFill.signature frame.inst
      WNear.Binary.ZeroFill.function [.i32 ptr,.i32 value,.i32 0])) (4*op+rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.ZeroFill.function,WNear.Binary.ZeroFill.signature,leaf,leafFrame,saved,atCode,
      List.map_cons,List.map_nil,List.append_nil,List.length_cons,List.length_nil,ValType.default,arrays] using body
  have result := cr (hc.mono cut) next
  have cost : cfg.regularOpCost+(10*op+(4*op+rest))=15*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.ZeroFill
