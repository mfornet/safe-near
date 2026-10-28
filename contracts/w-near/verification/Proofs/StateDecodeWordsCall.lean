import Proofs.StateDecodeWordsBody
import NearVM.MeteredWasmCall

/-! Actual typed accepted calls of deployed f694 and f710. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after copyAfter lowStore highStore

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (index : Nat) (memory : Memory) (out source : UInt32) :=
  after wide (entered s cfg.regularOpCost) cfg.regularOpCost index memory out source
def leafFrame (inst height : Nat) (wide : Bool) (out source : UInt32) : CallFrame :=
  {locals:=#[.i32 out,.i32 source,.i32 (width wide),.i32 0],inst,arity:=0,height,labels:=[],code:=[]}

theorem after_credits (wide : Bool) (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (bodyCost wide*op+rest)) :
    (after wide s op index memory out source).host.gas.Credits rest := by
  have cut : 6*op+(copyCost wide*op+(5*op+rest))≤bodyCost wide*op+rest := by simp only [bodyCost,Nat.add_mul];omega
  have c0 := paid_credits s op 6 _ (hc.mono cut)
  have c1 := copyAfter_credits wide (paid s op 6) op index (5*op+rest) memory out source c0
  have c2 := paid_credits (copyAfter wide (paid s op 6) op index memory out source) op 2 (3*op+rest) (c1.mono (by omega))
  have c3 := paid_credits (paid (copyAfter wide (paid s op 6) op index memory out source) op 2) op 3 rest c2
  simpa only [after,statusStore,storeByte_host] using c3

theorem callAfter_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits ((bodyCost wide+11)*cfg.regularOpCost+rest)) :
    (callAfter wide cfg s index memory out source).host.gas.Credits rest := by
  let op:=cfg.regularOpCost
  have c0 := StorePair.charged_credits s op (10*op+(bodyCost wide*op+rest)) (hc.mono (by simp only [Nat.add_mul];dsimp[op];omega))
  have c1 := StorePair.charged_credits (chargedStore s op) (10*op) (bodyCost wide*op+rest) c0
  exact after_credits wide (entered s op) op index rest memory out source c1

theorem wp_call (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out source : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]?=some mi)
    (hfi : mi.funcAddrs[if wide then 694 else 710]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeWords.signature frame.inst (WNear.Binary.StateDecodeWords.function wide)))
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hwf : memory.wf) (hb : source.toNat+widthNat wide≤memory.byteSize)
    (hw : out.toNat+(widthNat wide+1)≤memory.byteSize) (hwidth : memory.byteSize≤2^32)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost wide+11)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter wide cfg s index memory out source) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps wide+2) (.next (atCode s limits
      (base++[Value.i32 out,.i32 source,.i32 (width wide)]).toArray frame callers ((.call (if wide then 694 else 710))::code)))
      ((bodyCost wide+11)*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=entered s op
  let leaf:=leafFrame frame.inst base.length wide out source
  let saved:={frame with code}
  have c0 := StorePair.charged_credits s op (10*op+(bodyCost wide*op+rest)) (hc.mono (by simp only [Nat.add_mul];dsimp[op];omega))
  have ca := StorePair.charged_credits (chargedStore s op) (10*op) (bodyCost wide*op+rest) c0
  have cf := callAfter_credits wide cfg s index rest memory out source hc
  have leaveNext : WP cfg fuel (.next (atCode (callAfter wide cfg s index memory out source) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter wide cfg s index memory out source) limits base [] (finalFrame leaf) saved callers post rfl rfl rfl cf leaveNext
  have bn : WP cfg (fuel+1) (.next (atCode (after wide active op index memory out source) limits base.toArray (finalFrame leaf) (saved::callers) [])) rest post := by
    simpa only [callAfter,active,op,List.append_nil] using leave
  have body := wp_body wide cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] out source mi index memory post
    rfl rfl rfl (by simp [leaf,leafFrame]) hm hi hmem hwf hb hw hwidth ca bn
  have activationEq : activationGas cfg.regularOpCost (wasmLocals (WNear.Binary.StateDecodeWords.function wide)
      [.i32 out,.i32 source,.i32 (width wide)])=10*op := by
    simpa [wasmLocals,WNear.Binary.StateDecodeWords.function,op,ValType.default] using WNear.Binary.StateDecodeWords.activation cfg.regularOpCost out source (width wide)
  have callCredits : s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost
      (wasmLocals (WNear.Binary.StateDecodeWords.function wide) [.i32 out,.i32 source,.i32 (width wide)])+(bodyCost wide*op+rest))) := by
    rw [activationEq]
    exact hc.mono (by simp only[Nat.add_mul];dsimp[op];omega)
  have cr := wp_call_wasm cfg ((fuel+1)+bodySteps wide) (bodyCost wide*op+rest) s limits base
    [.i32 out,.i32 source,.i32 (width wide)] frame callers code (if wide then 694 else 710) address mi
    WNear.Binary.StateDecodeWords.signature frame.inst (WNear.Binary.StateDecodeWords.function wide) post
    hm hfi hf rfl hd callCredits
  rw [activationEq] at cr
  have actual : WP cfg ((fuel+1)+bodySteps wide) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateDecodeWords.signature frame.inst (WNear.Binary.StateDecodeWords.function wide)
      [.i32 out,.i32 source,.i32 (width wide)])) (bodyCost wide*op+rest) post := by
    simpa [WNear.Binary.StateDecodeWords.function,WNear.Binary.StateDecodeWords.signature,leaf,leafFrame,
      wasmCallee,wasmLocals,atCode,saved,op,ValType.default] using body
  have result := cr actual
  have fuelEq : (fuel+1+bodySteps wide)+1=fuel+bodySteps wide+2 := by omega
  have costEq : cfg.regularOpCost+(10*op+(bodyCost wide*op+rest))=(bodyCost wide+11)*cfg.regularOpCost+rest := by
    dsimp[op];simp only[Nat.add_mul];omega
  simpa only [WNear.Binary.StateDecodeWords.function,WNear.Binary.StateDecodeWords.signature,
    fuelEq,costEq] using result
end WNear.Proofs.StateDecodeWords
