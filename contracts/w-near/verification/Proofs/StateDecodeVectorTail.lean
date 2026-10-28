import Proofs.StateDecodeVectorSteps
import Proofs.StateDecodeScalarCache

/-! Actual373 suffix over an arbitrary post-allocation store. Caching precedes
both output writes, including when the output aliases its source record. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI64 writeI64 writeI32

def tailMemory (memory:Memory) (out scratch:UInt32) :=
  writeI64 (writeI32 memory (out.toNat+8) 0) out.toNat (readI64 memory (scratch.toNat+8))
def tailAfter (s:Store NearState) (op i gi:Nat) (memory:Memory) (out scratch:UInt32) :=
  setGlobal (paid (outputStore (paid s op 3) op i memory out (readI64 memory (scratch.toNat+8))) op 4) gi (.i32 (scratch+16))
def tailFrame (frame:CallFrame) (memory:Memory) (scratch:UInt32) :=
  {frame with locals:=frame.locals.set! 3 (.i64 (readI64 memory (scratch.toNat+8)))}
private theorem modules_paid (s:Store NearState) (op n:Nat) : (paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s:Store NearState) (op n:Nat) : (paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s:Store NearState) (op n:Nat) : (paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem output_modules (s:Store NearState) (op i:Nat) (m:Memory) (out:UInt32) (v:UInt64) :
    (outputStore s op i m out v).modules=s.modules:=by
  simp only[outputStore,StateDecodeScalar.store64Local,zeroStore,storeI64_modules,storeI32_modules,modules_paid]
private theorem output_globals (s:Store NearState) (op i:Nat) (m:Memory) (out:UInt32) (v:UInt64) :
    (outputStore s op i m out v).globals=s.globals:=by
  simp only[outputStore,StateDecodeScalar.store64Local,zeroStore,storeI64_globals,storeI32_globals,globals_paid]
private theorem output_credits (s:Store NearState) (op i rest:Nat) (m:Memory) (out:UInt32) (v:UInt64)
    (hc:s.host.gas.Credits (6*op+rest)) : (outputStore s op i m out v).host.gas.Credits rest:=by
  simpa only[outputStore,StateDecodeScalar.store64Local,zeroStore,storeI64_host,storeI32_host,paid,chargedStore] using paid_credits s op 6 rest hc

theorem wp_tail (cfg:WasmConfig) (fuel rest:Nat) (s:Store NearState) (limits:ExecLimits)
    (stack:Array Value) (frame:CallFrame) (callers:List CallFrame) (code:Expr) (out scratch:UInt32)
    (mi:ModuleInst) (i gi:Nat) (global:GlobalInst) (memory:Memory) (post:Post)
    (h0:frame.locals[0]?=some (.i32 out)) (h2:frame.locals[2]?=some (.i32 scratch)) (hsize:4≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi) (hi:mi.memAddrs[0]?=some i) (hgi:mi.globalAddrs[0]?=some gi)
    (he:s.mems[i]?=some memory) (hg:s.globals[gi]?=some global)
    (hw:memory.wf) (hs:scratch.toNat+16≤memory.byteSize) (ho:out.toNat+12≤memory.byteSize)
    (hc:s.host.gas.Credits (13*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (tailAfter s cfg.regularOpCost i gi memory out scratch) limits stack
      (tailFrame frame memory scratch) callers code)) rest post) :
    WP cfg (fuel+13) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeVector.cache++WNear.Binary.StateDecodeVector.output++WNear.Binary.StateDecodeVector.restore++code)))
      (13*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=tailFrame frame memory scratch
  let value:=readI64 memory (scratch.toNat+8)
  let cached:=paid s op 3
  let written:=outputStore cached op i memory out value
  have f0:f.locals[0]?=some (.i32 out):=by simp[f,tailFrame,Array.set!,h0]
  have f2:f.locals[2]?=some (.i32 scratch):=by simp[f,tailFrame,Array.set!,h2]
  have f3:f.locals[3]?=some (.i64 value):=by simp[f,tailFrame,value,Array.set!,show 3<frame.locals.size by omega]
  have cc:cached.host.gas.Credits (10*op+rest):=paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))
  have co:written.host.gas.Credits (4*op+rest):=output_credits cached op i _ memory out value (cc.mono (by omega))
  have wm:written.modules[frame.inst]?=some mi:=by rw[output_modules,modules_paid];exact hm
  have wg:written.globals[gi]?=some global:=by rw[output_globals,globals_paid];exact hg
  have restore:=InterfaceStack.wp_restore cfg fuel rest written limits stack f callers code mi gi global scratch 2 16 post f2 wm hgi wg co hn
  have cm:cached.modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have ce:cached.mems[i]?=some memory:=by rw[mems_paid];exact he
  have output:=wp_output cfg (fuel+4) (4*op+rest) cached limits stack f callers (WNear.Binary.StateDecodeVector.restore++code)
    out value mi i memory post f0 f3 cm hi ce hw ho (cc.mono (by omega)) restore
  have next:WP cfg (fuel+10) (.next (atCode cached limits stack
      (StateDecodeScalar.loaded64Frame frame 3 value) callers (WNear.Binary.StateDecodeVector.output++WNear.Binary.StateDecodeVector.restore++code))) (10*op+rest) post:=by
    simpa only[WNear.Binary.StateDecodeVector.restore,f,tailFrame,StateDecodeScalar.loaded64Frame,List.append_assoc,
      show 6*cfg.regularOpCost+(4*op+rest)=10*op+rest by dsimp[op];omega] using output
  have cache:=StateDecodeScalar.wp_load64_local cfg (fuel+10) (10*op+rest) s limits stack frame callers
    (WNear.Binary.StateDecodeVector.output++WNear.Binary.StateDecodeVector.restore++code) 2 3 {align:=3,offset:=8} scratch mi i memory post
    h2 hm hi he hs (hc.mono (by dsimp[op];omega)) next
  simpa only[WNear.Binary.StateDecodeVector.cache,List.cons_append,List.nil_append,
    show 3*cfg.regularOpCost+(10*op+rest)=13*cfg.regularOpCost+rest by dsimp[op];omega] using cache
end WNear.Proofs.StateDecodeVector
