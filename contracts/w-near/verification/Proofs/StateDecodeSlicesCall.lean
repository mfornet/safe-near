import Proofs.StateDecodeSlicesBody
import NearVM.MeteredWasmCall

/-! Complete typed accepted calls of deployed361 and362. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :=
  after drop (entered s op) op index memory out pointer len split

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (12*op+rest)) :
    (entered s op).host.gas.Credits rest := by
  have c0 := StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest c0

theorem callAfter_credits (drop : Bool) (s : Store NearState) (op index rest : Nat)
    (memory : Memory) (out pointer len split : UInt32)
    (hc : s.host.gas.Credits ((WNear.Binary.StateDecodeSlices.bodyCost drop+12)*op+rest)) :
    (callAfter drop s op index memory out pointer len split).host.gas.Credits rest :=
  after_credits drop (entered s op) op index rest memory out pointer len split
    (entered_credits s op _ (hc.mono (by simp only [Nat.add_mul];omega)))

/-- Only the output record is accessed. Source pointer arithmetic wraps exactly as
i32 arithmetic does; the accepted split is checked from the original argument values. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (drop : Bool) (out pointer len split location : UInt32)
    (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (he : s.mems[index]?=some memory)
    (hfi : mi.funcAddrs[WNear.Binary.StateDecodeSlices.index drop]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function drop)))
    (hwf : memory.wf) (hb : out.toNat+8≤memory.byteSize) (hn : split.toNat≤len.toNat)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((WNear.Binary.StateDecodeSlices.bodyCost drop+12)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter drop s cfg.regularOpCost index memory out pointer len split)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+WNear.Binary.StateDecodeSlices.bodySteps drop+2) (.next (atCode s limits
      (base++[Value.i32 out,.i32 pointer,.i32 len,.i32 split,.i32 location]).toArray frame callers
      (.call (WNear.Binary.StateDecodeSlices.index drop)::code)))
      ((WNear.Binary.StateDecodeSlices.bodyCost drop+12)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {
    locals:=#[.i32 out,.i32 pointer,.i32 len,.i32 split,.i32 location]
    inst:=frame.inst
    arity:=0
    height:=base.length
    labels:=[]
    code:=[]}
  let saved := {frame with code}
  have ca := entered_credits s op (WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest)
    (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter_credits drop s op index rest memory out pointer len split hc
  have ln : WP cfg fuel (.next (atCode (callAfter drop s op index memory out pointer len split) limits
      (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op,List.append_nil] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter drop s op index memory out pointer len split) limits base [] leaf saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel+1) (.next (atCode (after drop active op index memory out pointer len split) limits base.toArray leaf (saved::callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using leave
  have body := wp_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] drop out pointer len split mi index memory post
    rfl rfl rfl rfl hm hi he hwf hb hn ca bn
  have cr := wp_call_wasm cfg ((fuel+1)+WNear.Binary.StateDecodeSlices.bodySteps drop) (WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest)
    s limits base [.i32 out,.i32 pointer,.i32 len,.i32 split,.i32 location] frame callers code (WNear.Binary.StateDecodeSlices.index drop) address mi
    WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function drop) post hm hfi hf rfl hd
  rw [WNear.Binary.StateDecodeSlices.activation] at cr
  have next : WP cfg ((fuel+1)+WNear.Binary.StateDecodeSlices.bodySteps drop) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function drop) [.i32 out,.i32 pointer,.i32 len,.i32 split,.i32 location]))
      (WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.StateDecodeSlices.function,WNear.Binary.StateDecodeSlices.signature,
      leaf,saved,atCode,List.length_cons,List.length_nil,List.map_nil,List.append_nil,Array.append_empty] using body
  have proof := cr (hc.mono (by simp only [Nat.add_mul,op];omega)) next
  have ce : cfg.regularOpCost+(11*cfg.regularOpCost+(WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest))=
      (WNear.Binary.StateDecodeSlices.bodyCost drop+12)*cfg.regularOpCost+rest := by simp only [Nat.add_mul,op];omega
  have fe : (fuel+1+WNear.Binary.StateDecodeSlices.bodySteps drop)+1=fuel+WNear.Binary.StateDecodeSlices.bodySteps drop+2 := by omega
  simpa only [ce,fe] using proof
end WNear.Proofs.StateDecodeSlices
