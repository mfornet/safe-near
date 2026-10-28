import Proofs.StateDecodePrefixDropPayloadCall
import Proofs.StateDecodePrefixExit

/-! Concrete316 suffix over an arbitrary current allocation store. The slice
helper reads the current descriptor, then the actual output branch restores SP. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode dropPayloadAfter exitAfter StateDecodeSlices.callAfter StateDecodeSlices.finalMemory readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def tailLayout (memory:Memory)(index:Nat)(scratch slice out count:UInt32):Output.Layout:=
  {memory:=StateDecodeSlices.finalMemory true memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count,
   index,out,scratch,slice}
def tailAfter (cfg:WasmConfig)(s:Store NearState)(index globalIndex:Nat)(memory:Memory)(scratch slice out count:UInt32):=
  exitAfter (dropPayloadAfter cfg s index memory scratch slice count) cfg.regularOpCost globalIndex (tailLayout memory index scratch slice out count)

theorem wp_tail (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code outerRest middleRest innerRest discarded:Expr)
    (mi:ModuleInst)(index globalIndex address:Nat)(global:GlobalInst)(memory:Memory)(scratch slice out count:UInt32)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h1:frame.locals[1]?=some (.i32 slice))(h2:frame.locals[2]?=some (.i32 scratch))
    (h3:frame.locals[3]?=some (.i32 count))(hs:5≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hg:mi.globalAddrs[0]?=some globalIndex)(hglobal:s.globals[globalIndex]?=some global)
    (hfi:mi.funcAddrs[361]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function true)))
    (hw:memory.wf)(hwidth:memory.byteSize≤2^32)(hb:scratch.toNat+64≤memory.byteSize)
    (hbs:slice.toNat+8≤memory.byteSize)(hbo:out.toNat+16≤memory.byteSize)
    (henough:count.toNat≤(readI32 memory (slice.toNat+4)).toNat)(hd:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits (59*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (tailAfter cfg s index globalIndex memory scratch slice out count) limits base.toArray
      (Output.cachedFrame frame (tailLayout memory index scratch slice out count)) callers code)) rest post):
    WP cfg (fuel+50) (.next (atCode s limits base.toArray
      (Output.nested frame base.toArray.size (WNear.Binary.StateDecodePrefix.restore++code) outerRest middleRest innerRest) callers
      (WNear.Binary.StateDecodePrefix.dropPayload++WNear.Binary.StateDecodePrefix.output++discarded)))
      (59*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let n:=Output.nested frame base.toArray.size (WNear.Binary.StateDecodePrefix.restore++code) outerRest middleRest innerRest
  let d:=dropPayloadAfter cfg s index memory scratch slice count
  let p:=tailLayout memory index scratch slice out count
  have nowrap:(scratch+8).toNat=scratch.toNat+8:=by
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have bound:(scratch+8).toNat+8≤memory.byteSize:=by rw[nowrap];omega
  have shape:=StateDecodeSlices.finalMemory_spec true memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count hw bound
  have pn:Output.Native p:=by
    refine ⟨shape.1,?_,?_,?_,?_⟩
    · change (StateDecodeSlices.finalMemory true memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count).byteSize≤2^32
      rw[shape.2.1];exact hwidth
    all_goals dsimp only[p,tailLayout];rw[shape.2.1];assumption
  have fields:=StateDecodeSlices.callAfter_fields true (paid s op 9) op index memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count
  have dm:d.mems[index]?=some p.memory:=by
    unfold d dropPayloadAfter
    dsimp only[p,tailLayout]
    exact StateDecodeSlices.callAfter_memory true (paid s op 9) op index memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count (by rw[mems_paid];exact he)
  have dc:d.host.gas.Credits (24*op+rest):=by
    unfold d dropPayloadAfter
    apply StateDecodeSlices.callAfter_credits true (paid s op 9) op index _ memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count
    simp only[WNear.Binary.StateDecodeSlices.bodyCost,ite_true,Nat.reduceAdd]
    exact paid_credits s op 9 _ (hc.mono (by dsimp[op];omega))
  have exit:=wp_exit cfg fuel rest d limits base.toArray frame callers code outerRest middleRest innerRest discarded p mi globalIndex global post pn h0 h1 h2 hs
    (by unfold d dropPayloadAfter;rw[fields.2.1,modules_paid];exact hm) hi dm hg
    (by unfold d dropPayloadAfter;rw[fields.2.2.2,globals_paid];exact hglobal) dc hnext
  have drop:=wp_drop_payload_call cfg (fuel+24) (24*op+rest) s limits base n callers
    (WNear.Binary.StateDecodePrefix.output++discarded) scratch slice count mi index address memory post h1 h2 h3 hm hi he hfi hf hw hbs bound henough hd
    (hc.mono (by dsimp[op];omega)) exit
  simpa only[List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 35*cfg.regularOpCost+(24*op+rest)=59*cfg.regularOpCost+rest by dsimp[op];omega] using drop
end WNear.Proofs.StateDecodePrefix
