import Proofs.StateDecodePrefixOutputFrame
import Proofs.StateDecodePrefixBranch

/-! Actual316's twenty output instructions. The remainder is cached first;
the packed vector is read only after the high caller-output store. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode high low tagged described after

def nested(frame:CallFrame)(height:Nat)(code outerRest middleRest innerRest:Expr):=
  emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame height code) height outerRest) height middleRest) height innerRest

theorem wp_output (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code outerRest middleRest innerRest discarded:Expr)
    (p:Layout)(mi:ModuleInst)(post:Post)(hn:Native p)
    (h0:frame.locals[0]?=some (.i32 p.out))(h1:frame.locals[1]?=some (.i32 p.slice))(h2:frame.locals[2]?=some (.i32 p.scratch))
    (hsize:5≤frame.locals.size)(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some p.index)(he:s.mems[p.index]?=some p.memory)
    (hc:s.host.gas.Credits (20*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits stack (cachedFrame frame p) callers code)) rest post):
    WP cfg (fuel+20) (.next (atCode s limits stack (nested frame stack.size code outerRest middleRest innerRest) callers
      (WNear.Binary.StateDecodePrefix.output++discarded))) (20*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let n:=nested frame stack.size code outerRest middleRest innerRest
  let f:=cachedFrame n p
  let endCode:=.br 3::discarded
  let descCode:Expr:=[.local_get 1,.local_get 4,.store .i64 none {align:=2,offset:=0}]
  have h0f:f.locals[0]?=some (.i32 p.out):=by simp[f,cachedFrame,StateDecodeScalar.loaded64Frame,n,nested,emptyBlockFrame,Array.set!,h0]
  have h1f:f.locals[1]?=some (.i32 p.slice):=by simp[f,cachedFrame,StateDecodeScalar.loaded64Frame,n,nested,emptyBlockFrame,Array.set!,h1]
  have h2f:f.locals[2]?=some (.i32 p.scratch):=by simp[f,cachedFrame,StateDecodeScalar.loaded64Frame,n,nested,emptyBlockFrame,Array.set!,h2]
  have h4f:f.locals[4]?=some (.i64 (remainder p)):=by simp[f,cachedFrame,StateDecodeScalar.loaded64Frame,n,nested,emptyBlockFrame,Array.set!,show 4<frame.locals.size by omega]
  have same:f=nested (cachedFrame frame p) stack.size code outerRest middleRest innerRest:=rfl
  have specs:=memory_specs p hn
  have hmTagged:(tagged s op p).modules[f.inst]?=some mi:=by rw[tagged_modules];exact hm
  have hmLow:(low s op p).modules[f.inst]?=some mi:=by rw[low_modules];exact hm
  have hmHigh:(high s op p).modules[f.inst]?=some mi:=by rw[high_modules];exact hm
  have hmCached:(cached s op).modules[f.inst]?=some mi:=by rw[cached_modules];exact hm
  have descBound:p.slice.toNat+8≤(tagMemory p).byteSize:=by rw[specs.2.2.2.2.2];exact hn.sliceBound
  have lowOut:p.out.toNat+12≤(highMemory p).byteSize:=by rw[specs.2.1];have o:=hn.outBound;omega
  have lowSource:p.scratch.toNat+56≤(highMemory p).byteSize:=by rw[specs.2.1];have b:=hn.scratchBound;omega
  have tagOut:p.out.toNat+4≤(lowMemory p).byteSize:=by rw[specs.2.2.2.1];have o:=hn.outBound;omega
  have highOut:(p.out+12).toNat+4≤p.memory.byteSize:=by rw[out_address p hn];exact hn.outBound
  have highSource:p.scratch.toNat+60≤p.memory.byteSize:=by have b:=hn.scratchBound;omega
  have branchNext:WP cfg fuel (.next (atCode (chargedStore (described s op p) cfg.regularOpCost) limits stack (cachedFrame frame p) callers code)) rest post:=by
    simpa only[after,op] using hnext
  have branch:=wp_br_four_blocks cfg fuel rest (described s op p) limits stack (cachedFrame frame p) callers code outerRest middleRest innerRest discarded post (described_credits s op rest p hc) branchNext
  have branchWP:WP cfg (fuel+1) (.next (atCode (described s op p) limits stack f callers endCode)) (op+rest) post:=by
    simpa only[same,nested,endCode] using branch
  simp only[described,op] at branchWP
  have desc:=StateDecodeScalar.wp_store64_local cfg (fuel+1) (op+rest) (tagged s op p) limits stack f callers endCode 1 4 p.slice (remainder p) mi p.index (tagMemory p) post h1f h4f hmTagged hi (tagged_memory s op p he) descBound ((tagged_credits s op rest p hc).mono (by dsimp[op];omega)) branchWP
  have descWP:WP cfg (fuel+4) (.next (atCode (tagged s op p) limits stack f callers (descCode++endCode))) (4*op+rest) post:=by
    simpa only[descCode,List.cons_append,List.nil_append,show fuel+1+3=fuel+4 by omega,
      show 3*cfg.regularOpCost+(op+rest)=4*op+rest by dsimp[op];omega] using desc
  simp only[tagged,op] at descWP
  have tag:=wp_output_tag cfg (fuel+4) (4*op+rest) (low s op p) limits stack f callers (descCode++endCode) p.out p.scratch mi p.index (lowMemory p) post h0f h2f hmLow hi (low_memory s op p he) tagOut ((low_credits s op rest p hc).mono (by dsimp[op];omega)) descWP
  have tagWP:WP cfg (fuel+7) (.next (atCode (low s op p) limits stack f callers (outputTagCode++descCode++endCode))) (7*op+rest) post:=by
    simpa only[List.append_assoc,show fuel+4+3=fuel+7 by omega,show 3*cfg.regularOpCost+(4*op+rest)=7*op+rest by dsimp[op];omega] using tag
  simp only[low,op] at tagWP
  have lo:=wp_output_low cfg (fuel+7) (7*op+rest) (high s op p) limits stack f callers (outputTagCode++descCode++endCode) p.out p.scratch mi p.index (highMemory p) post h0f h2f hmHigh hi (high_memory s op p he) lowOut lowSource ((high_credits s op rest p hc).mono (by dsimp[op];omega)) tagWP
  have lowWP:WP cfg (fuel+11) (.next (atCode (high s op p) limits stack f callers (outputLowCode++outputTagCode++descCode++endCode))) (11*op+rest) post:=by
    simpa only[List.append_assoc,show fuel+7+4=fuel+11 by omega,show 4*cfg.regularOpCost+(7*op+rest)=11*op+rest by dsimp[op];omega] using lo
  simp only[high,op] at lowWP
  have highRule:=wp_output_high cfg (fuel+11) (11*op+rest) (cached s op) limits stack f callers (outputLowCode++outputTagCode++descCode++endCode) p.out p.scratch mi p.index p.memory post h0f h2f hmCached hi (cached_memory s op p he) highOut highSource ((cached_credits s op rest hc).mono (by dsimp[op];omega)) lowWP
  have highWP:WP cfg (fuel+17) (.next (atCode (cached s op) limits stack f callers (outputHighCode++outputLowCode++outputTagCode++descCode++endCode))) (17*op+rest) post:=by
    simpa only[List.append_assoc,show fuel+11+6=fuel+17 by omega,show 6*cfg.regularOpCost+(11*op+rest)=17*op+rest by dsimp[op];omega] using highRule
  have load:=StateDecodeScalar.wp_load64_local cfg (fuel+17) (17*op+rest) s limits stack n callers (outputHighCode++outputLowCode++outputTagCode++descCode++endCode) 2 4 {align:=3,offset:=8} p.scratch mi p.index p.memory post h2 hm hi he (by dsimp;have b:=hn.scratchBound;omega) (hc.mono (by dsimp[op];omega)) highWP
  simpa only[WNear.Binary.StateDecodePrefix.output,outputHighCode,outputLowCode,outputTagCode,descCode,endCode,List.cons_append,List.nil_append,List.append_assoc,n,
    show fuel+17+3=fuel+20 by omega,show 3*cfg.regularOpCost+(17*op+rest)=20*cfg.regularOpCost+rest by dsimp[op];omega] using load
end WNear.Proofs.StateDecodePrefix.Output
