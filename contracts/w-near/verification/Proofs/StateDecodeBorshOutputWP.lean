import Proofs.StateDecodeBorshOutputExit
import Proofs.StateDecodeBorshGas
import Proofs.StateDecodeBorshFrame
import Proofs.StateDecodeBorshMemoryFrame
import Proofs.StateDecodeBorshGlobals
import Proofs.StateDecodeBorshMemoryNative
import Proofs.StateDecodeBorshCode

/-! Actual425 final accepted output, with every current resource and credit
cut derived from the original425 store and native domain. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode prefixDecoded prefixCached prefixGuarded prefixHighSaved prefixSaved
  wideArguments wideDecoded wideFirstSaved wideSecondSaved wideSaved wideGuarded wideCached narrowArguments narrowDecoded
  narrowHighSaved narrowSaved narrowGuarded vectorHighSaved vectorSaved usageCached
  prefixMemory savedPrefixMemory wideMemory wideFirstMemory wideSecondMemory savedWideMemory narrowMemory narrowHighMemory
  savedNarrowMemory vectorHighMemory cachedMemory readI32 readI64 writeI32 writeI64

private theorem output_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    cachedOutputStore (usageCached cfg s p q) cfg.regularOpCost p.memoryIndex (cachedMemory p q) p.out425
      (wideHigh p q) (wideLow p q) (usageValue p q) (vectorPacked p q) (vectorLength p q)=tagged cfg s p q:=rfl
private theorem exit_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p):
    cachedExitStore (usageCached cfg s p q) cfg.regularOpCost p.memoryIndex p.globalIndex (cachedMemory p q)
      p.out425 (scratch p) (wideHigh p q) (wideLow p q) (usageValue p q) (vectorPacked p q) (vectorLength p q)=after cfg s p q:=by
  unfold cachedExitStore exitStore
  rw[output_eq,(scratch_numbers p hn).2.2.2]
  rfl

theorem wp_final_output(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code outer middle inner discarded:Expr)
    (p:Layout)(q:StateDecodeVectorCopy.Layout)(a581 a236:Nat)(post:Post)
    (hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global425)
    (h0:frame.locals[0]?=some (.i32 p.out425))(h2:frame.locals[2]?=some (.i32 (scratch p)))
    (h3:frame.locals[3]?=some (.i64 (wideHigh p q)))(h5:frame.locals[5]?=some (.i64 (wideLow p q)))
    (h7:frame.locals[7]?=some (.i64 (usageValue p q)))(h6:frame.locals[6]?=some (.i64 (vectorPacked p q)))
    (h1:frame.locals[1]?=some (.i32 (vectorLength p q)))
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits stack frame callers code)) rest post):
    WP cfg (fuel+33) (.next (atCode (usageCached cfg s p q) limits stack (exitNested frame stack.size code outer middle inner) callers
      (WNear.Binary.StateDecodeBorsh.output++.br 3::discarded))) (33*cfg.regularOpCost+rest) post:=by
  have fields:=usageCached_fields cfg s p q
  have mem:=usageCached_memory cfg s p q hn hd hm
  have global:=usageCached_global cfg s p q hn hd hg
  have shape:=cachedMemory_spec p q hn hd
  have cost:=usageCached_credits cfg s p q hn hd (33*cfg.regularOpCost+rest)
    (hc.mono (by unfold bodyCost;simp only[Nat.add_mul];omega))
  have bound:=hn.outBound
  have b16:(p.out425+16).toNat+8≤(cachedMemory p q).byteSize:=by
    have a:(p.out425+16).toNat=p.out425.toNat+16:=output_add p hn 16 (by omega)
    rw[shape.2.1,a];omega
  have b8:(p.out425+8).toNat+8≤(cachedMemory p q).byteSize:=by
    have a:(p.out425+8).toNat=p.out425.toNat+8:=output_add p hn 8 (by omega)
    rw[shape.2.1,a];omega
  have b24:(p.out425+24).toNat+8≤(cachedMemory p q).byteSize:=by
    have a:(p.out425+24).toNat=p.out425.toNat+24:=output_add p hn 24 (by omega)
    rw[shape.2.1,a];omega
  have b32:(p.out425+32).toNat+8≤(cachedMemory p q).byteSize:=by
    have a:(p.out425+32).toNat=p.out425.toNat+32:=output_add p hn 32 (by omega)
    rw[shape.2.1,a];omega
  have b40:(p.out425+40).toNat+4≤(cachedMemory p q).byteSize:=by
    have a:(p.out425+40).toNat=p.out425.toNat+40:=output_add p hn 40 (by omega)
    rw[shape.2.1,a];omega
  have b0:p.out425.toNat+4≤(cachedMemory p q).byteSize:=by rw[shape.2.1];omega
  exact wp_output_exit cfg fuel rest (usageCached cfg s p q) limits stack frame callers code outer middle inner discarded
    p.out425 (scratch p) (wideHigh p q) (wideLow p q) (usageValue p q) (vectorPacked p q) (vectorLength p q)
    p.mi p.memoryIndex p.globalIndex {p.global425 with value:=.i32 (scratch p)} (cachedMemory p q) post
    h0 h2 h3 h5 h7 h6 h1 (by rw[fields.2.1];exact hcode.prefixCode.child.module)
    hcode.prefixCode.child.memoryIndex mem hcode.prefixCode.child.globalIndex global shape.1 b16 b8 b24 b32 b40 b0 cost
    (by rw[exit_eq cfg s p q hn];exact hnext)
end WNear.Proofs.StateDecodeBorsh
