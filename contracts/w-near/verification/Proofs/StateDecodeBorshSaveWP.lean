import Proofs.StateDecodeBorshSavePrefix
import Proofs.StateDecodeBorshSaveWideCompose
import Proofs.StateDecodeBorshSaveNarrow
import Proofs.StateDecodeBorshGas
import Proofs.StateDecodeBorshFrame
import Proofs.StateDecodeBorshMemoryFrame
import Proofs.StateDecodeBorshMemoryNative
import Proofs.StateDecodeBorshCode

/-! Cached opaque425 save stages, with operational memory/credits derived from
original resources. Every source uses the actual sequential memory snapshot. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode prefixGuarded prefixHighSaved prefixSaved wideDecoded wideFirstSaved wideSecondSaved wideSaved narrowDecoded narrowHighSaved narrowSaved
  prefixMemory prefixHighMemory savedPrefixMemory wideMemory wideFirstMemory wideSecondMemory savedWideMemory narrowMemory narrowHighMemory savedNarrowMemory readI32 readI64 writeI32 writeI64

private theorem add_bound(p:Layout)(hn:Native p)(m:Memory)(size:m.byteSize=p.memory.byteSize)(offset width:Nat)
    (hb:offset+width≤96): (scratch p+UInt32.ofNat offset).toNat+width≤m.byteSize:=by
  have n:=scratch_numbers p hn
  have lt:=p.sp425.toNat_lt
  have off:offset<2^32:=by omega
  rw[size,UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off,Nat.mod_eq_of_lt (by omega)]
  omega
private theorem sum_add(p:Layout)(a b:UInt32):scratch p+a+b=scratch p+(a+b):=UInt32.add_assoc _ _ _

private theorem prefix_shape(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize:=by
  have h:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  unfold prefixMemory
  exact ⟨h.1,h.2.1⟩
private theorem wide_shape(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (wideMemory p q).wf ∧(wideMemory p q).byteSize=p.memory.byteSize:=by
  have h:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) (wide_native p q hn hd)
  have prev:=savedPrefixMemory_spec p q hn hd
  have mem:(wideLayout p q).memory=savedPrefixMemory p q:=rfl
  rw[mem] at h
  unfold wideMemory
  exact ⟨h.1,h.2.1.trans prev.2.1⟩

private theorem prefix_save_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    prefixSavedStore (prefixGuarded cfg s p q) cfg.regularOpCost p.memoryIndex (prefixMemory p q) (scratch p) (prefixPacked p q)=prefixSaved cfg s p q:=by
  simp only[prefixSavedStore,prefixHighStore,prefixSavedHighMemory,prefixSaved,prefixHighSaved,prefixHighMemory,prefixLength]
private theorem wide_save_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    saveWideStore (wideDecoded cfg s p q) cfg.regularOpCost p.memoryIndex (wideMemory p q) (scratch p) (scratch p+68)=wideSaved cfg s p q:=by
  simp only[saveWideStore,saveWideFirstStore,saveWideSecondStore,saveWideLastStore,saveWideMemory1,saveWideMemory2,
    wideSaved,wideSecondSaved,wideFirstSaved,wideFirstMemory,wideSecondMemory,Nat.add_zero]
private theorem narrow_save_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    narrowSavedStore (narrowDecoded cfg s p q) cfg.regularOpCost p.memoryIndex (narrowMemory p q) (scratch p)=narrowSaved cfg s p q:=by
  simp only[narrowSavedStore,narrowHighStore,narrowLowStore,narrowSavedHighMemory,narrowSaved,narrowHighSaved,narrowHighMemory]

theorem wp_prefix_save(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(h2:frame.locals[2]?=some (.i32 (scratch p)))
    (h3:frame.locals[3]?=some (.i64 (prefixPacked p q)))
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (prefixSaved cfg s p q) limits stack (prefixSavedFrame frame (scratch p)) callers code))
      (435*cfg.regularOpCost+rest) post):
    WP cfg (fuel+10) (.next (atCode (prefixGuarded cfg s p q) limits stack frame callers
      (WNear.Binary.StateDecodeBorsh.savePrefix++code))) (445*cfg.regularOpCost+rest) post:=by
  have fields:=prefixGuarded_fields cfg s p q
  have shape:=prefix_shape p q hn hd
  have n:=scratch_numbers p hn
  have read:(scratch p+68).toNat+4≤(prefixMemory p q).byteSize:=add_bound p hn _ shape.2 68 4 (by omega)
  have cost:=prefixGuarded_credits cfg s p q hn hd (445*cfg.regularOpCost+rest)
    (hc.mono (by unfold bodyCost;simp only[Nat.add_mul];omega))
  rw[show 445*cfg.regularOpCost+rest=10*cfg.regularOpCost+(435*cfg.regularOpCost+rest) by omega]
  apply wp_save_prefix cfg fuel (435*cfg.regularOpCost+rest) (prefixGuarded cfg s p q) limits stack frame callers code
    (scratch p) (prefixPacked p q) p.mi p.memoryIndex (prefixMemory p q) post h2 h3
    (by rw[fields.2.1];exact hcode.prefixCode.child.module) hcode.prefixCode.child.memoryIndex
    (prefixGuarded_memory cfg s p q hn hd hm) shape.1 (by rw[shape.2];omega) read
  · exact cost.mono (by omega)
  · rw[prefix_save_eq];exact hnext

theorem wp_wide_save(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(h2:frame.locals[2]?=some (.i32 (scratch p)))
    (h4:frame.locals[4]?=some (.i32 (scratch p+68)))
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (wideSaved cfg s p q) limits stack frame callers code)) (243*cfg.regularOpCost+rest) post):
    WP cfg (fuel+20) (.next (atCode (wideDecoded cfg s p q) limits stack frame callers
      (WNear.Binary.StateDecodeBorsh.saveWide++code))) (263*cfg.regularOpCost+rest) post:=by
  have fields:=wideDecoded_fields cfg s p q
  have shape:=wide_shape p q hn hd
  have n:=scratch_numbers p hn
  have a40:((scratch p+32)+8).toNat+0+8≤(wideMemory p q).byteSize:=by
    rw[UInt32.add_assoc];exact add_bound p hn _ shape.2 40 8 (by omega)
  have a68:(scratch p+68).toNat+0+8≤(wideMemory p q).byteSize:=add_bound p hn _ shape.2 68 8 (by omega)
  have a48:(scratch p+48).toNat+0+4≤(wideMemory p q).byteSize:=add_bound p hn _ shape.2 48 4 (by omega)
  have a76:(scratch p+76).toNat+0+4≤(wideMemory p q).byteSize:=add_bound p hn _ shape.2 76 4 (by omega)
  have cost:=wideDecoded_credits cfg s p q hn hd (263*cfg.regularOpCost+rest)
    (hc.mono (by unfold bodyCost;simp only[Nat.add_mul];omega))
  rw[show 263*cfg.regularOpCost+rest=20*cfg.regularOpCost+(243*cfg.regularOpCost+rest) by omega]
  apply wp_save_wide cfg fuel (243*cfg.regularOpCost+rest) (wideDecoded cfg s p q) limits stack frame callers code
    (scratch p) (scratch p+68) p.mi p.memoryIndex (wideMemory p q) post h2 h4
    (by rw[fields.2.1];exact hcode.prefixCode.child.module) hcode.prefixCode.child.memoryIndex
    (wideDecoded_memory cfg s p q hn hd hm) shape.1 a40 a68 a48 a76 (by rw[shape.2];omega) (by rw[shape.2];omega)
  · exact cost.mono (by omega)
  · rw[wide_save_eq];exact hnext

theorem wp_narrow_save(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(h2:frame.locals[2]?=some (.i32 (scratch p)))
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (narrowSaved cfg s p q) limits stack frame callers code)) (57*cfg.regularOpCost+rest) post):
    WP cfg (fuel+16) (.next (atCode (narrowDecoded cfg s p q) limits stack frame callers
      (WNear.Binary.StateDecodeBorsh.saveNarrow++code))) (73*cfg.regularOpCost+rest) post:=by
  have fields:=narrowDecoded_fields cfg s p q
  have shape:=narrowMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a68:((scratch p+56)+12).toNat+4≤(narrowMemory p q).byteSize:=by
    rw[UInt32.add_assoc];exact add_bound p hn _ shape.2.1 68 4 (by omega)
  have a88:((scratch p+80)+8).toNat+4≤(narrowMemory p q).byteSize:=by
    rw[UInt32.add_assoc];exact add_bound p hn _ shape.2.1 88 4 (by omega)
  have cost:=narrowDecoded_credits cfg s p q hn hd (73*cfg.regularOpCost+rest)
    (hc.mono (by unfold bodyCost;simp only[Nat.add_mul];omega))
  rw[show 73*cfg.regularOpCost+rest=16*cfg.regularOpCost+(57*cfg.regularOpCost+rest) by omega]
  apply wp_save_narrow cfg fuel (57*cfg.regularOpCost+rest) (narrowDecoded cfg s p q) limits stack frame callers code
    (scratch p) p.mi p.memoryIndex (narrowMemory p q) post h2
    (by rw[fields.2.1];exact hcode.prefixCode.child.module) hcode.prefixCode.child.memoryIndex
    (narrowDecoded_memory cfg s p q hn hd hm) shape.1 a68 a88 (by rw[shape.2.1];omega) (by rw[shape.2.1];omega)
  · exact cost.mono (by omega)
  · rw[narrow_save_eq];exact hnext
end WNear.Proofs.StateDecodeBorsh
