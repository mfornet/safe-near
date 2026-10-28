import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodePrefixWrapperCallResult
import Proofs.StateDecodeScalarResult

/-! Every actual425 accepted phase preserves installed function/module/table arrays. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem charged_funcs(s:Store NearState)(op:Nat):(chargedStore s op).funcs=s.funcs:=rfl
private theorem global_funcs(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).funcs=s.funcs:=rfl
private theorem charged_modules(s:Store NearState)(op:Nat):(chargedStore s op).modules=s.modules:=rfl
private theorem global_modules(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).modules=s.modules:=rfl
private theorem charged_tables(s:Store NearState)(op:Nat):(chargedStore s op).tables=s.tables:=rfl
private theorem global_tables(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).tables=s.tables:=rfl
attribute [local irreducible] reserved prefixArguments prefixDecoded prefixCached prefixGuarded prefixHighSaved prefixSaved wideArguments wideDecoded wideFirstSaved wideSecondSaved wideSaved wideGuarded wideCached narrowArguments narrowDecoded narrowHighSaved narrowSaved narrowGuarded vectorHighSaved vectorSaved usageCached output16 output8 output24 output32 output40 tagged branched after

attribute [local irreducible] scratch count prefixMemory prefixPacked prefixLength prefixHighMemory savedPrefixMemory wideLayout wideMemory wideFirstMemory wideSecondMemory savedWideMemory wideHigh wideLow narrowLayout narrowMemory narrowHighMemory savedNarrowMemory vectorLength vectorHighMemory vectorPacked cachedMemory usageValue output16Memory output8Memory output24Memory output32Memory output40Memory finalMemory

theorem reserved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    (reserved s cfg.regularOpCost p).funcs=s.funcs ∧(reserved s cfg.regularOpCost p).modules=s.modules ∧(reserved s cfg.regularOpCost p).tables=s.tables:=by
  simp only[reserved,setGlobal,paid_funcs,paid_modules,paid_tables,and_self]

theorem prefixArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    (prefixArguments s cfg.regularOpCost p).funcs=s.funcs ∧(prefixArguments s cfg.regularOpCost p).modules=s.modules ∧(prefixArguments s cfg.regularOpCost p).tables=s.tables:=by
  have h:=reserved_fields cfg s p
  unfold prefixArguments
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem prefixDecoded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixDecoded cfg s p q).funcs=s.funcs ∧(prefixDecoded cfg s p q).modules=s.modules ∧(prefixDecoded cfg s p q).tables=s.tables:=by
  have h:=StateDecodePrefixWrapper.callAfter_fields cfg (prefixArguments s cfg.regularOpCost p) p.toPrefixWrapper q
  have v:=prefixArguments_fields cfg s p
  unfold prefixDecoded
  exact ⟨h.1.trans v.1,h.2.1.trans v.2.1,h.2.2.trans v.2.2⟩

theorem prefixCached_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixCached cfg s p q).funcs=s.funcs ∧(prefixCached cfg s p q).modules=s.modules ∧(prefixCached cfg s p q).tables=s.tables:=by
  have h:=prefixDecoded_fields cfg s p q
  unfold prefixCached
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem prefixGuarded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixGuarded cfg s p q).funcs=s.funcs ∧(prefixGuarded cfg s p q).modules=s.modules ∧(prefixGuarded cfg s p q).tables=s.tables:=by
  have h:=prefixCached_fields cfg s p q
  unfold prefixGuarded
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem prefixHighSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixHighSaved cfg s p q).funcs=s.funcs ∧(prefixHighSaved cfg s p q).modules=s.modules ∧(prefixHighSaved cfg s p q).tables=s.tables:=by
  have h:=prefixGuarded_fields cfg s p q
  unfold prefixHighSaved
  rw[storeI32_funcs,paid_funcs,storeI32_modules,paid_modules,storeI32_tables,paid_tables]
  exact h

theorem prefixSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixSaved cfg s p q).funcs=s.funcs ∧(prefixSaved cfg s p q).modules=s.modules ∧(prefixSaved cfg s p q).tables=s.tables:=by
  have h:=prefixHighSaved_fields cfg s p q
  unfold prefixSaved
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem wideArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideArguments cfg s p q).funcs=s.funcs ∧(wideArguments cfg s p q).modules=s.modules ∧(wideArguments cfg s p q).tables=s.tables:=by
  have h:=prefixSaved_fields cfg s p q
  unfold wideArguments
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem wideDecoded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideDecoded cfg s p q).funcs=s.funcs ∧(wideDecoded cfg s p q).modules=s.modules ∧(wideDecoded cfg s p q).tables=s.tables:=by
  have h:=StateDecodeScalar.callAfter_fields true cfg (wideArguments cfg s p q) (wideLayout p q)
  have v:=wideArguments_fields cfg s p q
  unfold wideDecoded
  exact ⟨h.1.trans v.1,h.2.1.trans v.2.1,h.2.2.trans v.2.2⟩

theorem wideFirstSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideFirstSaved cfg s p q).funcs=s.funcs ∧(wideFirstSaved cfg s p q).modules=s.modules ∧(wideFirstSaved cfg s p q).tables=s.tables:=by
  have h:=wideDecoded_fields cfg s p q
  unfold wideFirstSaved
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem wideSecondSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideSecondSaved cfg s p q).funcs=s.funcs ∧(wideSecondSaved cfg s p q).modules=s.modules ∧(wideSecondSaved cfg s p q).tables=s.tables:=by
  have h:=wideFirstSaved_fields cfg s p q
  unfold wideSecondSaved
  rw[storeI32_funcs,paid_funcs,storeI32_modules,paid_modules,storeI32_tables,paid_tables]
  exact h

theorem wideSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideSaved cfg s p q).funcs=s.funcs ∧(wideSaved cfg s p q).modules=s.modules ∧(wideSaved cfg s p q).tables=s.tables:=by
  have h:=wideSecondSaved_fields cfg s p q
  unfold wideSaved
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem wideGuarded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideGuarded cfg s p q).funcs=s.funcs ∧(wideGuarded cfg s p q).modules=s.modules ∧(wideGuarded cfg s p q).tables=s.tables:=by
  have h:=wideSaved_fields cfg s p q
  unfold wideGuarded
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem wideCached_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideCached cfg s p q).funcs=s.funcs ∧(wideCached cfg s p q).modules=s.modules ∧(wideCached cfg s p q).tables=s.tables:=by
  have h:=wideGuarded_fields cfg s p q
  unfold wideCached
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem narrowArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (narrowArguments cfg s p q).funcs=s.funcs ∧(narrowArguments cfg s p q).modules=s.modules ∧(narrowArguments cfg s p q).tables=s.tables:=by
  have h:=wideCached_fields cfg s p q
  unfold narrowArguments
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem narrowDecoded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (narrowDecoded cfg s p q).funcs=s.funcs ∧(narrowDecoded cfg s p q).modules=s.modules ∧(narrowDecoded cfg s p q).tables=s.tables:=by
  have h:=StateDecodeScalar.callAfter_fields false cfg (narrowArguments cfg s p q) (narrowLayout p q)
  have v:=narrowArguments_fields cfg s p q
  unfold narrowDecoded
  exact ⟨h.1.trans v.1,h.2.1.trans v.2.1,h.2.2.trans v.2.2⟩

theorem narrowHighSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (narrowHighSaved cfg s p q).funcs=s.funcs ∧(narrowHighSaved cfg s p q).modules=s.modules ∧(narrowHighSaved cfg s p q).tables=s.tables:=by
  have h:=narrowDecoded_fields cfg s p q
  unfold narrowHighSaved
  rw[storeI32_funcs,paid_funcs,storeI32_modules,paid_modules,storeI32_tables,paid_tables]
  exact h

theorem narrowSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (narrowSaved cfg s p q).funcs=s.funcs ∧(narrowSaved cfg s p q).modules=s.modules ∧(narrowSaved cfg s p q).tables=s.tables:=by
  have h:=narrowHighSaved_fields cfg s p q
  unfold narrowSaved
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem narrowGuarded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (narrowGuarded cfg s p q).funcs=s.funcs ∧(narrowGuarded cfg s p q).modules=s.modules ∧(narrowGuarded cfg s p q).tables=s.tables:=by
  have h:=narrowSaved_fields cfg s p q
  unfold narrowGuarded
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem vectorHighSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (vectorHighSaved cfg s p q).funcs=s.funcs ∧(vectorHighSaved cfg s p q).modules=s.modules ∧(vectorHighSaved cfg s p q).tables=s.tables:=by
  have h:=narrowGuarded_fields cfg s p q
  unfold vectorHighSaved
  rw[storeI32_funcs,paid_funcs,storeI32_modules,paid_modules,storeI32_tables,paid_tables]
  exact h

theorem vectorSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (vectorSaved cfg s p q).funcs=s.funcs ∧(vectorSaved cfg s p q).modules=s.modules ∧(vectorSaved cfg s p q).tables=s.tables:=by
  have h:=vectorHighSaved_fields cfg s p q
  unfold vectorSaved
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem usageCached_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (usageCached cfg s p q).funcs=s.funcs ∧(usageCached cfg s p q).modules=s.modules ∧(usageCached cfg s p q).tables=s.tables:=by
  have h:=vectorSaved_fields cfg s p q
  unfold usageCached
  simpa only[paid_funcs,paid_modules,paid_tables] using h

theorem output16_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (output16 cfg s p q).funcs=s.funcs ∧(output16 cfg s p q).modules=s.modules ∧(output16 cfg s p q).tables=s.tables:=by
  have h:=usageCached_fields cfg s p q
  unfold output16
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem output8_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (output8 cfg s p q).funcs=s.funcs ∧(output8 cfg s p q).modules=s.modules ∧(output8 cfg s p q).tables=s.tables:=by
  have h:=output16_fields cfg s p q
  unfold output8
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem output24_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (output24 cfg s p q).funcs=s.funcs ∧(output24 cfg s p q).modules=s.modules ∧(output24 cfg s p q).tables=s.tables:=by
  have h:=output8_fields cfg s p q
  unfold output24
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem output32_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (output32 cfg s p q).funcs=s.funcs ∧(output32 cfg s p q).modules=s.modules ∧(output32 cfg s p q).tables=s.tables:=by
  have h:=output24_fields cfg s p q
  unfold output32
  rw[storeI64_funcs,paid_funcs,storeI64_modules,paid_modules,storeI64_tables,paid_tables]
  exact h

theorem output40_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (output40 cfg s p q).funcs=s.funcs ∧(output40 cfg s p q).modules=s.modules ∧(output40 cfg s p q).tables=s.tables:=by
  have h:=output32_fields cfg s p q
  unfold output40
  rw[storeI32_funcs,paid_funcs,storeI32_modules,paid_modules,storeI32_tables,paid_tables]
  exact h

theorem tagged_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagged cfg s p q).funcs=s.funcs ∧(tagged cfg s p q).modules=s.modules ∧(tagged cfg s p q).tables=s.tables:=by
  have h:=output40_fields cfg s p q
  unfold tagged
  rw[storeI32_funcs,paid_funcs,storeI32_modules,paid_modules,storeI32_tables,paid_tables]
  exact h

theorem branched_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (branched cfg s p q).funcs=s.funcs ∧(branched cfg s p q).modules=s.modules ∧(branched cfg s p q).tables=s.tables:=by
  have h:=tagged_fields cfg s p q
  unfold branched
  rw[charged_funcs,charged_modules,charged_tables]
  exact h

theorem after_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (after cfg s p q).funcs=s.funcs ∧(after cfg s p q).modules=s.modules ∧(after cfg s p q).tables=s.tables:=by
  have h:=branched_fields cfg s p q
  unfold after
  rw[global_funcs,paid_funcs,global_modules,paid_modules,global_tables,paid_tables]
  exact h
end WNear.Proofs.StateDecodeBorsh
