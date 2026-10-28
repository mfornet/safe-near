import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodeBorshNarrowNative
import Proofs.StateDecodePrefixWrapperCallResult
import Proofs.StateDecodeScalarResult

/-! Actual425 callees restore the complete reserved stack-pointer array. The
final restore reinstates the original global instances, including metadata. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] wideLayout narrowLayout
attribute [local irreducible] reserved prefixArguments prefixDecoded prefixCached prefixGuarded prefixHighSaved prefixSaved wideArguments wideDecoded wideFirstSaved wideSecondSaved wideSaved wideGuarded wideCached narrowArguments narrowDecoded narrowHighSaved narrowSaved narrowGuarded vectorHighSaved vectorSaved usageCached output16 output8 output24 output32 output40 tagged branched after
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_charge(s:Store NearState)(op:Nat):(chargedStore s op).globals=s.globals:=rfl
private theorem globals_word(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):(storeI64 s i a m v).globals=s.globals:=rfl
private theorem globals_dword(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl

theorem reserved_global(s:Store NearState)(op:Nat)(p:Layout)
    (hg:s.globals[p.globalIndex]?=some p.global425):
    (reserved s op p).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  simp only[reserved,setGlobal,globals_paid]
  simp[Array.getElem?_modify,hg]

theorem prefixArguments_globals(s:Store NearState)(op:Nat)(p:Layout):
    (prefixArguments s op p).globals=(reserved s op p).globals:=by unfold prefixArguments;exact globals_paid _ _ _

theorem prefixDecoded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixDecoded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  have g:(prefixArguments s cfg.regularOpCost p).globals[p.globalIndex]?=some p.wrapperGlobal:=by
    rw[prefixArguments_globals,hn.childGlobal]
    exact reserved_global s cfg.regularOpCost p hg
  have v:p.wrapperGlobal.value=.i32 p.wrapperSP:=by rw[hn.childGlobal,hn.childSP]
  unfold prefixDecoded
  exact (StateDecodePrefixWrapper.callAfter_globals cfg _ _ _ hn.prefixNative hd.toAcceptedDomain g v).trans (prefixArguments_globals s cfg.regularOpCost p)

theorem prefixCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[prefixCached,globals_paid]
  exact prefixDecoded_globals cfg s p q hn hd hg

theorem prefixGuarded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixGuarded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[prefixGuarded,globals_paid]
  exact prefixCached_globals cfg s p q hn hd hg

theorem prefixHighSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixHighSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[prefixHighSaved,globals_dword,globals_paid]
  exact prefixGuarded_globals cfg s p q hn hd hg

theorem prefixSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[prefixSaved,globals_word,globals_paid]
  exact prefixHighSaved_globals cfg s p q hn hd hg

theorem wideArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[wideArguments,globals_paid]
  exact prefixSaved_globals cfg s p q hn hd hg

theorem wideDecoded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideDecoded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  have g:(wideArguments cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
    rw[wideArguments_globals cfg s p q hn hd hg]
    exact reserved_global s cfg.regularOpCost p hg
  have gc:(wideArguments cfg s p q).globals[(wideLayout p q).globalIndex]?=some (wideLayout p q).global:=by
    simpa only[wideLayout] using g
  have vc:(wideLayout p q).global.value=.i32 (wideLayout p q).sp:=by simp only[wideLayout]
  have child: (StateDecodeScalar.callAfter true cfg (wideArguments cfg s p q) (wideLayout p q)).globals=(wideArguments cfg s p q).globals:=
    StateDecodeScalar.callAfter_globals true cfg (wideArguments cfg s p q) (wideLayout p q) gc vc
  unfold wideDecoded
  exact child.trans (wideArguments_globals cfg s p q hn hd hg)

theorem wideFirstSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideFirstSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[wideFirstSaved,globals_word,globals_paid]
  exact wideDecoded_globals cfg s p q hn hd hg

theorem wideSecondSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideSecondSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[wideSecondSaved,globals_dword,globals_paid]
  exact wideFirstSaved_globals cfg s p q hn hd hg

theorem wideSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[wideSaved,globals_word,globals_paid]
  exact wideSecondSaved_globals cfg s p q hn hd hg

theorem wideGuarded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideGuarded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[wideGuarded,globals_paid]
  exact wideSaved_globals cfg s p q hn hd hg

theorem wideCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[wideCached,globals_paid]
  exact wideGuarded_globals cfg s p q hn hd hg

theorem narrowArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[narrowArguments,globals_paid]
  exact wideCached_globals cfg s p q hn hd hg

theorem narrowDecoded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowDecoded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  have g:(narrowArguments cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
    rw[narrowArguments_globals cfg s p q hn hd hg]
    exact reserved_global s cfg.regularOpCost p hg
  have gc:(narrowArguments cfg s p q).globals[(narrowLayout p q).globalIndex]?=some (narrowLayout p q).global:=by
    simpa only[narrowLayout] using g
  have vc:(narrowLayout p q).global.value=.i32 (narrowLayout p q).sp:=by simp only[narrowLayout]
  have child: (StateDecodeScalar.callAfter false cfg (narrowArguments cfg s p q) (narrowLayout p q)).globals=(narrowArguments cfg s p q).globals:=
    StateDecodeScalar.callAfter_globals false cfg (narrowArguments cfg s p q) (narrowLayout p q) gc vc
  unfold narrowDecoded
  exact child.trans (narrowArguments_globals cfg s p q hn hd hg)

theorem narrowHighSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowHighSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[narrowHighSaved,globals_dword,globals_paid]
  exact narrowDecoded_globals cfg s p q hn hd hg

theorem narrowSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[narrowSaved,globals_word,globals_paid]
  exact narrowHighSaved_globals cfg s p q hn hd hg

theorem narrowGuarded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowGuarded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[narrowGuarded,globals_paid]
  exact narrowSaved_globals cfg s p q hn hd hg

theorem vectorHighSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (vectorHighSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[vectorHighSaved,globals_dword,globals_paid]
  exact narrowGuarded_globals cfg s p q hn hd hg

theorem vectorSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (vectorSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[vectorSaved,globals_word,globals_paid]
  exact vectorHighSaved_globals cfg s p q hn hd hg

theorem usageCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (usageCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[usageCached,globals_paid]
  exact vectorSaved_globals cfg s p q hn hd hg

theorem output16_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (output16 cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[output16,globals_word,globals_paid]
  exact usageCached_globals cfg s p q hn hd hg

theorem output8_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (output8 cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[output8,globals_word,globals_paid]
  exact output16_globals cfg s p q hn hd hg

theorem output24_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (output24 cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[output24,globals_word,globals_paid]
  exact output8_globals cfg s p q hn hd hg

theorem output32_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (output32 cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[output32,globals_word,globals_paid]
  exact output24_globals cfg s p q hn hd hg

theorem output40_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (output40 cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[output40,globals_dword,globals_paid]
  exact output32_globals cfg s p q hn hd hg

theorem tagged_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (tagged cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[tagged,globals_dword,globals_paid]
  exact output40_globals cfg s p q hn hd hg

theorem branched_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (branched cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[branched,globals_charge]
  exact tagged_globals cfg s p q hn hd hg

theorem after_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425)
    (hv:p.global425.value=.i32 p.sp425):
    (after cfg s p q).globals=s.globals:=by
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global425 hg
  simp only[after,setGlobal,globals_paid,branched_globals cfg s p q hn hd hg,reserved,globals_paid]
  simpa only[setGlobal,hv] using restore

theorem prefixDecoded_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixDecoded cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[prefixDecoded_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem prefixSaved_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (prefixSaved cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[prefixSaved_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem wideDecoded_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideDecoded cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[wideDecoded_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem wideSaved_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (wideSaved cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[wideSaved_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem narrowDecoded_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowDecoded cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[narrowDecoded_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem narrowSaved_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (narrowSaved cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[narrowSaved_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem usageCached_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (usageCached cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[usageCached_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg

theorem branched_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global425):
    (branched cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
  rw[branched_globals cfg s p q hn hd hg]
  exact reserved_global s cfg.regularOpCost p hg
end WNear.Proofs.StateDecodeBorsh
