import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodePrefixWrapperCallResult
import Proofs.StateDecodeScalarResult

/-! Functional host preservation of actual425: only gas and gasProfile are masked. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_global(seed:NearState)(s:Store NearState)(i:Nat)(v:Value):view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_store32(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_store64(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):view seed (storeI64 s i a m v).host=view seed s.host:=rfl
private theorem view_wrapper(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:StateDecodePrefixWrapper.Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (StateDecodePrefixWrapper.callAfter cfg s p q).host=view seed s.host:=by
  have h:=congrArg (view seed) (StateDecodePrefixWrapper.callAfter_functional_host cfg s p q)
  exact h
private theorem view_scalar(seed:NearState)(wide:Bool)(cfg:WasmConfig)(s:Store NearState)(p:StateDecodeScalar.Layout):
    view seed (StateDecodeScalar.callAfter wide cfg s p).host=view seed s.host:=by
  have h:=congrArg (view seed) (StateDecodeScalar.callAfter_functional_host wide cfg s p)
  exact h
attribute [local irreducible] reserved prefixArguments prefixDecoded prefixCached prefixGuarded prefixHighSaved prefixSaved wideArguments wideDecoded wideFirstSaved wideSecondSaved wideSaved wideGuarded wideCached narrowArguments narrowDecoded narrowHighSaved narrowSaved narrowGuarded vectorHighSaved vectorSaved usageCached output16 output8 output24 output32 output40 tagged branched after

theorem after_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(after cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  change view s.host (after cfg s p q).host=s.host
  rw[after,view_global,view_paid]
  rw[branched,view_charge]
  rw[tagged,view_store32,view_paid]
  rw[output40,view_store32,view_paid]
  rw[output32,view_store64,view_paid]
  rw[output24,view_store64,view_paid]
  rw[output8,view_store64,view_paid]
  rw[output16,view_store64,view_paid]
  rw[usageCached,view_paid]
  rw[vectorSaved,view_store64,view_paid]
  rw[vectorHighSaved,view_store32,view_paid]
  rw[narrowGuarded,view_paid]
  rw[narrowSaved,view_store64,view_paid]
  rw[narrowHighSaved,view_store32,view_paid]
  rw[narrowDecoded,view_scalar]
  rw[narrowArguments,view_paid]
  rw[wideCached,view_paid]
  rw[wideGuarded,view_paid]
  rw[wideSaved,view_store64,view_paid]
  rw[wideSecondSaved,view_store32,view_paid]
  rw[wideFirstSaved,view_store64,view_paid]
  rw[wideDecoded,view_scalar]
  rw[wideArguments,view_paid]
  rw[prefixSaved,view_store64,view_paid]
  rw[prefixHighSaved,view_store32,view_paid]
  rw[prefixGuarded,view_paid]
  rw[prefixCached,view_paid]
  rw[prefixDecoded,view_wrapper]
  rw[prefixArguments,view_paid]
  rw[reserved,view_global,view_paid]
  rfl
end WNear.Proofs.StateDecodeBorsh
