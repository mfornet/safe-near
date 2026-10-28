import Proofs.StateReadOuterStorageCredits
import Proofs.StateReadOuterDomain
import Proofs.StateDecodeBorshReadResult
import Proofs.UnwrapStateCopyEffects

/-! All219 callees restore the reserved SP array. The final actual global.set
restores the original complete global array; no future global lookup is assumed. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem charge_globals(s:Store NearState)(n:Nat):(chargedStore s n).globals=s.globals:=rfl
private theorem word_globals(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl
private theorem wide_globals(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):(storeI64 s i a m v).globals=s.globals:=rfl
private theorem copies_globals(s:Store NearState)(op i:Nat)(m:Memory)(r:UInt32):
    (copiedStorage s op i m r).globals=s.globals:=by
  rw[copiedStorage,storageLowStore,wide_globals,paid_globals,storageHighStore,word_globals,paid_globals]
private theorem pack_globals(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory):
    (PackWordsCall.callAfter s op i out src m).globals=s.globals:=
  (PackWordsCall.callAfter_frame s op i out src m).2.2.1
private theorem copy_globals(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory)(n:Nat):
    (UnwrapStateCopyEntry.callAfter s op i out src m n).globals=s.globals:=by
  have h:=congrArg (fun t:Store NearState=>t.globals) (UnwrapStateCopyEffects.callAfter_resources s op i out src m n)
  exact h
private theorem release_globals(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    (VectorDropInsert.callAfter s op q).globals=s.globals:=
  (VectorDropInsert.callAfter_fields s op q).2.2.1
attribute [local irreducible] reserved storageArguments stored presenceChecked storageCopied packArguments packed decodeArguments decoded decodeGuarded copyArguments outputCopied outputDropped releaseArguments released restored after actualDecoder actualAllocation actualRelease

 theorem storageArguments_globals(s:Store NearState)(op:Nat)(p:Layout):
    (storageArguments s op p).globals=(reserved s op p).globals:=by
  rw[storageArguments,paid_globals]

 theorem stored_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (stored cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  have global:=storageArguments_global s cfg.regularOpCost p hn hg
  have frame:=StateReadStorageOuter.callAfter_globals cfg (storageArguments s cfg.regularOpCost p) p.toStorage ctx key
    hn.storage hn.allocator global (storage_global_value p hn)
  unfold stored
  exact frame.trans (storageArguments_globals s cfg.regularOpCost p)

 theorem presenceChecked_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (presenceChecked cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[presenceChecked,paid_globals]
  exact stored_globals cfg s p ctx key hn hg

 theorem storageCopied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (storageCopied cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[storageCopied,copies_globals]
  exact presenceChecked_globals cfg s p ctx key hn hg

 theorem packArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (packArguments cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[packArguments,paid_globals]
  exact storageCopied_globals cfg s p ctx key hn hg

 theorem packed_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (packed cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[packed,pack_globals]
  exact packArguments_globals cfg s p ctx key hn hg

 theorem decodeArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (decodeArguments cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[decodeArguments,paid_globals]
  exact packed_globals cfg s p ctx key hn hg

 theorem decodeArguments_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (decodeArguments cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[decodeArguments_globals cfg s p ctx key hn hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem decoded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)
    (hg:s.globals[p.globalIndex]?=some p.global219):
    (decoded cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  have index:(actualDecoder p).globalIndex=p.globalIndex:=by simp only[actualDecoder];exact hn.decoderGlobalIndex
  have value:(actualDecoder p).global161=p.global548:=by simp only[actualDecoder];exact hn.decoderGlobal
  have sp:(actualDecoder p).sp161=p.sp548:=by simp only[actualDecoder];exact hn.decoderSP.trans hn.storageSP.symm
  have global:(decodeArguments cfg s p ctx key).globals[(actualDecoder p).globalIndex]?=some (actualDecoder p).global161:=by
    rw[index,value]
    exact decodeArguments_global cfg s p ctx key hn hg
  have hv:(actualDecoder p).global161.value=.i32 (actualDecoder p).sp161:=by
    rw[value,sp]
    exact storage_global_value p hn
  have frame:=StateDecodeBorshRead.callAfter_globals cfg (decodeArguments cfg s p ctx key) (actualDecoder p) (actualAllocation p)
    (decoder_native p hn state hw hb) (decoder_domain p hn state hw hb) global hv
  unfold decoded
  exact frame.trans (decodeArguments_globals cfg s p ctx key hn hg)

 theorem decodeGuarded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (decodeGuarded cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[decodeGuarded,paid_globals]
  exact decoded_globals cfg s p ctx key hn state hw hb hg

 theorem copyArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (copyArguments cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[copyArguments,paid_globals]
  exact decodeGuarded_globals cfg s p ctx key hn state hw hb hg

 theorem outputCopied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (outputCopied cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[outputCopied,copy_globals]
  exact copyArguments_globals cfg s p ctx key hn state hw hb hg

 theorem outputDropped_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (outputDropped cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[outputDropped,paid_globals]
  exact outputCopied_globals cfg s p ctx key hn state hw hb hg

 theorem releaseArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (releaseArguments cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[releaseArguments,paid_globals]
  exact outputDropped_globals cfg s p ctx key hn state hw hb hg

 theorem released_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (released cfg s p ctx key).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[released,release_globals]
  exact releaseArguments_globals cfg s p ctx key hn state hw hb hg

 theorem stored_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (stored cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[stored_globals cfg s p ctx key hn hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem presenceChecked_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (presenceChecked cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[presenceChecked_globals cfg s p ctx key hn hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem storageCopied_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (storageCopied cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[storageCopied_globals cfg s p ctx key hn hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem packArguments_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (packArguments cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[packArguments_globals cfg s p ctx key hn hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem packed_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global219):
    (packed cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[packed_globals cfg s p ctx key hn hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem decodeGuarded_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (decodeGuarded cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[decodeGuarded_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem copyArguments_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (copyArguments cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[copyArguments_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem outputCopied_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (outputCopied cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[outputCopied_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem outputDropped_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (outputDropped cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[outputDropped_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem releaseArguments_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (releaseArguments cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[releaseArguments_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem released_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (released cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[released_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

 theorem decoded_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hg:s.globals[p.globalIndex]?=some p.global219):
    (decoded cfg s p ctx key).globals[p.globalIndex]?=some p.global548:=by
  rw[decoded_globals cfg s p ctx key hn state hw hb hg]
  exact reserved_global s cfg.regularOpCost p hn hg

private theorem global_congr(s t:Store NearState)(i:Nat)(v:Value)(h:s.globals=t.globals):
    (setGlobal s i v).globals=(setGlobal t i v).globals:=by simp only[setGlobal,h]
private theorem reserved_as_global(s:Store NearState)(op:Nat)(p:Layout):
    (reserved s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals:=by
  rw[reserved];simp only[setGlobal,paid_globals]
 theorem restored_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)
    (hg:s.globals[p.globalIndex]?=some p.global219)(hv:p.global219.value=.i32 p.sp219):
    (restored cfg s p ctx key).globals=s.globals:=by
  have before:(paid (released cfg s p ctx key) cfg.regularOpCost 4).globals=
      (setGlobal s p.globalIndex (.i32 (scratch p))).globals:=by
    rw[paid_globals,released_globals cfg s p ctx key hn state hw hb hg]
    exact reserved_as_global s cfg.regularOpCost p
  have first:=global_congr _ _ p.globalIndex (.i32 p.sp219) before
  have last:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global219 hg
  rw[hv] at last
  unfold restored
  exact first.trans last
 theorem after_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)
    (hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)
    (hg:s.globals[p.globalIndex]?=some p.global219)(hv:p.global219.value=.i32 p.sp219):
    (after cfg s p ctx key).globals=s.globals:=by
  rw[after,charge_globals]
  exact restored_globals cfg s p ctx key hn state hw hb hg hv
end WNear.Proofs.StateReadOuter
