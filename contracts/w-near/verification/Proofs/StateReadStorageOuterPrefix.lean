import Proofs.StateReadStorageOuterSetupWP
import Proofs.StateReadStorageOuterStorageCall
import Proofs.StateReadStorageOuterGuard

/-! Original548 reserve, four block entries, real storage read, and status-one selection. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode guarded stored

def outerFrame (frame : CallFrame) (p : Layout) (height : Nat) (code : Expr) :=
  emptyBlockFrame (guardedFrame frame p) height (WNear.Binary.StateReadStorageOuter.restore++code)

theorem wp_prefix (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (key : List UInt8) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p extra) (ha : p.allocator=1074896)
    (h1 : frame.locals[1]?=some (.i32 p.keyPtr)) (h2 : frame.locals[2]?=some (.i32 p.keyLen))
    (hs : 5≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hv : p.global548.value=.i32 p.sp548)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hd : callers.length+4<limits.maxCallDepth)
    (hc : s.host.gas.Credits (283*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest))
    (hnext : WP cfg fuel (.next (atCode (guarded cfg s p ctx key) limits base.toArray
      (outerFrame frame p base.toArray.size code) callers WNear.Binary.StateReadStorageOuter.present)) rest post) :
    WP cfg (fuel+195) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateReadStorageOuter.body++code)))
      (283*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest) post := by
  let op := cfg.regularOpCost
  let height := base.toArray.size
  let rf := reservedFrame frame p
  let outer := emptyBlockFrame rf height (WNear.Binary.StateReadStorageOuter.restore++code)
  let miss := emptyBlockFrame outer height WNear.Binary.StateReadStorageOuter.present
  let panic := emptyBlockFrame miss height WNear.Binary.StateReadStorageOuter.missing
  let inner := emptyBlockFrame panic height WNear.Binary.StateReadStorageOuter.panic
  let skipped : List Label := [{arity:=0,height,rest:=WNear.Binary.StateReadStorageOuter.panic,loop:=none},
    {arity:=0,height,rest:=WNear.Binary.StateReadStorageOuter.missing,loop:=none}]
  have sf : 5≤outer.locals.size := by simpa only [outer,emptyBlockFrame,rf,reservedFrame,Array.size_set!] using hs
  have r3 : inner.locals[3]?=some (.i32 (scratch p)) := by
    simp [inner,panic,miss,outer,emptyBlockFrame,rf,reservedFrame,show 3<frame.locals.size by omega]
  have gn : WP cfg fuel (.next (atCode (StorePairCaller.paid (stored cfg s p ctx key) op 7) limits base.toArray (statusFrame outer) callers
      WNear.Binary.StateReadStorageOuter.present)) rest post := by
    simpa only [guarded,outerFrame,guardedFrame,outer,rf,emptyBlockFrame,statusFrame,op] using hnext
  have gc := stored_credits cfg s p hn ctx raw storage key (7*op+rest)
    hcode.register.prefixCode.memoryIndex hm hr (hc.mono (by dsimp [op];omega))
  have guard := wp_status_one cfg fuel rest (stored cfg s p ctx key) limits base.toArray outer callers skipped WNear.Binary.StateReadStorageOuter.present post sf rfl gc gn
  have gs : WP cfg (fuel+7) (.next (atCode (stored cfg s p ctx key) limits (base.toArray.push (.i64 1)) inner callers
      WNear.Binary.StateReadStorageOuter.statusGuard)) (7*op+rest) post := by
    simpa only [inner,panic,miss,skipped,emptyBlockFrame,labelPrefixFrame,op,height,List.cons_append,List.nil_append] using guard
  have ic : Code s inner.inst p extra := by simpa only [inner,panic,miss,outer,rf,emptyBlockFrame,reservedFrame] using hcode
  have call := wp_storage_call cfg extra (fuel+7) (7*op+rest) s limits base inner callers WNear.Binary.StateReadStorageOuter.statusGuard
    p ctx raw storage key post hn ic ha hm hg r3 hr hd (hc.mono (by dsimp [op];omega)) gs
  have cn : WP cfg ((fuel+7)+173) (.next (atCode (setupStore s op p) limits base.toArray inner callers
      WNear.Binary.StateReadStorageOuter.lookup)) (265*op+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+(7*op+rest)) post := by
    simpa only [WNear.Binary.StateReadStorageOuter.lookup,op,List.append_assoc,List.cons_append,List.nil_append] using call
  have cc : (setupStore s op p).host.gas.Credits (265*op+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+(7*op+rest)) := by
    simpa only [setupStore,highStore,storeI32_host,reserved,setGlobal,StorePairCaller.paid,chargedStore] using
      StorePairCaller.paid_credits s op 11 _ (hc.mono (by dsimp [op];omega))
  have b1 := wp_block_empty cfg ((fuel+7)+173) _ (setupStore s op p) limits base.toArray panic callers
    WNear.Binary.StateReadStorageOuter.lookup WNear.Binary.StateReadStorageOuter.panic post cc cn
  have b2 := wp_block_empty cfg (((fuel+7)+173)+1) _ (setupStore s op p) limits base.toArray miss callers
    ([.block .empty WNear.Binary.StateReadStorageOuter.lookup]++WNear.Binary.StateReadStorageOuter.panic)
    WNear.Binary.StateReadStorageOuter.missing post cc b1
  have b3 := wp_block_empty cfg ((((fuel+7)+173)+1)+1) _ (setupStore s op p) limits base.toArray outer callers
    ([.block .empty ([.block .empty WNear.Binary.StateReadStorageOuter.lookup]++WNear.Binary.StateReadStorageOuter.panic)]++WNear.Binary.StateReadStorageOuter.missing)
    WNear.Binary.StateReadStorageOuter.present post cc b2
  have b4 := wp_block_empty cfg (((((fuel+7)+173)+1)+1)+1) _ (setupStore s op p) limits base.toArray rf callers
    ([.block .empty ([.block .empty ([.block .empty WNear.Binary.StateReadStorageOuter.lookup]++WNear.Binary.StateReadStorageOuter.panic)]++WNear.Binary.StateReadStorageOuter.missing)]++WNear.Binary.StateReadStorageOuter.present)
    (WNear.Binary.StateReadStorageOuter.restore++code) post cc b3
  have bounds : (scratch p).toNat+16≤p.memory.byteSize := by
    rw [(stack_numbers p hn).1];have := hn.spLower;have := hn.spBound;omega
  have setup := wp_setup cfg ((((((fuel+7)+173)+1)+1)+1)+1) _ s limits base frame callers
    (.block .empty ([.block .empty ([.block .empty ([.block .empty WNear.Binary.StateReadStorageOuter.lookup]++WNear.Binary.StateReadStorageOuter.panic)]++WNear.Binary.StateReadStorageOuter.missing)]++WNear.Binary.StateReadStorageOuter.present)::(WNear.Binary.StateReadStorageOuter.restore++code))
    p post h1 h2 (by omega) hcode.register.prefixCode.module hcode.register.prefixCode.memoryIndex hm
    hcode.register.prefixCode.globalIndex hg hv hn.register.allocation.wf bounds (hc.mono (by dsimp [op];omega)) b4
  have ce : 11*cfg.regularOpCost+(265*op+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+(7*op+rest))=
      283*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest := by dsimp [op];omega
  rw [ce] at setup
  simpa only [WNear.Binary.StateReadStorageOuter.body,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using setup
end WNear.Proofs.StateReadStorageOuter
