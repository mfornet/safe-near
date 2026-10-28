import Proofs.StateReadStorageOuterReady
import Proofs.StateReadStorageOuterHostReady
import Proofs.StateReadStorageOuterArguments
import Proofs.StateReadStorageOuterCredits

/-! Actual459 call plus its four guest argument instructions inside548's blocks. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode stored storageArguments setupStore

theorem wp_storage_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (key : List UInt8) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p extra) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hd : callers.length+4<limits.maxCallDepth)
    (hc : s.host.gas.Credits (276*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest))
    (hnext : WP cfg fuel (.next (atCode (stored cfg s p ctx key) limits
      (base.toArray.push (.i64 1)) frame callers code)) rest post) :
    WP cfg (fuel+173) (.next (atCode (setupStore s cfg.regularOpCost p) limits base.toArray frame callers
      (WNear.Binary.StateReadStorageOuter.storageArguments++(.call 459::code))))
      (265*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest) post := by
  let op := cfg.regularOpCost
  let args := storageArguments s op p
  let q := storageLayout p
  let leaf := StateDispatchStorage.leafFrame frame.inst base.length q
  let saved := {frame with code}
  have ready := Code.storage_ready cfg s limits leaf (saved::callers) p extra hn ha hcode hm hg rfl rfl (by simp [leaf,StateDispatchStorage.leafFrame])
    (by simp only [List.length_cons];omega)
  have fields := storageArguments_fields s op p
  have fn : args.funcs[p.address459]?=some (.wasm WNear.Binary.StateDispatchStorage.signature frame.inst WNear.Binary.StateDispatchStorage.function) := by
    rw [fields.1];exact hcode.function459
  have cp := storageArguments_credits s op (261*op+StateDispatchStorage.fee s q ctx key p.bytes+rest) p
    (hc.mono (by dsimp [op,q];omega))
  have feeEq : StateDispatchStorage.fee args q ctx key p.bytes=StateDispatchStorage.fee s q ctx key p.bytes :=
    StateDispatchStorage.cost_of_host_mask s.host args.host _ ctx.trie _ _ _ key p.bytes (storageArguments_functional_host s op p)
  have oneArray : (base++[Value.i64 1]).toArray=base.toArray.push (.i64 1) := by apply Array.toList_inj.mp;simp
  have cn : WP cfg fuel (.next (atCode (StateDispatchStorage.callAfter cfg args q ctx key p.bytes) limits
      (base++[Value.i64 1]).toArray frame callers code)) rest post := by
    simpa only [stored,args,q,op,oneArray] using hnext
  have cc : args.host.gas.Credits (261*cfg.regularOpCost+StateDispatchStorage.fee args q ctx key p.bytes+rest) := by
    rw [feeEq];exact cp
  have call := StateDispatchStorage.wp_call cfg extra fuel rest args limits base frame callers code q p.address459 ctx raw storage key p.bytes post
    ready hcode.index459 fn (storage_host_ready cfg s p hn ctx raw storage key hr) cc cn
  rw [feeEq] at call
  have arr : (base++[Value.i32 1055020,.i32 (scratch p+8)]).toArray=
      (base.toArray.push (.i32 1055020)).push (.i32 (scratch p+8)) := by apply Array.toList_inj.mp;simp
  have an : WP cfg (fuel+169) (.next (atCode (paid (setupStore s op p) op 4) limits
      ((base.toArray.push (.i32 1055020)).push (.i32 (scratch p+8))) frame callers (.call 459::code)))
      (261*op+StateDispatchStorage.fee s q ctx key p.bytes+rest) post := by
    simpa only [q,storageLayout,storageArguments,arr,args,op] using call
  have cs : (setupStore s op p).host.gas.Credits (4*op+(261*op+StateDispatchStorage.fee s q ctx key p.bytes+rest)) := by
    simpa only [setupStore,highStore,storeI32_host,reserved,setGlobal,paid,chargedStore] using
      paid_credits s op 11 (4*op+(261*op+StateDispatchStorage.fee s q ctx key p.bytes+rest)) (hc.mono (by dsimp [op,q];omega))
  have arguments := wp_storage_arguments cfg (fuel+169) (261*op+StateDispatchStorage.fee s q ctx key p.bytes+rest)
    (setupStore s op p) limits base.toArray frame callers (.call 459::code) (scratch p) post h3 cs an
  have ce : 4*cfg.regularOpCost+(261*op+StateDispatchStorage.fee s q ctx key p.bytes+rest)=
      265*cfg.regularOpCost+StateDispatchStorage.fee s q ctx key p.bytes+rest := by dsimp [op,q];omega
  rw [ce] at arguments
  simpa only [q,op,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateReadStorageOuter
