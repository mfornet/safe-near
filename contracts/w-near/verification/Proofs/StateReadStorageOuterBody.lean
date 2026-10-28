import Proofs.StateReadStorageOuterPrefix
import Proofs.StateReadStorageOuterRegisterCall
import Proofs.StateReadStorageOuterTail
import Proofs.StateReadStorageOuterRegisteredFrame
import Proofs.StateReadStorageOuterRegisterMemory
import Proofs.StateReadStorageOuterResultReady

/-! Complete actual548 selected canonical-hit, positive-value execution. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode guarded registered after registeredMemory actualRegister fee bodyCost bodySteps

theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (key : List UInt8) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p extra) (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.out548)) (h1 : frame.locals[1]?=some (.i32 p.keyPtr))
    (h2 : frame.locals[2]?=some (.i32 p.keyLen)) (hs : 5≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hv : p.global548.value=.i32 p.sp548)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hd : callers.length+12<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg s p ctx key+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p ctx key) limits base.toArray (guardedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateReadStorageOuter.body++code)))
      (bodyCost p*cfg.regularOpCost+fee cfg s p ctx key+rest) post := by
  let op := cfg.regularOpCost
  let q := actualRegister p
  let gf := guardedFrame frame p
  let outer := outerFrame frame p base.toArray.size code
  let tailCode := WNear.Binary.StateReadStorageOuter.optionArguments++[.call 498]
  have g0 : gf.locals[0]?=some (.i32 p.out548) := by simp [gf,guardedFrame,statusFrame,reservedFrame,h0]
  have g3 : gf.locals[3]?=some (.i32 (scratch p)) := by
    simp [gf,guardedFrame,statusFrame,reservedFrame,show 3<frame.locals.size by omega]
  have fields := registered_fields cfg s p ctx key
  have moduleR : (registered cfg s p ctx key).modules[gf.inst]?=some p.mi := by
    rw [fields.2.1]
    simpa only [gf,guardedFrame,statusFrame,reservedFrame,StateReadRegisterOuter.actualLength,StateReadRegisterOuter.lengthOn] using hcode.register.prefixCode.module
  have memR := registered_memory cfg s limits frame.inst base.length callers p ctx key extra hn ha hcode hm hg (by omega)
  have globalR := registered_global cfg s p ctx key hn ha hg
  have fn : (registered cfg s p ctx key).funcs[p.address498]?=some (.wasm WNear.Binary.StateRead.resultSignature gf.inst WNear.Binary.StateRead.resultFunction) := by
    rw [fields.1]
    simpa only [gf,guardedFrame,statusFrame,reservedFrame] using hcode.function498
  have bounds := result_bounds p hn ha
  have cr := registered_credits cfg s p hn ctx raw storage key (38*op+rest)
    hcode.register.prefixCode.memoryIndex hm hr (hc.mono (by simp only [bodyCost,Nat.add_mul,op];omega))
  have tn : WP cfg fuel (.next (atCode (tailAfter (registered cfg s p ctx key) op p.memoryIndex p.globalIndex
      (registeredMemory p) p.out548 (scratch p)) limits base.toArray gf callers code)) rest post := by
    simpa only [tailAfter,after,converted,optionArguments,scratch,UInt32.sub_add_cancel,op,gf] using hnext
  have tail := wp_tail cfg fuel rest (registered cfg s p ctx key) limits base gf callers code p.out548 (scratch p) p.mi p.memoryIndex p.globalIndex p.address498
    (registeredMemory p) p.global523 post g0 g3 moduleR hcode.register.prefixCode.memoryIndex memR hcode.register.prefixCode.globalIndex globalR
    hcode.index498 fn bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.1
    (registeredMemory_present p hn ha) (by omega) cr tn
  have tailN : WP cfg (fuel+30) (.next (atCode (registered cfg s p ctx key) limits base.toArray outer callers tailCode)) (38*op+rest) post := by
    simpa only [outer,outerFrame,gf,tailCode,op] using tail
  have codeO : Code s outer.inst p extra := by simpa only [outer,outerFrame,guardedFrame,statusFrame,reservedFrame,emptyBlockFrame] using hcode
  have localO : outer.locals[3]?=some (.i32 (scratch p)) := g3
  have reg := wp_register_call cfg extra (fuel+30) (38*op+rest) s limits base outer callers tailCode p ctx raw storage key post hn codeO ha hm hg localO hr hd
    (hc.mono (by simp only [bodyCost,Nat.add_mul,op];omega)) tailN
  let rb := (StateReadRegisterOuter.bodyCost q+53)*op+StateReadRegisterOuter.fee cfg s q+rest
  have ce : (StateReadRegisterOuter.bodyCost q+15)*cfg.regularOpCost+StateReadRegisterOuter.fee cfg s q+(38*op+rest)=rb := by
    simp only [rb,Nat.add_mul,op];omega
  have regN : WP cfg ((fuel+30)+StateReadRegisterOuter.bodySteps q+6) (.next (atCode (guarded cfg s p ctx key) limits base.toArray outer callers
      WNear.Binary.StateReadStorageOuter.present)) rb post := by
    simpa only [q,ce,WNear.Binary.StateReadStorageOuter.present,tailCode,List.append_assoc,List.cons_append,List.nil_append] using reg
  have pref := wp_prefix cfg extra ((fuel+30)+StateReadRegisterOuter.bodySteps q+6) rb s limits base frame callers code p ctx raw storage key post hn hcode ha h1 h2 hs hm hg hv hr (by omega)
    (hc.mono (by simp only [bodyCost,fee,rb,q,Nat.add_mul,op];omega)) regN
  have cp : 283*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rb=
      bodyCost p*cfg.regularOpCost+fee cfg s p ctx key+rest := by simp only [bodyCost,fee,rb,q,Nat.add_mul,op];omega
  rw [cp] at pref
  have fs : (fuel+30+StateReadRegisterOuter.bodySteps q+6)+195=fuel+bodySteps p := by simp only [bodySteps,q];omega
  rw [fs] at pref
  exact pref
end WNear.Proofs.StateReadStorageOuter
