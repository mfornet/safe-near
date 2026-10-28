import Proofs.StateReadStorageOuterRegisterReady
import Proofs.StateReadStorageOuterCredits
import Proofs.StateReadStorageOuterArguments

/-! Actual523 call from the canonical storage-read result, with its real arguments. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode actualRegister guarded registerArguments registered fee

theorem wp_register_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (key : List UInt8) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p extra) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hd : callers.length+12<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((StateReadRegisterOuter.bodyCost (actualRegister p)+298)*cfg.regularOpCost+fee cfg s p ctx key+rest))
    (hnext : WP cfg fuel (.next (atCode (registered cfg s p ctx key) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+StateReadRegisterOuter.bodySteps (actualRegister p)+6) (.next (atCode (guarded cfg s p ctx key) limits base.toArray frame callers
      (WNear.Binary.StateReadStorageOuter.registerArguments++(.call 523::code))))
      ((StateReadRegisterOuter.bodyCost (actualRegister p)+15)*cfg.regularOpCost+
        StateReadRegisterOuter.fee cfg s (actualRegister p)+rest) post := by
  let op := cfg.regularOpCost
  let q := actualRegister p
  let args := registerArguments cfg s p ctx key
  have resources := register_call_resources cfg extra s frame.inst p ctx key hn ha hcode hm hg
  have ca := registerArguments_credits cfg s p hn ctx raw storage key
    ((StateReadRegisterOuter.bodyCost q+11)*op+StateReadRegisterOuter.fee cfg s q+rest)
    hcode.register.prefixCode.memoryIndex hm hr (hc.mono (by simp only [q,fee,Nat.add_mul,op];omega))
  have feeEq : StateReadRegisterOuter.fee cfg args q=StateReadRegisterOuter.fee cfg s q := by
    simp only [args,StateReadRegisterOuter.fee,RegisterRead.readCost,registerArguments_costs]
  have cb : args.host.gas.Credits ((StateReadRegisterOuter.bodyCost q+11)*cfg.regularOpCost+StateReadRegisterOuter.fee cfg args q+rest) := by
    rw [feeEq];exact ca
  have cn : WP cfg fuel (.next (atCode (StateReadRegisterOuter.callAfter cfg args q) limits base.toArray frame callers code)) rest post := by
    simpa only [registered,args] using hnext
  have haQ : q.allocator=1074896 := by simpa only [q,actualRegister,registerTemplate] using ha
  have call := StateReadRegisterOuter.wp_call cfg extra fuel rest args limits base frame callers code q p.address523 post
    (register_native p hn ha) resources.1 haQ resources.2.1 resources.2.2.1 resources.2.2.2.1 resources.2.2.2.2.1
    resources.2.2.2.2.2.1 resources.2.2.2.2.2.2 hd cb cn
  rw [feeEq] at call
  have qo : q.out523=scratch p+16 := by simpa only [q,actualRegister,registerTemplate] using hn.registerOut
  have qr : q.register=0 := by simpa only [q,actualRegister,registerTemplate] using hn.registerId
  have operands : (base++[Value.i32 q.out523,.i64 q.register]).toArray=
      (base.toArray.push (.i32 (scratch p+16))).push (.i64 0) := by
    rw [qo,qr];apply Array.toList_inj.mp;simp
  have next : WP cfg (fuel+StateReadRegisterOuter.bodySteps q+2) (.next (atCode (paid (guarded cfg s p ctx key) op 4) limits
      ((base.toArray.push (.i32 (scratch p+16))).push (.i64 0)) frame callers (.call 523::code)))
      ((StateReadRegisterOuter.bodyCost q+11)*op+StateReadRegisterOuter.fee cfg s q+rest) post := by
    rw [operands] at call
    simpa only [args,registerArguments,op] using call
  have cg := guarded_credits cfg s p hn ctx raw storage key
    (4*op+((StateReadRegisterOuter.bodyCost q+11)*op+StateReadRegisterOuter.fee cfg s q+rest))
    hcode.register.prefixCode.memoryIndex hm hr (hc.mono (by simp only [fee,q,Nat.add_mul,op];omega))
  have arguments := wp_register_arguments cfg (fuel+StateReadRegisterOuter.bodySteps q+2)
    ((StateReadRegisterOuter.bodyCost q+11)*op+StateReadRegisterOuter.fee cfg s q+rest)
    (guarded cfg s p ctx key) limits base.toArray frame callers (.call 523::code) (scratch p) post h3 cg next
  have ce : 4*cfg.regularOpCost+((StateReadRegisterOuter.bodyCost q+11)*op+StateReadRegisterOuter.fee cfg s q+rest)=
      (StateReadRegisterOuter.bodyCost q+15)*cfg.regularOpCost+StateReadRegisterOuter.fee cfg s q+rest := by simp only [Nat.add_mul,op];omega
  rw [ce] at arguments
  simpa only [q,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateReadStorageOuter
