import Proofs.StateReadStorageOuterBody
import Proofs.StateReadStorageOuterEntry
import NearVM.MeteredWasmCall

/-! Actual typed548 selected present-storage path and its normal void return. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after actualRegister fee bodyCost bodySteps

/-- Original canonical hit data suffice for the deployed f548 call, including
all nested storage dispatch, allocation, register copying and result conversion. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (key : List UInt8) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p extra) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hv : p.global548.value=.i32 p.sp548)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hi : p.mi.funcAddrs[548]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateReadStorageOuter.signature frame.inst WNear.Binary.StateReadStorageOuter.function))
    (hd : callers.length+13<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg s p ctx key+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p ctx key) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps p+2) (.next (atCode s limits
      (base++[Value.i32 p.out548,.i32 p.keyPtr,.i32 p.keyLen]).toArray frame callers (.call 548::code)))
      ((bodyCost p+12)*cfg.regularOpCost+fee cfg s p ctx key+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ra : StorageReadCalls.Ready ⟨p.memory,active.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes :=
    (hr.charge _ op ctx raw storage _ _ _ key p.bytes).charge _ (11*op) ctx raw storage _ _ _ key p.bytes
  have ca : active.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg active p ctx key+rest) := by
    rw [entered_fee]
    exact entered_credits s op _ (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter_credits cfg s p hn ctx raw storage key rest hcode.register.prefixCode.memoryIndex hm hr hc
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s p ctx key) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s p ctx key) limits base []
    (guardedFrame leaf p) saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel+1) (.next (atCode (after cfg active p ctx key) limits base.toArray
      (guardedFrame leaf p) (saved::callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using left
  have cd : Code active leaf.inst p extra := hcode.transport s active frame.inst p extra rfl rfl rfl
  have body := wp_body cfg extra (fuel+1) rest active limits base leaf (saved::callers) [] p ctx raw storage key post hn cd ha
    rfl rfl rfl (by simp [leaf,leafFrame]) hm hg hv ra (by simp only [List.length_cons];omega) ca bn
  have module : s.modules[frame.inst]?=some p.mi := by
    simpa only [StateReadRegisterOuter.actualLength,StateReadRegisterOuter.lengthOn] using hcode.register.prefixCode.module
  have cr := wp_call_wasm cfg ((fuel+1)+bodySteps p) (bodyCost p*op+fee cfg s p ctx key+rest) s limits base
    [.i32 p.out548,.i32 p.keyPtr,.i32 p.keyLen] frame callers code 548 address p.mi WNear.Binary.StateReadStorageOuter.signature
    frame.inst WNear.Binary.StateReadStorageOuter.function post module hi hf rfl (by omega)
  rw [WNear.Binary.StateReadStorageOuter.activation] at cr
  have arrays : #[Value.i32 p.out548,Value.i32 p.keyPtr,Value.i32 p.keyLen]++#[Value.i32 0,Value.i64 0]=
      #[Value.i32 p.out548,Value.i32 p.keyPtr,Value.i32 p.keyLen,Value.i32 0,Value.i64 0] := by apply Array.toList_inj.mp;simp
  have afee : fee cfg active p ctx key=fee cfg s p ctx key := entered_fee cfg s p ctx key
  rw [afee] at body
  have next : WP cfg ((fuel+1)+bodySteps p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateReadStorageOuter.signature frame.inst WNear.Binary.StateReadStorageOuter.function [.i32 p.out548,.i32 p.keyPtr,.i32 p.keyLen]))
      (bodyCost p*op+fee cfg s p ctx key+rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.StateReadStorageOuter.function,WNear.Binary.StateReadStorageOuter.signature,
      leaf,leafFrame,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,ValType.default,arrays] using body
  have proof := cr (hc.mono (by simp only [Nat.add_mul,op];omega)) next
  have ce : cfg.regularOpCost+(11*cfg.regularOpCost+(bodyCost p*op+fee cfg s p ctx key+rest))=
      (bodyCost p+12)*cfg.regularOpCost+fee cfg s p ctx key+rest := by simp only [Nat.add_mul,op];omega
  have fe : (fuel+1+bodySteps p)+1=fuel+bodySteps p+2 := by omega
  simpa only [ce,fe] using proof
end WNear.Proofs.StateReadStorageOuter
