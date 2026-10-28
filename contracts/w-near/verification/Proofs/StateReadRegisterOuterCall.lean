import Proofs.StateReadRegisterOuterBody
import NearVM.MeteredWasmCall

/-! Typed actual523 entry, complete positive register read, and normal void return. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
attribute [local irreducible] WP atCode after actualVector fee
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.out523,.i64 p.register,.i32 0],inst,arity:=0,height,labels:=[],code:=[]}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after cfg (entered s cfg.regularOpCost) p

theorem entered_fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    fee cfg (entered s cfg.regularOpCost) p=fee cfg s p := by
  simp only [fee,RegisterRead.readCost,entered,chargedStore,chargeHost]

theorem entered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11*op+rest)) : (entered s op).host.gas.Credits rest := by
  have c0 := StorePair.charged_credits s op (10*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10*op) rest c0

theorem callAfter_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost p+11)*cfg.regularOpCost+fee cfg s p+rest)) :
    (callAfter cfg s p).host.gas.Credits rest := by
  have ca := entered_credits s cfg.regularOpCost (bodyCost p*cfg.regularOpCost+fee cfg s p+rest)
    (hc.mono (by simp only [Nat.add_mul];omega))
  unfold callAfter
  exact after_credits cfg (entered s cfg.regularOpCost) p rest (by rw [entered_fee];exact ca)

/-- Real f523 on a present positive register, including actual f524, allocation f687,
actual read-register dispatch f435, sequential result copies and caller restoration. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p extra) (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hv : p.global523.value=.i32 p.sp523) (hr : s.host.registers p.register.toNat=some p.bytes)
    (hi : p.mi.funcAddrs[523]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateReadRegisterOuter.signature frame.inst WNear.Binary.StateReadRegisterOuter.function))
    (hd : callers.length+12<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost p+11)*cfg.regularOpCost+fee cfg s p+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps p+2) (.next (atCode s limits
      (base++[Value.i32 p.out523,.i64 p.register]).toArray frame callers (.call 523::code)))
      ((bodyCost p+11)*cfg.regularOpCost+fee cfg s p+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca : active.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg active p+rest) := by
    rw [entered_fee]
    exact entered_credits s op _ (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter_credits cfg s p rest hc
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s p) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s p) limits base []
    (reservedFrame leaf p) saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel+1) (.next (atCode (after cfg active p) limits base.toArray
      (reservedFrame leaf p) (saved::callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using left
  have cd : Code active leaf.inst p extra := hcode.transport s active frame.inst p extra rfl rfl rfl
  have body := wp_body cfg extra (fuel+1) rest active limits base leaf (saved::callers) [] p post hn cd haRoot
    rfl rfl (by simp [leaf,leafFrame]) hm hg hv hr (by simp only [List.length_cons];omega) ca bn
  have cr := wp_call_wasm cfg ((fuel+1)+bodySteps p) (bodyCost p*op+fee cfg s p+rest) s limits base
    [.i32 p.out523,.i64 p.register] frame callers code 523 address p.mi WNear.Binary.StateReadRegisterOuter.signature
    frame.inst WNear.Binary.StateReadRegisterOuter.function post hcode.prefixCode.module hi hf rfl (by omega)
  rw [WNear.Binary.StateReadRegisterOuter.activation] at cr
  have arrays : #[Value.i32 p.out523,Value.i64 p.register]++#[Value.i32 0]=
      #[Value.i32 p.out523,Value.i64 p.register,Value.i32 0] := by apply Array.toList_inj.mp;simp
  have afee : fee cfg active p=fee cfg s p := entered_fee cfg s p
  rw [afee] at body
  have next : WP cfg ((fuel+1)+bodySteps p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateReadRegisterOuter.signature frame.inst WNear.Binary.StateReadRegisterOuter.function [.i32 p.out523,.i64 p.register]))
      (bodyCost p*op+fee cfg s p+rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.StateReadRegisterOuter.function,WNear.Binary.StateReadRegisterOuter.signature,
      leaf,leafFrame,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,ValType.default,arrays] using body
  have proof := cr (hc.mono (by simp only [Nat.add_mul,op];omega)) next
  have ce : cfg.regularOpCost+(10*cfg.regularOpCost+(bodyCost p*op+fee cfg s p+rest))=
      (bodyCost p+11)*cfg.regularOpCost+fee cfg s p+rest := by simp only [Nat.add_mul,op];omega
  have fe : (fuel+1+bodySteps p)+1=fuel+bodySteps p+2 := by omega
  simpa only [ce,fe] using proof
end WNear.Proofs.StateReadRegisterOuter
