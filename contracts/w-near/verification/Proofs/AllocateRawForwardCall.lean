import Proofs.AllocateRawForwardBody

/-! Actual typed236 entry and normal return around the proved581 forwarding body. -/
namespace WNear.Proofs.AllocateRawForward
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after236

def leaf236 (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.size,.i32 1],inst,arity:=1,height,labels:=[],code:=[]}

theorem entered236_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (10*op+rest)) :
    (entered236 s op).host.gas.Credits rest := by
  have first := StorePair.charged_credits s op (9*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (9*op) rest first

theorem wp_call236 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address581 address236 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi581 : p.mi.funcAddrs[581]?=some address581)
    (hf581 : s.funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature frame.inst WNear.Binary.Allocate.function))
    (hi236 : p.mi.funcAddrs[236]?=some address236)
    (hf236 : s.funcs[address236]?=some (.wasm WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function236))
    (hd : callers.length+5<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((cost236 p+10)*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter236 cfg s p) limits
      (base++[Value.i32 (AllocateRetry.result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+steps236 p+2) (.next (atCode s limits
      (base++[Value.i32 p.size,.i32 1]).toArray frame callers (.call 236::code)))
      ((cost236 p+10)*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let active := entered236 s op
  let leaf := leaf236 frame.inst base.length p
  let saved := {frame with code}
  have ca := entered236_credits s op (cost236 p*op+fee cfg p+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter236_credits cfg s p rest hc
  have leaveNext : WP cfg fuel (.next (atCode (callAfter236 cfg s p) limits (base++[Value.i32 (AllocateRetry.result p)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter236 cfg s p) limits base [.i32 (AllocateRetry.result p)] leaf saved callers post rfl rfl rfl cf leaveNext
  have bn : WP cfg (fuel+1) (.next (atCode (after236 cfg active p) limits (base++[Value.i32 (AllocateRetry.result p)]).toArray
      leaf (saved::callers) [])) rest post := by simpa only [callAfter236,active] using leave
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.global := hg
  have f581 : active.funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature leaf.inst WNear.Binary.Allocate.function) := hf581
  have body := wp_body236 cfg (fuel+1) rest active limits base leaf (saved::callers) [] p address581 post hn cd ha rfl rfl
    ma ga hv hi581 f581 (by simpa only [List.length_cons] using hd) ca bn
  have call := wp_call_wasm cfg ((fuel+1)+steps236 p) (cost236 p*op+fee cfg p+rest) s limits base
    [.i32 p.size,.i32 1] frame callers code 236 address236 p.mi WNear.Binary.AllocateRawForward.signature
    frame.inst WNear.Binary.AllocateRawForward.function236 post hcode.originalCode.search.module hi236 hf236 rfl (by omega)
  rw [WNear.Binary.AllocateRawForward.activation236] at call
  have next : WP cfg ((fuel+1)+steps236 p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function236 [.i32 p.size,.i32 1]))
      (cost236 p*op+fee cfg p+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateRawForward.function236,WNear.Binary.AllocateRawForward.signature,
      leaf,leaf236,saved,atCode,List.replicate_zero,List.map_nil,List.append_nil,List.length_cons,List.length_nil,List.nil_append,Array.append_empty,Nat.zero_add,op] using body
  have result := call (hc.mono (by simp only [op,Nat.add_mul];omega)) next
  have costEq : cfg.regularOpCost+(9*cfg.regularOpCost+(cost236 p*op+fee cfg p+rest))=(cost236 p+10)*cfg.regularOpCost+fee cfg p+rest := by simp only [op,Nat.add_mul];omega
  have fuelEq : (fuel+1+steps236 p)+1=fuel+steps236 p+2 := by omega
  simpa only [costEq,fuelEq] using result
end WNear.Proofs.AllocateRawForward
