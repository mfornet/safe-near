import Proofs.AllocateForwardBody

/-! Actual typed239 entry and normal return around the proved153 forwarding body. -/
namespace WNear.Proofs.AllocateForward
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after239

def entered239 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9*op)
def callAfter239 (s : Store NearState) (op : Nat) (p : Layout) := after239 (entered239 s op) op p
def leaf239 (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.size,.i32 1],inst,arity:=1,height,labels:=[],code:=[]}

theorem entered239_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (10*op+rest)) :
    (entered239 s op).host.gas.Credits rest := by
  have first := StorePair.charged_credits s op (9*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (9*op) rest first

theorem callAfter239_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits ((cost239 p+10)*op+rest)) : (callAfter239 s op p).host.gas.Credits rest := by
  unfold callAfter239
  exact after239_credits (entered239 s op) op rest p (entered239_credits s op _ (hc.mono (by simp only [Nat.add_mul];omega)))

theorem wp_call239 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address153 address239 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi153 : p.mi.funcAddrs[153]?=some address153)
    (hf153 : s.funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function))
    (hi239 : p.mi.funcAddrs[239]?=some address239)
    (hf239 : s.funcs[address239]?=some (.wasm WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function239))
    (hd : callers.length+5<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((cost239 p+10)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter239 s cfg.regularOpCost p) limits
      (base++[Value.i32 (AllocateZeroed.result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+steps239 p+2) (.next (atCode s limits
      (base++[Value.i32 p.size,.i32 1]).toArray frame callers (.call 239::code)))
      ((cost239 p+10)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered239 s op
  let leaf := leaf239 frame.inst base.length p
  let saved := {frame with code}
  have ca := entered239_credits s op (cost239 p*op+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter239_credits s op rest p hc
  have leaveNext : WP cfg fuel (.next (atCode (callAfter239 s op p) limits (base++[Value.i32 (AllocateZeroed.result p)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter239 s op p) limits base [.i32 (AllocateZeroed.result p)] leaf saved callers post rfl rfl rfl cf leaveNext
  have bn : WP cfg (fuel+1) (.next (atCode (after239 active op p) limits (base++[Value.i32 (AllocateZeroed.result p)]).toArray
      leaf (saved::callers) [])) rest post := by simpa only [callAfter239,active] using leave
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.global := hg
  have f153 : active.funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature leaf.inst WNear.Binary.AllocateZeroed.function) := hf153
  have body := wp_body239 cfg (fuel+1) rest active limits base leaf (saved::callers) [] p address153 post hn cd ha rfl rfl
    ma ga hv hi153 f153 (by simpa only [List.length_cons] using hd) ca bn
  have call := wp_call_wasm cfg ((fuel+1)+steps239 p) (cost239 p*op+rest) s limits base
    [.i32 p.size,.i32 1] frame callers code 239 address239 p.mi WNear.Binary.AllocateForward.signature
    frame.inst WNear.Binary.AllocateForward.function239 post hcode.positive.search.module hi239 hf239 rfl (by omega)
  rw [WNear.Binary.AllocateForward.activation239] at call
  have next : WP cfg ((fuel+1)+steps239 p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function239 [.i32 p.size,.i32 1]))
      (cost239 p*op+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateForward.function239,WNear.Binary.AllocateForward.signature,
      leaf,leaf239,saved,atCode,List.replicate_zero,List.map_nil,List.append_nil,List.length_cons,List.length_nil,List.nil_append,Array.append_empty,Nat.zero_add,op] using body
  have result := call (hc.mono (by simp only [op,Nat.add_mul];omega)) next
  have fee : cfg.regularOpCost+(9*cfg.regularOpCost+(cost239 p*op+rest))=(cost239 p+10)*cfg.regularOpCost+rest := by simp only [op,Nat.add_mul];omega
  have fuelEq : (fuel+1+steps239 p)+1=fuel+steps239 p+2 := by omega
  simpa only [fee,fuelEq] using result
end WNear.Proofs.AllocateForward
