import Proofs.AllocateForwardRetryReturn

/-! Actual313 typed call; its explicit return resumes arbitrary callers. -/
namespace WNear.Proofs.AllocateForwardRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after313

def leaf313 (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.size,.i32 1,.i32 0],inst,arity:=1,height,labels:=[],code:=[]}

theorem entered313_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (11*op+rest)) :
    (entered313 s op).host.gas.Credits rest := by
  have first := StorePair.charged_credits s op (10*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10*op) rest first

theorem wp_call313 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address153 address239 address313 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi153 : p.mi.funcAddrs[153]?=some address153)
    (hf153 : s.funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function))
    (hi239 : p.mi.funcAddrs[239]?=some address239)
    (hf239 : s.funcs[address239]?=some (.wasm WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function239))
    (hi313 : p.mi.funcAddrs[313]?=some address313)
    (hf313 : s.funcs[address313]?=some (.wasm WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function313))
    (hd : callers.length+7<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((cost313 p+11)*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter313 cfg s p) limits
      (base++[Value.i32 (AllocateZeroedRetry.result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+steps313 p+1) (.next (atCode s limits
      (base++[Value.i32 p.size,.i32 1]).toArray frame callers (.call 313::code)))
      ((cost313 p+11)*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let active := entered313 s op
  let leaf := leaf313 frame.inst base.length p
  let saved := {frame with code}
  have ca := entered313_credits s op (cost313 p*op+fee cfg p+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.global := hg
  have f153 : active.funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature leaf.inst WNear.Binary.AllocateZeroed.function) := hf153
  have f239 : active.funcs[address239]?=some (.wasm WNear.Binary.AllocateForward.signature leaf.inst WNear.Binary.AllocateForward.function239) := hf239
  have bn : WP cfg fuel (.next (atCode (after313 cfg active p) limits (base++[Value.i32 (AllocateZeroedRetry.result p)]).toArray
      saved callers saved.code)) rest post := by simpa only [callAfter313,active,saved,atCode,op] using hnext
  have body := wp_body313 cfg fuel rest active limits base leaf saved callers [] p address153 address239 post hn cd ha rfl rfl
    (by simp [leaf,leaf313]) rfl rfl ma ga hv hi153 f153 hi239 f239 hd ca bn
  have call := wp_call_wasm cfg (fuel+steps313 p) (cost313 p*op+fee cfg p+rest) s limits base
    [.i32 p.size,.i32 1] frame callers code 313 address313 p.mi WNear.Binary.AllocateForward.signature
    frame.inst WNear.Binary.AllocateForward.function313 post hcode.retry.originalCode.search.module hi313 hf313 rfl (by omega)
  rw [WNear.Binary.AllocateForward.activation313] at call
  have arrays : #[Value.i32 p.size,Value.i32 1]++#[Value.i32 0]=#[Value.i32 p.size,Value.i32 1,Value.i32 0] := by
    apply Array.toList_inj.mp;simp
  have next : WP cfg (fuel+steps313 p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function313 [.i32 p.size,.i32 1]))
      (cost313 p*op+fee cfg p+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateForward.function313,WNear.Binary.AllocateForward.signature,
      leaf,leaf313,saved,atCode,List.replicate_succ,List.replicate_zero,List.map_cons,List.map_nil,List.append_nil,
      List.length_cons,List.length_nil,ValType.default,List.nil_append,Nat.zero_add,arrays,op] using body
  have result := call (hc.mono (by simp only [op,Nat.add_mul];omega)) next
  have costEq : cfg.regularOpCost+(10*cfg.regularOpCost+(cost313 p*op+fee cfg p+rest))=(cost313 p+11)*cfg.regularOpCost+fee cfg p+rest := by simp only [op,Nat.add_mul];omega
  simpa only [costEq] using result
end WNear.Proofs.AllocateForwardRetry
