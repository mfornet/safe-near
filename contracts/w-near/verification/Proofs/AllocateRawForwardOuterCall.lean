import Proofs.AllocateRawForwardReturn

/-! Actual310 typed call; its explicit return resumes arbitrary callers. -/
namespace WNear.Proofs.AllocateRawForward
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after310

def leaf310 (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.size,.i32 1,.i32 0],inst,arity:=1,height,labels:=[],code:=[]}

theorem entered310_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (11*op+rest)) :
    (entered310 s op).host.gas.Credits rest := by
  have first := StorePair.charged_credits s op (10*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10*op) rest first

theorem wp_call310 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address581 address236 address310 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi581 : p.mi.funcAddrs[581]?=some address581)
    (hf581 : s.funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature frame.inst WNear.Binary.Allocate.function))
    (hi236 : p.mi.funcAddrs[236]?=some address236)
    (hf236 : s.funcs[address236]?=some (.wasm WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function236))
    (hi310 : p.mi.funcAddrs[310]?=some address310)
    (hf310 : s.funcs[address310]?=some (.wasm WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function310))
    (hd : callers.length+6<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((cost310 p+11)*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter310 cfg s p) limits
      (base++[Value.i32 (AllocateRetry.result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+steps310 p+1) (.next (atCode s limits
      (base++[Value.i32 p.size,.i32 1]).toArray frame callers (.call 310::code)))
      ((cost310 p+11)*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let active := entered310 s op
  let leaf := leaf310 frame.inst base.length p
  let saved := {frame with code}
  have ca := entered310_credits s op (cost310 p*op+fee cfg p+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.global := hg
  have f581 : active.funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature leaf.inst WNear.Binary.Allocate.function) := hf581
  have f236 : active.funcs[address236]?=some (.wasm WNear.Binary.AllocateRawForward.signature leaf.inst WNear.Binary.AllocateRawForward.function236) := hf236
  have bn : WP cfg fuel (.next (atCode (after310 cfg active p) limits (base++[Value.i32 (AllocateRetry.result p)]).toArray
      saved callers saved.code)) rest post := by simpa only [callAfter310,active,saved,atCode,op] using hnext
  have body := wp_body310 cfg fuel rest active limits base leaf saved callers [] p address581 address236 post hn cd ha rfl rfl
    (by simp [leaf,leaf310]) rfl rfl ma ga hv hi581 f581 hi236 f236 hd ca bn
  have call := wp_call_wasm cfg (fuel+steps310 p) (cost310 p*op+fee cfg p+rest) s limits base
    [.i32 p.size,.i32 1] frame callers code 310 address310 p.mi WNear.Binary.AllocateRawForward.signature
    frame.inst WNear.Binary.AllocateRawForward.function310 post hcode.originalCode.search.module hi310 hf310 rfl (by omega)
  rw [WNear.Binary.AllocateRawForward.activation310] at call
  have arrays : #[Value.i32 p.size,Value.i32 1]++#[Value.i32 0]=#[Value.i32 p.size,Value.i32 1,Value.i32 0] := by
    apply Array.toList_inj.mp;simp
  have next : WP cfg (fuel+steps310 p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function310 [.i32 p.size,.i32 1]))
      (cost310 p*op+fee cfg p+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateRawForward.function310,WNear.Binary.AllocateRawForward.signature,
      leaf,leaf310,saved,atCode,List.replicate_succ,List.replicate_zero,List.map_cons,List.map_nil,List.append_nil,
      List.length_cons,List.length_nil,ValType.default,List.nil_append,Nat.zero_add,arrays,op] using body
  have result := call (hc.mono (by simp only [op,Nat.add_mul];omega)) next
  have costEq : cfg.regularOpCost+(10*cfg.regularOpCost+(cost310 p*op+fee cfg p+rest))=(cost310 p+11)*cfg.regularOpCost+fee cfg p+rest := by simp only [op,Nat.add_mul];omega
  simpa only [costEq] using result
end WNear.Proofs.AllocateRawForward
