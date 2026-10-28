import Proofs.AllocateVectorOuterBody

/-! Actual typed687 activation and normal void return around its complete body. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode after
set_option maxRecDepth 16384

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after cfg (entered s cfg.regularOpCost) p
def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.out687,.i32 p.flag,.i32 p.size,.i32 0,.i64 0],inst,arity:=0,height,labels:=[],code:=[]}

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (12*op+rest)) :
    (entered s op).host.gas.Credits rest := by
  have first := StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest first
 theorem callAfter_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter cfg s p).host.gas.Credits rest := by
  unfold callAfter
  exact after_credits cfg (entered s cfg.regularOpCost) p rest
    (entered_credits s cfg.regularOpCost _ (hc.mono (by simp only [Nat.add_mul];omega)))
 theorem finalFrame_shape (frame : CallFrame) (p : Layout) :
    (finalFrame frame p).arity=frame.arity ∧ (finalFrame frame p).height=frame.height ∧
    (finalFrame frame p).labels=frame.labels := by simp only [finalFrame,cachedFrame,reservedFrame,and_self]

/-- Real687 on positive size and a zero low-byte flag, including its actual nested686,
sequential output copies, stack restoration and normal void return. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global687) (hv : p.global687.value=.i32 p.sp687)
    (hi : p.mi.funcAddrs[687]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateVectorOuter.signature frame.inst WNear.Binary.AllocateVectorOuter.function))
    (hd : callers.length+11<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps p+2) (.next (atCode s limits
      (base++[Value.i32 p.out687,.i32 p.flag,.i32 p.size]).toArray frame callers (.call 687::code)))
      ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (bodyCost p*op+fee cfg p+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter_credits cfg s p rest hc
  have shape := finalFrame_shape leaf p
  have arity : ([] : List Value).length=(finalFrame leaf p).arity := by rw [shape.1];rfl
  have height : (finalFrame leaf p).height=base.length := by rw [shape.2.1];rfl
  have labels : (finalFrame leaf p).labels=[] := by rw [shape.2.2];rfl
  have leaveNext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op,List.append_nil] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter cfg s p) limits base [] (finalFrame leaf p) saved callers post arity height labels cf leaveNext
  have bn : WP cfg (fuel+1) (.next (atCode (after cfg active p) limits base.toArray
      (finalFrame leaf p) (saved::callers) [])) rest post := by simpa only [callAfter,active,List.append_nil] using leave
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.global687 := hg
  have body := wp_body cfg (fuel+1) rest active limits base leaf (saved::callers) [] p post hn cd ha rfl rfl rfl
    (by simp [leaf,leafFrame]) ma ga hv (by simpa only [List.length_cons] using hd) ca bn
  have call := wp_call_wasm cfg ((fuel+1)+bodySteps p) (bodyCost p*op+fee cfg p+rest) s limits base
    [.i32 p.out687,.i32 p.flag,.i32 p.size] frame callers code 687 address p.mi WNear.Binary.AllocateVectorOuter.signature
    frame.inst WNear.Binary.AllocateVectorOuter.function post hcode.vector.allocation.allocation.retry.originalCode.search.module hi hf rfl (by omega)
  rw [WNear.Binary.AllocateVectorOuter.activation] at call
  have arrays : #[Value.i32 p.out687,Value.i32 p.flag,Value.i32 p.size]++#[Value.i32 0,Value.i64 0]=
      #[Value.i32 p.out687,Value.i32 p.flag,Value.i32 p.size,Value.i32 0,Value.i64 0] := by apply Array.toList_inj.mp;simp
  have next : WP cfg ((fuel+1)+bodySteps p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateVectorOuter.signature frame.inst WNear.Binary.AllocateVectorOuter.function [.i32 p.out687,.i32 p.flag,.i32 p.size]))
      (bodyCost p*op+fee cfg p+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateVectorOuter.function,WNear.Binary.AllocateVectorOuter.signature,
      leaf,leafFrame,saved,atCode,List.replicate_succ,List.replicate_zero,List.map_cons,List.map_nil,List.append_nil,List.length_cons,List.length_nil,List.nil_append,Array.append_empty,Nat.zero_add,ValType.default,arrays,op] using body
  have result := call (hc.mono (by simp only [op,Nat.add_mul];omega)) next
  have ce : cfg.regularOpCost+(11*cfg.regularOpCost+(bodyCost p*op+fee cfg p+rest))=(bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest := by simp only [op,Nat.add_mul];omega
  have fe : (fuel+1+bodySteps p)+1=fuel+bodySteps p+2 := by omega
  simpa only [ce,fe] using result
end WNear.Proofs.AllocateVectorOuter
