import Proofs.AllocateZeroedGas

/-! Actual typed f153 entry, both real callees, and normal pointer return. -/
namespace WNear.Proofs.AllocateZeroed
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode after
set_option maxRecDepth 16384

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p
def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.allocator,.i32 p.size,.i32 1],inst,arity:=1,height,labels:=[],code:=[]}

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (11*op+rest)) :
    (entered s op).host.gas.Credits rest := by
  have first := StorePair.charged_credits s op (10*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10*op) rest first
 theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits ((bodyCost p+11)*op+rest)) : (callAfter s op p).host.gas.Credits rest := by
  unfold callAfter
  exact after_credits (entered s op) op rest p (entered_credits s op _ (hc.mono (by simp only [Nat.add_mul];omega)))
 theorem resultFrame_shape (frame : CallFrame) (p : Layout) :
    (resultFrame frame p).arity=frame.arity ∧ (resultFrame frame p).height=frame.height ∧
    (resultFrame frame p).labels=frame.labels := by simp only [resultFrame,and_self]

/-- Positive alignment-one f153 on the original directly-fitting heap. Neither
allocation nor memset is supplied as a successful-execution premise. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi : p.mi.funcAddrs[153]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function))
    (hd : callers.length+4<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost p+11)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits
      (base++[Value.i32 (result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps p+2) (.next (atCode s limits
      (base++[Value.i32 p.allocator,.i32 p.size,.i32 1]).toArray frame callers (.call 153::code)))
      ((bodyCost p+11)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (bodyCost p*op+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cf := callAfter_credits s op rest p hc
  have shape := resultFrame_shape leaf p
  have arity : [Value.i32 (result p)].length=(resultFrame leaf p).arity := by rw [shape.1];rfl
  have height : (resultFrame leaf p).height=base.length := by rw [shape.2.1];rfl
  have labels : (resultFrame leaf p).labels=[] := by rw [shape.2.2];rfl
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits (base++[Value.i32 (result p)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base [.i32 (result p)] (resultFrame leaf p) saved callers post arity height labels cf leaveNext
  have bn : WP cfg (fuel+1) (.next (atCode (after active op p) limits (base++[Value.i32 (result p)]).toArray
      (resultFrame leaf p) (saved::callers) [])) rest post := by simpa only [callAfter,active] using leave
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.global := hg
  have body := wp_body cfg (fuel+1) rest active limits base leaf (saved::callers) [] p post hn cd rfl rfl rfl
    (by simp [leaf,leafFrame]) ma ga hv (by simpa only [List.length_cons] using hd) ca bn
  have call := wp_call_wasm cfg ((fuel+1)+bodySteps p) (bodyCost p*op+rest) s limits base
    [.i32 p.allocator,.i32 p.size,.i32 1] frame callers code 153 address p.mi WNear.Binary.AllocateZeroed.signature
    frame.inst WNear.Binary.AllocateZeroed.function post hcode.positive.search.module hi hf rfl (by omega)
  rw [WNear.Binary.AllocateZeroed.activation] at call
  have next : WP cfg ((fuel+1)+bodySteps p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function [.i32 p.allocator,.i32 p.size,.i32 1]))
      (bodyCost p*op+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateZeroed.function,WNear.Binary.AllocateZeroed.signature,
      leaf,leafFrame,saved,atCode,List.replicate_zero,List.map_nil,List.append_nil,List.length_cons,List.length_nil,List.nil_append,Array.append_empty,Nat.zero_add,op] using body
  have result := call (hc.mono (by simp only [op,Nat.add_mul];omega)) next
  have fee : cfg.regularOpCost+(10*cfg.regularOpCost+(bodyCost p*op+rest))=(bodyCost p+11)*cfg.regularOpCost+rest := by simp only [op,Nat.add_mul];omega
  have fuelEq : (fuel+1+bodySteps p)+1=fuel+bodySteps p+2 := by omega
  simpa only [fee,fuelEq] using result
end WNear.Proofs.AllocateZeroed
