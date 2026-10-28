import Proofs.AllocateVectorBody

/-! Actual typed686 call. Its explicit return resumes the caller without an extra leave. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode after

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after cfg (entered s cfg.regularOpCost) p
def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.out686,.i32 p.size,.i32 1,.i32 0,.i32 0,.i32 0],inst,arity:=0,height,labels:=[],code:=[]}

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (12*op+rest)) :
    (entered s op).host.gas.Credits rest := by
  have a := StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest a

theorem callAfter_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter cfg s p).host.gas.Credits rest := by
  unfold callAfter
  exact after_credits cfg (entered s cfg.regularOpCost) p rest
    (entered_credits s cfg.regularOpCost _ (hc.mono (by simp only [Nat.add_mul];omega)))

/-- Original heap/code/bounds and gas credits suffice for the complete selected
positive alignment-one zeroed vector call, including all nested execution. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.outerGlobal)
    (hv : p.outerGlobal.value=.i32 p.outerSP)
    (hi : p.mi.funcAddrs[686]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateVector.signature frame.inst WNear.Binary.AllocateVector.function))
    (hd : callers.length+10<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps p+1) (.next (atCode s limits
      (base++[Value.i32 p.out686,.i32 p.size,.i32 1]).toArray frame callers (.call 686::code)))
      ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (bodyCost p*op+fee cfg p+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have cd : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have ma : active.mems[p.memoryIndex]?=some p.memory := hm
  have ga : active.globals[p.globalIndex]?=some p.outerGlobal := hg
  have bn : WP cfg fuel (.next (atCode (after cfg active p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [active,callAfter,saved,atCode,op] using hnext
  have body := wp_body cfg fuel rest active limits base leaf saved callers [] p post hn cd haRoot rfl rfl rfl
    (by simp [leaf,leafFrame]) rfl rfl ma ga hv hd ca bn
  have om : s.modules[frame.inst]?=some p.mi := by
    simpa only [AllocatePositive.searchLayout] using hcode.allocation.allocation.retry.originalCode.search.module
  have call := wp_call_wasm cfg (fuel+bodySteps p) (bodyCost p*op+fee cfg p+rest) s limits base
    [.i32 p.out686,.i32 p.size,.i32 1] frame callers code 686 address p.mi WNear.Binary.AllocateVector.signature
    frame.inst WNear.Binary.AllocateVector.function post om hi hf rfl (by omega)
  rw [WNear.Binary.AllocateVector.activation] at call
  have arr : #[Value.i32 p.out686,Value.i32 p.size,Value.i32 1]++#[Value.i32 0,Value.i32 0,Value.i32 0]=
      #[Value.i32 p.out686,Value.i32 p.size,Value.i32 1,Value.i32 0,Value.i32 0,Value.i32 0] := by
    apply Array.toList_inj.mp;simp
  have bc : WP cfg (fuel+bodySteps p) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateVector.signature frame.inst WNear.Binary.AllocateVector.function
      [.i32 p.out686,.i32 p.size,.i32 1])) (bodyCost p*op+fee cfg p+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateVector.function,WNear.Binary.AllocateVector.signature,
      leaf,leafFrame,saved,atCode,List.map_cons,List.map_nil,ValType.default,arr,List.append_nil,List.length_nil,op] using body
  have result := call (hc.mono (by simp only [Nat.add_mul,op];omega)) bc
  have ce : cfg.regularOpCost+(11*cfg.regularOpCost+(bodyCost p*op+fee cfg p+rest))=
      (bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest := by simp only [Nat.add_mul,op];omega
  rw [ce] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocateVector
