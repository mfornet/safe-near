import Proofs.StateDispatchLengthOuterState
import Proofs.InterfaceStack

/-! Actual thirteen scalar instructions before f524 invokes f440. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode reserved inputStore arguments
set_option maxRecDepth 16384

private theorem wp_input (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (reg : UInt64) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]? = some (.i64 reg)) (h2 : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 16 ≤ memory.byteSize) (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (storeI64 (paid s cfg.regularOpCost 3) index (scratch.toNat+8) memory reg) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers ([.local_get 2,.local_get 1,.store .i64 none {align:=3,offset:=8}]++code))) (3*cfg.regularOpCost+rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := hm
  have mem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := hmem
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+2) _ s limits stack frame callers _ 2 (.i32 scratch) post h2 (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 1 (.i64 reg) post h1
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code {align:=3,offset:=8} scratch reg mi index memory post hm2 hi mem2 (by dsimp only; omega)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · simpa only [paid] using hnext

private theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 out)) (h2 : frame.locals[2]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((base.push (.i32 out)).push (.i32 1055020)).push (.i32 (scratch+8))) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits base frame callers
      ([.local_get 0,.i32_const 1055020,.local_get 2,.i32_const 8,.i32_binop .add]++code))) (5*cfg.regularOpCost+rest) post := by
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+4) _ s limits base frame callers _ 0 (.i32 out) post h0 (hc.mono (by omega))
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 1055020 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+2) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ 2 (.i32 scratch) post h2
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  apply wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 4) limits _ frame callers code scratch 8 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  · simpa only [paid] using hnext

/-- No callee outcome is assumed: this only reaches the real call instruction. -/
theorem wp_prefix (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hr : Ready s limits frame callers p extra)
    (hc : s.host.gas.Credits (13*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (arguments s cfg.regularOpCost p) limits
      (base++[Value.i32 p.out,.i32 1055020,.i32 (scratch p+8)]).toArray (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+13) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDispatchLengthOuter.head++code))) (13*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have b0 : 5*op+(8*op+rest) ≤ 13*cfg.regularOpCost+rest := by dsimp [op]; omega
  have b1 : 3*op+(5*op+rest) ≤ 8*op+rest := by omega
  have cr : (reserved s op p).host.gas.Credits (8*op+rest) := by
    unfold reserved
    exact paid_credits s op 5 _ (hc.mono b0)
  have ci : (inputStore s op p).host.gas.Credits (5*op+rest) := by
    unfold inputStore; rw [storeI64_host]; exact paid_credits _ op 3 _ (cr.mono b1)
  let rf := reservedFrame frame p
  have h0 : rf.locals[0]? = some (.i32 p.out) := by simpa [rf,reservedFrame] using hr.outLocal
  have h1 : rf.locals[1]? = some (.i64 p.register) := by simpa [rf,reservedFrame] using hr.registerLocal
  have h2 : rf.locals[2]? = some (.i32 (scratch p)) := by simp [rf,reservedFrame,show 2<frame.locals.size by have:=hr.localSize;omega]
  have an : WP cfg fuel (.next (atCode (paid (inputStore s op p) op 5) limits
      (((base.toArray.push (.i32 p.out)).push (.i32 1055020)).push (.i32 (scratch p+8))) rf callers code)) rest post := by
    have hs : (base++[Value.i32 p.out,.i32 1055020,.i32 (scratch p+8)]).toArray =
      (((base.toArray.push (.i32 p.out)).push (.i32 1055020)).push (.i32 (scratch p+8))) := by apply Array.toList_inj.mp; simp
    simpa only [arguments,rf,op,hs] using hnext
  have arg := wp_arguments cfg fuel rest (inputStore s op p) limits base.toArray rf callers code p.out (scratch p) post h0 h2 ci an
  have moduleR : (reserved s op p).modules[rf.inst]? = some p.inner.mi := by simpa only [reserved,setGlobal,paid,chargedStore,rf,reservedFrame] using hr.code.prefixCode.module
  have memR : (reserved s op p).mems[p.inner.memoryIndex]? = some p.memory := by simpa only [reserved,setGlobal,paid,chargedStore] using hr.memory
  have input := wp_input cfg (fuel+5) (5*op+rest) (reserved s op p) limits base.toArray rf callers
    ([.local_get 0,.i32_const 1055020,.local_get 2,.i32_const 8,.i32_binop .add]++code) (scratch p) p.register p.inner.mi p.inner.memoryIndex p.memory post
    h1 h2 moduleR hr.code.prefixCode.memoryIndex memR hr.inputWriteBound (cr.mono b1)
    (by simpa only [inputStore,op] using arg)
  have pn : WP cfg (fuel+8) (.next (atCode (reserved s op p) limits base.toArray rf callers
      ([.local_get 2,.local_get 1,.store .i64 none {align:=3,offset:=8},.local_get 0,.i32_const 1055020,.local_get 2,.i32_const 8,.i32_binop .add]++code))) (8*op+rest) post := by
    simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 3*cfg.regularOpCost+(5*op+rest)=8*op+rest by dsimp [op];omega] using input
  have headProof := InterfaceStack.wp_reserve cfg (fuel+8) (8*op+rest) s limits base.toArray frame callers
    ([.local_get 2,.local_get 1,.store .i64 none {align:=3,offset:=8},.local_get 0,.i32_const 1055020,.local_get 2,.i32_const 8,.i32_binop .add]++code)
    p.inner.mi p.inner.globalIndex p.global p.sp 2 16 post hr.code.prefixCode.module hr.code.prefixCode.globalIndex hr.global hr.sp (hc.mono b0)
    (by simpa only [reserved,reservedFrame,rf,scratch,op] using pn)
  simpa only [WNear.Binary.StateDispatchLengthOuter.head,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(8*op+rest)=13*cfg.regularOpCost+rest by dsimp [op];omega] using headProof
end WNear.Proofs.StateDispatchLengthOuter
