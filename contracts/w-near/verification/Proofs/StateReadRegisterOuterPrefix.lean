import Proofs.StateReadRegisterOuterSetup
import Proofs.StateReadRegisterOuterLengthReady
import Proofs.StateReadRegisterOuterPhases

/-! Actual523 prefix executes the complete real524 register-length dispatcher. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode looked actualLength lengthArguments

theorem wp_prefix (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p extra)
    (haRoot : p.allocator=1074896) (h1 : frame.locals[1]?=some (.i64 p.register))
    (hs : 3≤frame.locals.size) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global523) (hv : p.global523.value=.i32 p.sp523)
    (hd : callers.length+5<limits.maxCallDepth)
    (hc : s.host.gas.Credits (302*cfg.regularOpCost+s.host.extCosts.cost "base"+rest))
    (hnext : WP cfg fuel (.next (atCode (looked cfg s p) limits base.toArray (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+203) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateReadRegisterOuter.reserve++WNear.Binary.StateReadRegisterOuter.saveRegister++WNear.Binary.StateReadRegisterOuter.lengthArguments++[.call 524]++code)))
      (302*cfg.regularOpCost+s.host.extCosts.cost "base"+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  let q := actualLength p
  let leaf := StateDispatchLengthOuter.leafFrame rf.inst base.length q
  have cd : Code s leaf.inst p extra := by simpa only [leaf,StateDispatchLengthOuter.leafFrame,rf,reservedFrame] using hcode
  have hr := cd.length_ready cfg s limits leaf ({rf with code}::callers) p extra hn haRoot hm hg
    (by simp only [leaf,StateDispatchLengthOuter.leafFrame,q,actualLength,lengthOn];rfl)
    (by simp only [leaf,StateDispatchLengthOuter.leafFrame,q,actualLength,lengthOn];rfl)
    (by simp [leaf,StateDispatchLengthOuter.leafFrame])
    (by simp only [List.length_cons];omega)
  have fields := lengthArguments_fields s op p
  have hf : (lengthArguments s op p).funcs[p.address524]?=some (.wasm WNear.Binary.StateDispatchLengthOuter.signature rf.inst WNear.Binary.StateDispatchLengthOuter.function) := by
    rw [fields.1];simpa only [rf,reservedFrame] using hcode.function524
  have cc : (lengthArguments s op p).host.gas.Credits (290*op+(lengthArguments s op p).host.extCosts.cost "base"+rest) := by
    rw [lengthArguments_costs]
    exact lengthArguments_credits s op _ p (hc.mono (by dsimp [op];omega))
  have cn : WP cfg fuel (.next (atCode (StateDispatchLengthOuter.callAfter cfg (lengthArguments s op p) q) limits base.toArray rf callers code)) rest post := by
    simpa only [looked,rf,q,op] using hnext
  have call := StateDispatchLengthOuter.wp_call cfg extra fuel rest (lengthArguments s op p) limits base rf callers code q p.address524 post hr (by simpa only [q,actualLength,lengthOn] using hcode.index524) hf cc cn
  rw [lengthArguments_costs] at call
  have an : WP cfg (fuel+191) (.next (atCode (lengthArguments s op p) limits
      (base++[Value.i32 (scratch p+8),.i64 p.register]).toArray rf callers (.call 524::code)))
      (290*op+s.host.extCosts.cost "base"+rest) post := by
    simpa only [q,actualLength,lengthOn,op] using call
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have saveBound : (scratch p).toNat+24+8≤p.memory.byteSize := by rw [nums.1];omega
  have om : s.modules[frame.inst]?=some p.mi := by simpa only [actualLength,lengthOn] using hcode.prefixCode.module
  have oi : p.mi.memAddrs[0]?=some p.memoryIndex := by simpa only [actualLength,lengthOn] using hcode.prefixCode.memoryIndex
  have og : p.mi.globalAddrs[0]?=some p.globalIndex := by simpa only [actualLength,lengthOn] using hcode.prefixCode.globalIndex
  have setup := wp_setup cfg (fuel+191) (290*op+s.host.extCosts.cost "base"+rest) s limits base frame callers (.call 524::code) p post
    h1 hs om oi hm og hg hv saveBound
    (hc.mono (by dsimp [op];omega)) an
  have ce : 12*cfg.regularOpCost+(290*op+s.host.extCosts.cost "base"+rest)=302*cfg.regularOpCost+s.host.extCosts.cost "base"+rest := by dsimp [op];omega
  rw [ce] at setup
  simpa only [List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using setup
end WNear.Proofs.StateReadRegisterOuter
