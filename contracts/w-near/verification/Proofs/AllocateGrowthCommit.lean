import Binary.AllocateGrowth
import Proofs.AllocateGrowthBytes
import NearVM.MeteredMemoryRules
import NearVM.MeteredI32MemoryRules
import Proofs.ValueReturnLazyReturn

/-! Sequential fresh-header initialization and growth-result record writes. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode writeI32 writeI64

def freshMemory (memory : Memory) (header bytes : UInt32) :=
  writeI32 (writeI32 (writeI64 memory header.toNat 0) (header.toNat+8) 0)
    header.toNat ((header+bytes)|||2)
def freshFrame (frame : CallFrame) (header : UInt32) :=
  {frame with locals:=(frame.locals.set! 2 (.i32 header)).set! 3 (.i32 0)}
def freshStore (s : Store NearState) (op index : Nat) (memory : Memory) (header bytes : UInt32) :=
  let first := storeI64 (paid s op 6) index header.toNat memory 0
  let second := storeI32 (paid first op 5) index (header.toNat+8) (writeI64 memory header.toNat 0) 0
  storeI32 (paid second op 7) index header.toNat
    (writeI32 (writeI64 memory header.toNat 0) (header.toNat+8) 0) ((header+bytes)|||2)

theorem wp_fresh_header (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (oldPages bytes : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 oldPages)) (h4 : frame.locals[4]?=some (.i32 bytes))
    (hs : 5≤frame.locals.size) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb : (pageBytes oldPages).toNat+12≤memory.byteSize)
    (hc : s.host.gas.Credits (18*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (freshStore s cfg.regularOpCost index memory (pageBytes oldPages) bytes)
      limits stack (freshFrame frame (pageBytes oldPages)) callers code)) rest post) :
    WP cfg (fuel+18) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateGrowth.freshHeader++code))) (18*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let header := pageBytes oldPages
  let f1 : CallFrame := {frame with locals:=frame.locals.set! 2 (.i32 header)}
  let f2 := freshFrame frame header
  let m1 := writeI64 memory header.toNat 0
  let m2 := writeI32 m1 (header.toNat+8) 0
  let s1 := storeI64 (paid s op 6) index header.toNat memory 0
  let s2 := storeI32 (paid s1 op 5) index (header.toNat+8) m1 0
  have spec1 := writeI64_spec memory header.toNat 0 hw (by dsimp [header] at ⊢; omega)
  have spec2 := writeI32_spec m1 (header.toNat+8) 0 spec1.1 (by rw [show m1.byteSize=memory.byteSize from spec1.2.1]; dsimp [header]; omega)
  have mm1 : s1.mems[index]?=some m1 := by
    apply storeI64_memory
    simpa only [paid,chargedStore] using hmem
  have mm2 : s2.mems[index]?=some m2 := by
    apply storeI32_memory
    simpa only [paid,chargedStore] using mm1
  have c1 : s1.host.gas.Credits (12*op+rest) := paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  have c2 : s2.host.gas.Credits (7*op+rest) := paid_credits s1 op 5 _ (c1.mono (by omega))
  have f12 : f1.locals[2]?=some (.i32 header) := by simp [f1,show 2<frame.locals.size by omega]
  have f22 : f2.locals[2]?=some (.i32 header) := by simp [f2,freshFrame,show 2<frame.locals.size by omega]
  have f24 : f2.locals[4]?=some (.i32 bytes) := by simp [f2,freshFrame,h4]
  have hm5 : (paid s op 5).modules[f1.inst]?=some mi := by simpa only [paid,chargedStore,f1] using hm
  have mm5 : (paid s op 5).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have hm10 : (paid s1 op 4).modules[f2.inst]?=some mi := by simpa only [paid,chargedStore,s1,storeI64,f2,freshFrame] using hm
  have mm10 : (paid s1 op 4).mems[index]?=some m1 := by simpa only [paid,chargedStore] using mm1
  have hm17 : (paid s2 op 6).modules[f2.inst]?=some mi := by simpa only [paid,chargedStore,s2,storeI32,s1,storeI64,f2,freshFrame] using hm
  have mm17 : (paid s2 op 6).mems[index]?=some m2 := by simpa only [paid,chargedStore] using mm2
  unfold WNear.Binary.AllocateGrowth.freshHeader
  simp only [List.cons_append,List.nil_append]
  rw [show 18*cfg.regularOpCost+rest=cfg.regularOpCost+(17*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+17) _ s limits stack frame callers _ 2 (.i32 oldPages) post h2
  · exact paid_credits s op 0 _ (hc.mono (by dsimp [op]; omega))
  rw [show 17*op+rest=cfg.regularOpCost+(16*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+16) _ (paid s op 1) limits _ frame callers _ 16 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 16*op+rest=cfg.regularOpCost+(15*op+rest) by dsimp [op]; omega]
  apply wp_i32_binop_ok cfg (fuel+15) _ (paid s op 2) limits stack frame callers _ .shl oldPages 16 header post rfl
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 15*op+rest=cfg.regularOpCost+(14*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+14) _ (paid s op 3) limits stack frame callers _ 2 (.i32 header) post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 14*op+rest=cfg.regularOpCost+(13*op+rest) by dsimp [op]; omega]
  apply wp_i64_const cfg (fuel+13) _ (paid s op 4) limits _ f1 callers _ 0 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 13*op+rest=cfg.regularOpCost+(12*op+rest) by dsimp [op]; omega]
  apply wp_i64_store cfg (fuel+12) _ (paid s op 5) limits stack f1 callers _ {align:=3,offset:=0} header 0 mi index memory post hm5 hi mm5 (by dsimp [header]; omega)
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  rw [show 12*op+rest=cfg.regularOpCost+(11*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+11) _ s1 limits stack f1 callers _ 0 post
  · exact paid_credits s1 op 0 _ (c1.mono (by dsimp [op]; omega))
  rw [show 11*op+rest=cfg.regularOpCost+(10*op+rest) by dsimp [op]; omega]
  apply wp_local_set cfg (fuel+10) _ (paid s1 op 1) limits stack f1 callers _ 3 (.i32 0) post
  · exact paid_credits s1 op 1 _ (c1.mono (by dsimp [op]; omega))
  rw [show 10*op+rest=cfg.regularOpCost+(9*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+9) _ (paid s1 op 2) limits stack f2 callers _ 2 (.i32 header) post f22
  · exact paid_credits s1 op 2 _ (c1.mono (by dsimp [op]; omega))
  rw [show 9*op+rest=cfg.regularOpCost+(8*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+8) _ (paid s1 op 3) limits _ f2 callers _ 0 post
  · exact paid_credits s1 op 3 _ (c1.mono (by dsimp [op]; omega))
  rw [show 8*op+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op]; omega]
  apply wp_i32_store cfg (fuel+7) _ (paid s1 op 4) limits stack f2 callers _ {align:=2,offset:=8} header 0 mi index m1 post hm10 hi mm10 (by rw [spec1.2.1]; dsimp [header]; omega)
  · exact paid_credits s1 op 4 _ (c1.mono (by dsimp [op]; omega))
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ s2 limits stack f2 callers _ 2 (.i32 header) post f22
  · exact paid_credits s2 op 0 _ (c2.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ (paid s2 op 1) limits _ f2 callers _ 2 (.i32 header) post f22
  · exact paid_credits s2 op 1 _ (c2.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s2 op 2) limits _ f2 callers _ 4 (.i32 bytes) post f24
  · exact paid_credits s2 op 2 _ (c2.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel+3) _ (paid s2 op 3) limits (stack.push (.i32 header)) f2 callers _ header bytes post
  · exact paid_credits s2 op 3 _ (c2.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s2 op 4) limits _ f2 callers _ 2 post
  · exact paid_credits s2 op 4 _ (c2.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(1*op+rest) by dsimp [op]; omega]
  apply wp_i32_or cfg (fuel+1) _ (paid s2 op 5) limits (stack.push (.i32 header)) f2 callers _ (header+bytes) 2 post
  · exact paid_credits s2 op 5 _ (c2.mono (by dsimp [op]; omega))
  rw [show 1*op+rest=cfg.regularOpCost+(0*op+rest) by dsimp [op]; omega]
  apply wp_i32_store cfg (fuel+0) _ (paid s2 op 6) limits stack f2 callers _ {align:=2,offset:=0} header ((header+bytes)|||2) mi index m2 post hm17 hi mm17 (by rw [spec2.2.1,spec1.2.1]; dsimp [header]; omega)
  · exact paid_credits s2 op 6 _ (c2.mono (by dsimp [op]; omega))
  simpa only [freshStore,freshFrame,f1,f2,s1,s2,m1,m2,header,op,paid,Nat.add_zero,Nat.zero_mul,Nat.zero_add] using hnext

/-- The result record stores the new free-list pointer before its success tag. -/
def recordMemory (memory : Memory) (record header : UInt32) :=
  writeI32 (writeI32 memory (record.toNat+4) header) record.toNat 0

def recordStore (s : Store NearState) (op index : Nat) (memory : Memory) (record header : UInt32) :=
  let first := storeI32 (paid s op 3) index (record.toNat+4) memory header
  paid (storeI32 (paid first op 3) index record.toNat (writeI32 memory (record.toNat+4) header) 0) op 1

/-- The real seven-instruction record/explicit-return suffix, allowing arbitrary
aliases between the record and freshly initialized memory. -/
theorem wp_record_return (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (record header : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 record)) (h2 : frame.locals[2]?=some (.i32 header))
    (h3 : frame.locals[3]?=some (.i32 0)) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hw : memory.wf) (hb : record.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordStore s cfg.regularOpCost index memory record header)
      limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateGrowth.recordReturn++code))) (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first := storeI32 (paid s op 3) index (record.toNat+4) memory header
  let written := writeI32 memory (record.toNat+4) header
  let second := storeI32 (paid first op 3) index record.toNat written 0
  have spec := writeI32_spec memory (record.toNat+4) header hw (by omega)
  have mm : first.mems[index]?=some written := by
    apply storeI32_memory
    simpa only [paid,chargedStore] using hmem
  have cf : first.host.gas.Credits (4*op+rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have hm2 : (paid s op 2).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have mm2 : (paid s op 2).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have hm5 : (paid first op 2).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore,first,storeI32] using hm
  have mm5 : (paid first op 2).mems[index]?=some written := by simpa only [paid,chargedStore] using mm
  have cs : second.host.gas.Credits (op+rest) := paid_credits first op 3 _ (cf.mono (by omega))
  have next : WP cfg fuel (.next (atCode (chargedStore second op) limits (base++[]).toArray caller callers caller.code)) rest post := by
    simpa only [recordStore,first,second,written,paid,op,List.append_nil] using hnext
  have ret := ValueReturnLazyLookup.wp_return_wasm cfg fuel rest second limits base [] frame caller callers code post
    ha.symm hh cs next
  have tail : WP cfg (fuel+1) (.next (atCode second limits base.toArray frame (caller::callers) (.return::code))) (op+rest) post := by
    simpa only [List.append_nil] using ret
  unfold WNear.Binary.AllocateGrowth.recordReturn
  simp only [List.cons_append,List.nil_append]
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ s limits base.toArray frame (caller::callers) _ 0 (.i32 record) post h0
  · exact paid_credits s op 0 _ (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ (paid s op 1) limits _ frame (caller::callers) _ 2 (.i32 header) post h2
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_store cfg (fuel+4) _ (paid s op 2) limits base.toArray frame (caller::callers) _ {align:=2,offset:=4} record header mi index memory post hm2 hi mm2 (by omega)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ first limits base.toArray frame (caller::callers) _ 0 (.i32 record) post h0
  · exact paid_credits first op 0 _ (cf.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+2) _ (paid first op 1) limits _ frame (caller::callers) _ 3 (.i32 0) post h3
  · exact paid_credits first op 1 _ (cf.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(1*op+rest) by dsimp [op]; omega]
  apply wp_i32_store cfg (fuel+1) _ (paid first op 2) limits base.toArray frame (caller::callers) _ {align:=2,offset:=0} record 0 mi index written post hm5 hi mm5 (by change record.toNat+0+4≤written.byteSize; dsimp only [written]; rw [spec.2.1]; omega)
  · exact paid_credits first op 2 _ (cf.mono (by dsimp [op]; omega))
  simpa only [second,paid,Nat.one_mul,Nat.add_zero,op] using tail
end
end WNear.Proofs.AllocateGrowth
