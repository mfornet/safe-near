import Binary.AllocateSplit
import Proofs.AllocateCommit

/-! The actual first twelve heap-write instructions of f580's end split.
All writes are sequential; no disjointness is imposed on the operational rule. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
attribute [local irreducible] WP atCode readI32 writeI32 writeI64

def clearedMemory (memory : Memory) (header : UInt32) :=
  writeI64 (writeI32 memory (header.toNat+8) 0) header.toNat 0
def clearedStore (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :=
  storeI64 (paid (storeI32 (paid s op 3) index (header.toNat+8) memory 0) op 3)
    index header.toNat (writeI32 memory (header.toNat+8) 0) 0

theorem wp_clear_header (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[9]? = some (.i32 header)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hw : memory.wf) (hb : header.toNat+12 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (clearedStore s cfg.regularOpCost index memory header) limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      ([.local_get 9,.i32_const 0,.store .i32 none {align:=2,offset:=8},
        .local_get 9,.i64_const 0,.store .i64 none {align:=2,offset:=0}] ++ code))) (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first := storeI32 (paid s op 3) index (header.toNat+8) memory 0
  have spec := writeI32_spec memory (header.toNat+8) 0 hw (by omega)
  have hb' : header.toNat+0+8 ≤ (writeI32 memory (header.toNat+8) 0).byteSize := by rw [spec.2.1]; omega
  have hf : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have firstMem : first.mems[index]? = some (writeI32 memory (header.toNat+8) 0) := by
    apply storeI32_memory
    simpa only [paid,chargedStore] using hmem
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hm5 : (paid first op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore,first,storeI32_modules] using hm
  have hmem5 : (paid first op 2).mems[index]? = some (writeI32 memory (header.toNat+8) 0) := by simpa only [paid,chargedStore] using firstMem
  have cf : first.host.gas.Credits (3*op+rest) := by
    dsimp only [first]
    rw [storeI32_host]
    exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have lastNext : WP cfg fuel (.next (atCode (storeI64 (chargedStore (paid first op 2) op) index header.toNat
      (writeI32 memory (header.toNat+8) 0) 0) limits stack frame callers code)) rest post := by
    simpa only [clearedStore,first,paid,op] using hnext
  have last := wp_i64_store cfg fuel rest (paid first op 2) limits stack frame callers code {align:=2,offset:=0}
    header 0 mi index (writeI32 memory (header.toNat+8) 0) post hm5 hi hmem5 hb'
    (paid_credits first op 2 _ (cf.mono (by dsimp [op]; omega))) lastNext
  have secondConst := wp_i64_const cfg (fuel+1) (op+rest) (paid first op 1) limits (stack.push (.i32 header)) frame callers _ 0 post
    (paid_credits first op 1 _ (cf.mono (by dsimp [op]; omega))) last
  have second : WP cfg (fuel+3) (.next (atCode first limits stack frame callers
      ([.local_get 9,.i64_const 0,.store .i64 none {align:=2,offset:=0}]++code))) (3*op+rest) post := by
    have result := wp_local_get cfg (fuel+2) (op+(op+rest)) first limits stack frame callers _ 9 (.i32 header) post hl
      (cf.mono (by dsimp [op]; omega)) secondConst
    have cost : cfg.regularOpCost+(op+(op+rest))=3*op+rest := by dsimp [op]; omega
    rw [cost] at result
    simpa only [Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append] using result
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ s limits stack frame callers _ 9 (.i32 header) post hl (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+4) _ (paid s op 1) limits _ frame callers _ 0 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_store cfg (fuel+3) (3*op+rest) (paid s op 2) limits stack frame callers _ {align:=2,offset:=8}
    header 0 mi index memory post hm2 hi hf (by omega)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  · exact second

def copiedEndStore (s : Store NearState) (op index : Nat) (memory : Memory) (head header : UInt32) :=
  storeI32 (paid s op 6) index header.toNat memory (readI32 memory head.toNat &&& 4294967292)

/-- The copied end word is read after the preceding writes, as in the binary. -/
theorem wp_copy_end (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[9]? = some (.i32 header)) (hh : frame.locals[1]? = some (.i32 head))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hr : head.toNat+4 ≤ memory.byteSize) (hw : header.toNat+4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copiedEndStore s cfg.regularOpCost index memory head header)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      ([.local_get 9,.local_get 1,.load .i32 none {align:=2,offset:=0},.i32_const 4294967292,
        .i32_binop .and,.store .i32 none {align:=2,offset:=0}]++code))) (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hm5 : (paid s op 5).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hmem5 : (paid s op 5).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ s limits stack frame callers _ 9 (.i32 header) post hl (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s op 1) limits _ frame callers _ 1 (.i32 head) post hh
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+3) _ (paid s op 2) limits (stack.push (.i32 header)) frame callers _
    {align:=2,offset:=0} head mi index memory post hm2 hi hmem2 (by simpa using hr)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 3) limits _ frame callers _ 4294967292 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+1) _ (paid s op 4) limits (stack.push (.i32 header)) frame callers _ (readI32 memory head.toNat) 4294967292 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 5) limits stack frame callers code {align:=2,offset:=0}
    header (readI32 memory head.toNat &&& 4294967292) mi index memory post hm5 hi hmem5 (by simpa using hw)
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

theorem clearedMemory_spec (memory : Memory) (header : UInt32) (hw : memory.wf)
    (hb : header.toNat+12 ≤ memory.byteSize) :
    (clearedMemory memory header).wf ∧
    (clearedMemory memory header).byteSize = memory.byteSize ∧
    (clearedMemory memory header).max = memory.max ∧
    ∀ j, (j < header.toNat ∨ header.toNat+12 ≤ j) →
      (clearedMemory memory header).read8 j = memory.read8 j := by
  have first := writeI32_spec memory (header.toNat+8) 0 hw (by omega)
  have bound : header.toNat+8 ≤ (writeI32 memory (header.toNat+8) 0).byteSize := by rw [first.2.1]; omega
  have second := writeI64_spec (writeI32 memory (header.toNat+8) 0) header.toNat 0 first.1 bound
  refine ⟨second.1,second.2.1.trans first.2.1,second.2.2.1.trans first.2.2.1,?_⟩
  intro j hj
  change (writeI64 _ _ _).read8 _ = _
  rw [second.2.2.2]
  have noSecond : ¬(header.toNat ≤ j ∧ j < header.toNat+8) := by omega
  rw [ite_eq_right noSecond,first.2.2.2]
  have noFirst : ¬(header.toNat+8 ≤ j ∧ j < header.toNat+8+4) := by omega
  rw [ite_eq_right noFirst]

theorem clearedStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32)
    (hm : s.mems[index]? = some memory) :
    (clearedStore s op index memory header).mems[index]? = some (clearedMemory memory header) := by
  have hm3 : (paid s op 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using hm
  have first := storeI32_memory (paid s op 3) index (header.toNat+8) memory 0 hm3
  have first' : (paid (storeI32 (paid s op 3) index (header.toNat+8) memory 0) op 3).mems[index]? =
      some (writeI32 memory (header.toNat+8) 0) := by simpa only [paid,chargedStore] using first
  exact storeI64_memory _ index header.toNat _ 0 first'

theorem clearedStore_resources (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    {clearedStore s op index memory header with host := s.host,mems := s.mems} = s := by cases s; rfl

theorem clearedStore_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (header : UInt32)
    (hc : s.host.gas.Credits (6*op+rest)) : (clearedStore s op index memory header).host.gas.Credits rest := by
  have first := paid_credits s op 3 (3*op+rest) (hc.mono (by omega))
  unfold clearedStore
  rw [storeI64_host]
  have cf : (storeI32 (paid s op 3) index (header.toNat+8) memory 0).host.gas.Credits (3*op+rest) := first
  exact paid_credits _ op 3 rest cf

def initializedStore (s : Store NearState) (op index : Nat) (memory : Memory) (head header : UInt32) :=
  copiedEndStore (clearedStore s op index memory header) op index (clearedMemory memory header) head header

/-- All twelve actual initialization instructions, including the sequential
read of the original block end after clearing the new header. -/
theorem wp_initialize_split (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[9]? = some (.i32 header)) (hh : frame.locals[1]? = some (.i32 head))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hw : memory.wf)
    (hr : head.toNat+4 ≤ memory.byteSize) (hb : header.toNat+12 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (initializedStore s cfg.regularOpCost index memory head header)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits stack frame callers (WNear.Binary.Allocate.initializeSplit++code)))
      (12*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have spec := clearedMemory_spec memory header hw hb
  have resource := congrArg (fun t=>t.modules) (clearedStore_resources s op index memory header)
  simp only at resource
  have hm' : (clearedStore s op index memory header).modules[frame.inst]? = some mi := by rw [resource]; exact hm
  have hmem' := clearedStore_memory s op index memory header hmem
  have hr' : head.toNat+4 ≤ (clearedMemory memory header).byteSize := by rw [spec.2.1]; exact hr
  have hb' : header.toNat+4 ≤ (clearedMemory memory header).byteSize := by rw [spec.2.1]; omega
  have cc := clearedStore_credits s op index (6*op+rest) memory header (hc.mono (by dsimp [op]; omega))
  have tail := wp_copy_end cfg fuel rest (clearedStore s op index memory header) limits stack frame callers code
    head header mi index (clearedMemory memory header) post hl hh hm' hi hmem' hr' hb' cc hnext
  have result := wp_clear_header cfg (fuel+6) (6*op+rest) s limits stack frame callers
    ([.local_get 9,.local_get 1,.load .i32 none {align:=2,offset:=0},.i32_const 4294967292,
      .i32_binop .and,.store .i32 none {align:=2,offset:=0}]++code)
    header mi index memory post hl hm hi hmem hw hb (hc.mono (by dsimp [op]; omega)) tail
  have cost : 6*cfg.regularOpCost+(6*op+rest)=12*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [WNear.Binary.Allocate.initializeSplit,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append] using result
end WNear.Proofs.Allocate
