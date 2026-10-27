import Binary.DeallocateList
import Proofs.DeallocateMaskStore

/-! Exact sequential low-bit clearing at the end of the deployed unlink helper. -/
namespace WNear.Proofs.DeallocateListClear
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def highMemory (memory : Memory) (pointer raw : UInt32) :=
  writeI32 memory (pointer.toNat + 4) (raw &&& 3)
def clearMemory (memory : Memory) (pointer raw : UInt32) :=
  writeI32 (highMemory memory pointer raw) pointer.toNat (readI32 (highMemory memory pointer raw) pointer.toNat &&& 3)
def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (pointer raw : UInt32) :=
  storeI32 (paid s op 5) index (pointer.toNat + 4) memory (raw &&& 3)
def clearStore (s : Store NearState) (op index : Nat) (memory : Memory) (pointer raw : UInt32) :=
  storeI32 (paid (highStore s op index memory pointer raw) op 6) index pointer.toNat
    (highMemory memory pointer raw) (readI32 (highMemory memory pointer raw) pointer.toNat &&& 3)

/-- The real five-instruction high-word write. -/
theorem wp_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer raw : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer)) (hr : frame.locals[1]? = some (.i32 raw))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index memory pointer raw)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 1, .i32_const 3, .i32_binop .and, .store .i32 none {align := 2, offset := 4}] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have mem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have next : WP cfg fuel (.next (atCode
      (DeallocateMaskStore.maskStore (paid s cfg.regularOpCost 2) cfg.regularOpCost index memory pointer raw 3 4)
      limits stack frame callers code)) rest post := by
    simpa only [DeallocateMaskStore.maskStore, highStore, ValueReturnBorrow.paid_add] using hnext
  have mask := DeallocateMaskStore.wp_mask_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    pointer raw 3 4 mi index memory post hm2 hi mem2 (by omega)
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) next
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ 0 (.i32 pointer) post hp (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  have get := wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits
    (stack.push (.i32 pointer)) frame callers _ 1 (.i32 raw) post hr
    (paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))) mask
  simpa only [paid, List.append_eq, List.cons_append, List.nil_append] using get

def lowStore (s : Store NearState) (op index : Nat) (memory : Memory) (pointer : UInt32) :=
  storeI32 (paid s op 6) index pointer.toNat memory (readI32 memory pointer.toNat &&& 3)

/-- The second load reads the memory after the high-word write. -/
theorem wp_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (lowStore s cfg.regularOpCost index memory pointer)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 3,
        .i32_binop .and, .store .i32 none {align := 2, offset := 0}] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have mem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have mem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have next : WP cfg fuel (.next (atCode
      (DeallocateMaskStore.maskStore (paid s cfg.regularOpCost 3) cfg.regularOpCost index memory pointer (readI32 memory pointer.toNat) 3 0)
      limits stack frame callers code)) rest post := by
    simpa only [DeallocateMaskStore.maskStore, lowStore, ValueReturnBorrow.paid_add, Nat.add_zero] using hnext
  have mask := DeallocateMaskStore.wp_mask_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    pointer (readI32 memory pointer.toNat) 3 0 mi index memory post hm3 hi mem3 (by omega)
    (paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))) next
  have loadNext : WP cfg (fuel + 3) (.next (atCode (paid s cfg.regularOpCost 3) limits
      ((stack.push (.i32 pointer)).push (.i32 (readI32 memory (pointer.toNat + 0)))) frame callers
      ([.i32_const 3, .i32_binop .and, .store .i32 none {align := 2, offset := 0}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by simpa only [Nat.add_zero] using mask
  have load := wp_i32_load cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits
    (stack.push (.i32 pointer)) frame callers _ {align := 2, offset := 0} pointer mi index memory post hm2 hi mem2
    (by simpa using hb) (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) loadNext
  rw [show cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 4 * cfg.regularOpCost + rest by omega] at load
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack frame callers _ 0 (.i32 pointer) post hp (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  have get := wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits
    (stack.push (.i32 pointer)) frame callers _ 0 (.i32 pointer) post hp
    (paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))) load
  simpa only [paid, List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 4 * cfg.regularOpCost + rest by omega] using get

/-- Native result words and footprint of the actual two sequential stores. -/
theorem clear_spec (memory : Memory) (pointer raw : UInt32)
    (hw : memory.wf) (hb : pointer.toNat + 8 ≤ memory.byteSize) :
    (clearMemory memory pointer raw).wf ∧
    (clearMemory memory pointer raw).byteSize = memory.byteSize ∧
    (clearMemory memory pointer raw).max = memory.max ∧
    readI32 (clearMemory memory pointer raw) pointer.toNat = (readI32 memory pointer.toNat &&& 3) ∧
    readI32 (clearMemory memory pointer raw) (pointer.toNat + 4) = (raw &&& 3) ∧
    ∀ j, (j < pointer.toNat ∨ pointer.toNat + 8 ≤ j) →
      (clearMemory memory pointer raw).read8 j = memory.read8 j := by
  have b1 : pointer.toNat + 4 + 4 ≤ memory.byteSize := by omega
  have first := writeI32_spec memory (pointer.toNat + 4) (raw &&& 3) hw b1
  have b2 : pointer.toNat + 4 ≤ (highMemory memory pointer raw).byteSize := by
    rw [show (highMemory memory pointer raw).byteSize = memory.byteSize from first.2.1]; omega
  have second := writeI32_spec (highMemory memory pointer raw) pointer.toNat
    (readI32 (highMemory memory pointer raw) pointer.toNat &&& 3) first.1 b2
  have firstLow := PanicAllocateReadback.read_write_frame memory pointer.toNat (pointer.toNat + 4) (raw &&& 3) hw b1 (by omega)
  have outLow := PanicAllocateReadback.read_write_self (highMemory memory pointer raw) pointer.toNat
    (readI32 (highMemory memory pointer raw) pointer.toNat &&& 3) first.1 b2
  have firstHigh := PanicAllocateReadback.read_write_self memory (pointer.toNat + 4) (raw &&& 3) hw b1
  have outHigh := PanicAllocateReadback.read_write_frame (highMemory memory pointer raw) (pointer.toNat + 4) pointer.toNat
    (readI32 (highMemory memory pointer raw) pointer.toNat &&& 3) first.1 b2 (by omega)
  refine ⟨second.1, second.2.1.trans first.2.1, second.2.2.1.trans first.2.2.1, ?_, ?_, ?_⟩
  · change readI32 (writeI32 (highMemory memory pointer raw) pointer.toNat _) pointer.toNat = _
    rw [outLow]
    change (readI32 (writeI32 memory (pointer.toNat + 4) (raw &&& 3)) pointer.toNat &&& 3) = _
    rw [firstLow]
  · exact outHigh.trans firstHigh
  · intro j hj
    change (writeI32 (highMemory memory pointer raw) pointer.toNat _).read8 j = memory.read8 j
    rw [second.2.2.2, ite_eq_right (show ¬(pointer.toNat ≤ j ∧ j < pointer.toNat + 4) by omega)]
    change (writeI32 memory (pointer.toNat + 4) _).read8 j = memory.read8 j
    rw [first.2.2.2, ite_eq_right (show ¬(pointer.toNat + 4 ≤ j ∧ j < pointer.toNat + 4 + 4) by omega)]

theorem highStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (pointer raw : UInt32)
    (hm : s.mems[index]? = some memory) :
    (highStore s op index memory pointer raw).mems[index]? = some (highMemory memory pointer raw) := by
  have initial : (paid s op 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hm
  exact storeI32_memory (paid s op 5) index (pointer.toNat + 4) memory (raw &&& 3) initial

theorem clearStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (pointer raw : UInt32)
    (hm : s.mems[index]? = some memory) :
    (clearStore s op index memory pointer raw).mems[index]? = some (clearMemory memory pointer raw) := by
  have initial : (paid (highStore s op index memory pointer raw) op 6).mems[index]? = some (highMemory memory pointer raw) := by
    simpa only [paid, chargedStore] using highStore_memory s op index memory pointer raw hm
  exact storeI32_memory (paid (highStore s op index memory pointer raw) op 6) index pointer.toNat (highMemory memory pointer raw)
    (readI32 (highMemory memory pointer raw) pointer.toNat &&& 3) initial

/-- The complete real eleven-instruction unlink suffix. -/
theorem wp_clear (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer raw : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer)) (hr : frame.locals[1]? = some (.i32 raw))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hw : memory.wf) (hb : pointer.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (clearStore s cfg.regularOpCost index memory pointer raw)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 11) (.next (atCode s limits stack frame callers
      (WNear.Binary.DeallocateList.clear ++ code))) (11 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let first := highStore s op index memory pointer raw
  let middle := highMemory memory pointer raw
  let lowCode : Expr := [.local_get 0, .local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 3,
    .i32_binop .and, .store .i32 none {align := 2, offset := 0}]
  have spec := writeI32_spec memory (pointer.toNat + 4) (raw &&& 3) hw (by omega)
  have bound : pointer.toNat + 4 ≤ middle.byteSize := by rw [show middle.byteSize = memory.byteSize from spec.2.1]; omega
  have module : first.modules[frame.inst]? = some mi := by
    simpa only [first, highStore, storeI32_modules, paid, chargedStore] using hm
  have mem : first.mems[index]? = some middle := highStore_memory s op index memory pointer raw hmem
  have next : WP cfg fuel (.next (atCode (lowStore first op index middle pointer)
      limits stack frame callers code)) rest post := by simpa only [lowStore, clearStore, first, middle, op] using hnext
  have low := wp_low cfg fuel rest first limits stack frame callers code pointer mi index middle post hp module hi mem bound
    (by simpa only [first, highStore, storeI32_host] using paid_credits s op 5 (6 * op + rest) (hc.mono (by dsimp [op]; omega))) next
  have high := wp_high cfg (fuel + 6) (6 * op + rest) s limits stack frame callers (lowCode ++ code) pointer raw mi index memory post
    hp hr hm hi hmem hb (hc.mono (by dsimp [op]; omega)) low
  have ge : 5 * cfg.regularOpCost + (6 * op + rest) = 11 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [ge] at high
  simpa only [lowCode, WNear.Binary.DeallocateList.clear, List.append_eq, List.cons_append, List.nil_append,
    Nat.add_assoc, Nat.reduceAdd] using high

theorem clearStore_fields (s : Store NearState) (op index : Nat) (memory : Memory) (pointer raw : UInt32) :
    (clearStore s op index memory pointer raw).funcs = s.funcs ∧
    (clearStore s op index memory pointer raw).modules = s.modules ∧
    (clearStore s op index memory pointer raw).tables = s.tables ∧
    (clearStore s op index memory pointer raw).globals = s.globals := by
  simp only [clearStore, highStore, storeI32_funcs, storeI32_modules, storeI32_tables, storeI32_globals,
    paid, chargedStore, and_self]

theorem clearStore_host (s : Store NearState) (op index : Nat) (memory : Memory) (pointer raw : UInt32) :
    {(clearStore s op index memory pointer raw).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [clearStore, highStore, storeI32_host, paid, chargedStore, chargeHost]

theorem clearStore_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (pointer raw : UInt32)
    (hc : s.host.gas.Credits (11 * op + rest)) :
    (clearStore s op index memory pointer raw).host.gas.burnt = s.host.gas.burnt + 11 * op ∧
    (clearStore s op index memory pointer raw).host.gas.promises = s.host.gas.promises ∧
    (clearStore s op index memory pointer raw).host.gas.Credits rest := by
  have first := paid_gas s op 5 (6 * op + rest) (hc.mono (by omega))
  have firstCredits : (highStore s op index memory pointer raw).host.gas.Credits (6 * op + rest) := by
    simpa only [highStore, storeI32_host] using paid_credits s op 5 (6 * op + rest) (hc.mono (by omega))
  have second := paid_gas (highStore s op index memory pointer raw) op 6 rest firstCredits
  have secondCredits := paid_credits (highStore s op index memory pointer raw) op 6 rest firstCredits
  have secondBurnt : (clearStore s op index memory pointer raw).host.gas.burnt =
      (highStore s op index memory pointer raw).host.gas.burnt + 6 * op := by
    simpa only [clearStore, storeI32_host] using second.1
  have firstBurnt : (highStore s op index memory pointer raw).host.gas.burnt = s.host.gas.burnt + 5 * op := by
    simpa only [highStore, storeI32_host] using first.1
  refine ⟨?_, ?_, ?_⟩
  · rw [secondBurnt, firstBurnt]; omega
  · have h : (highStore s op index memory pointer raw).host.gas.promises = s.host.gas.promises := by
      simpa only [highStore, storeI32_host] using first.2
    simpa only [clearStore, storeI32_host] using second.2.trans h
  · simpa only [clearStore, storeI32_host] using secondCredits

theorem clearStore_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (pointer raw : UInt32)
    (hc : s.host.gas.Credits (11 * op + rest)) : (clearStore s op index memory pointer raw).host.gas.Credits rest :=
  (clearStore_gas s op index rest memory pointer raw hc).2.2

end WNear.Proofs.DeallocateListClear
