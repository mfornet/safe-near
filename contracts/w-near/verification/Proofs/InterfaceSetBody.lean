import Binary.InterfaceSet
import Proofs.ValueReturnOuter

/-! Small exact instruction capsules used by deployed f463. -/
namespace WNear.Proofs.InterfaceSetBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

def storeWord (s : Store NearState) (op index offset : Nat) (address value : UInt32) (memory : Memory) :=
  storeI32 (paid s op 3) index (address.toNat + offset) memory value

/-- The three actual local/local/store instructions retain the original
operand prefix, caller stack and local frame. -/
theorem wp_store_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (addressSlot valueSlot offset : Nat) (address value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ha : frame.locals[addressSlot]? = some (.i32 address)) (hv : frame.locals[valueSlot]? = some (.i32 value))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address.toNat + offset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (storeWord s cfg.regularOpCost index offset address value memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get addressSlot, .local_get valueSlot, .store .i32 none {align := 2, offset}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ addressSlot (.i32 address) post ha (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ valueSlot (.i32 value) post hv
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2, offset} address value mi index memory post hm2 hi hmem2 hb
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  · exact hnext

def twoWordsStore (s : Store NearState) (op index firstOffset secondOffset : Nat)
    (address first second : UInt32) (memory : Memory) :=
  storeWord (storeWord s op index firstOffset address first memory) op index secondOffset address second
    (writeI32 memory (address.toNat + firstOffset) first)

theorem wp_two_words (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (addressSlot firstSlot secondSlot firstOffset secondOffset : Nat)
    (address first second : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ha : frame.locals[addressSlot]? = some (.i32 address))
    (hfirst : frame.locals[firstSlot]? = some (.i32 first)) (hsecond : frame.locals[secondSlot]? = some (.i32 second))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb1 : address.toNat + firstOffset + 4 ≤ memory.byteSize)
    (hb2 : address.toNat + secondOffset + 4 ≤ (writeI32 memory (address.toNat + firstOffset) first).byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (twoWordsStore s cfg.regularOpCost index firstOffset secondOffset address first second memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get addressSlot, .local_get firstSlot, .store .i32 none {align := 2, offset := firstOffset},
        .local_get addressSlot, .local_get secondSlot, .store .i32 none {align := 2, offset := secondOffset}] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let written := storeWord s op index firstOffset address first memory
  have cm : written.host.gas.Credits (3 * op + rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have hm' : written.modules[frame.inst]? = some mi := by simpa only [written, storeWord, paid, chargedStore, storeI32_modules] using hm
  have hmem' : written.mems[index]? = some (writeI32 memory (address.toNat + firstOffset) first) :=
    storeI32_memory (paid s op 3) index (address.toNat + firstOffset) memory first hmem
  have secondRule := wp_store_word cfg fuel rest written limits stack frame callers code addressSlot secondSlot secondOffset address second mi index
    (writeI32 memory (address.toNat + firstOffset) first) post ha hsecond hm' hi hmem' hb2 cm hnext
  have firstNext : WP cfg (fuel + 3) (.next (atCode written limits stack frame callers
      ([.local_get addressSlot, .local_get secondSlot, .store .i32 none {align := 2, offset := secondOffset}] ++ code))) (3 * op + rest) post := secondRule
  have result := wp_store_word cfg (fuel + 3) (3 * op + rest) s limits stack frame callers _ addressSlot firstSlot firstOffset address first mi index memory post
    ha hfirst hm hi hmem hb1 (hc.mono (by dsimp [op]; omega)) firstNext
  have gas : 3 * cfg.regularOpCost + (3 * op + rest) = 6 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.cons_append, List.nil_append] using result

def copiedWord (s : Store NearState) (op index readOffset writeOffset : Nat) (address : UInt32) (memory : Memory) :=
  storeI32 (paid s op 4) index (address.toNat + writeOffset) memory (readI32 memory (address.toNat + readOffset))

theorem wp_copy_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot readOffset writeOffset : Nat) (address : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 address)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : address.toNat + readOffset + 4 ≤ memory.byteSize) (hw : address.toNat + writeOffset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copiedWord s cfg.regularOpCost index readOffset writeOffset address memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get slot, .local_get slot, .load .i32 none {align := 2, offset := readOffset},
        .store .i32 none {align := 2, offset := writeOffset}] ++ code))) (4 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ slot (.i32 address) post hl (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ slot (.i32 address) post hl
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := readOffset} address mi index memory post hm2 hi hmem2 hr
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 2, offset := writeOffset} address (readI32 memory (address.toNat + readOffset)) mi index memory post hm3 hi hmem3 hw
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  · exact hnext

def copiedTeeWord (s : Store NearState) (op index readOffset writeOffset : Nat) (address : UInt32) (memory : Memory) :=
  storeI32 (paid s op 5) index (address.toNat + writeOffset) memory (readI32 memory (address.toNat + readOffset))

theorem wp_copy_tee_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot teeSlot readOffset writeOffset : Nat) (address : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 address)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : address.toNat + readOffset + 4 ≤ memory.byteSize) (hw : address.toNat + writeOffset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copiedTeeWord s cfg.regularOpCost index readOffset writeOffset address memory)
      limits stack {frame with locals := frame.locals.set! teeSlot (.i32 (readI32 memory (address.toNat + readOffset)))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get slot, .local_get slot, .load .i32 none {align := 2, offset := readOffset}, .local_tee teeSlot,
        .store .i32 none {align := 2, offset := writeOffset}] ++ code))) (5 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ slot (.i32 address) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ slot (.i32 address) post hl
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := readOffset} address mi index memory post hm2 hi hmem2 hr
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ teeSlot (.i32 (readI32 memory (address.toNat + readOffset))) post
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 4) limits stack
    {frame with locals := frame.locals.set! teeSlot (.i32 (readI32 memory (address.toNat + readOffset)))} callers code
    {align := 2, offset := writeOffset} address (readI32 memory (address.toNat + readOffset)) mi index memory post hm4 hi hmem4 hw
  · apply paid_credits s cfg.regularOpCost 4; exact hc.mono (by omega)
  · exact hnext

theorem storeWord_credits (s : Store NearState) (op index offset rest : Nat)
    (address value : UInt32) (memory : Memory) (hc : s.host.gas.Credits (3 * op + rest)) :
    (storeWord s op index offset address value memory).host.gas.Credits rest := by
  unfold storeWord; rw [storeI32_host]
  exact paid_credits s op 3 rest hc

theorem twoWordsStore_credits (s : Store NearState) (op index firstOffset secondOffset rest : Nat)
    (address first second : UInt32) (memory : Memory) (hc : s.host.gas.Credits (6 * op + rest)) :
    (twoWordsStore s op index firstOffset secondOffset address first second memory).host.gas.Credits rest := by
  have c := storeWord_credits s op index firstOffset (3 * op + rest) address first memory (hc.mono (by omega))
  exact storeWord_credits _ op index secondOffset rest address second _ c

theorem copiedWord_credits (s : Store NearState) (op index readOffset writeOffset rest : Nat)
    (address : UInt32) (memory : Memory) (hc : s.host.gas.Credits (4 * op + rest)) :
    (copiedWord s op index readOffset writeOffset address memory).host.gas.Credits rest := by
  unfold copiedWord; rw [storeI32_host]
  exact paid_credits s op 4 rest hc

theorem copiedTeeWord_credits (s : Store NearState) (op index readOffset writeOffset rest : Nat)
    (address : UInt32) (memory : Memory) (hc : s.host.gas.Credits (5 * op + rest)) :
    (copiedTeeWord s op index readOffset writeOffset address memory).host.gas.Credits rest := by
  unfold copiedTeeWord; rw [storeI32_host]
  exact paid_credits s op 5 rest hc

theorem wp_set_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot : Nat) (post : Post)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack
      {frame with locals := frame.locals.set! slot (.i32 0)} callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers ([.i32_const 0, .local_set slot] ++ code)))
      (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  apply wp_local_set cfg fuel rest (paid s cfg.regularOpCost 1) limits stack frame callers code slot (.i32 0) post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  · exact hnext

theorem wp_offset_or (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot : Nat) (address offset mask : UInt32) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 address))
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (stack.push (.i32 ((address + offset) ||| mask))) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get slot, .i32_const offset, .i32_binop .add, .i32_const mask, .i32_binop .or] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ slot (.i32 address) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ offset post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ address offset post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ mask post
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  apply wp_i32_or cfg fuel rest (paid s cfg.regularOpCost 4) limits stack frame callers code (address + offset) mask post
  · apply paid_credits s cfg.regularOpCost 4; exact hc.mono (by omega)
  · exact hnext

theorem wp_acquire_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch cell : UInt32) (post : Post)
    (hs : frame.locals[3]? = some (.i32 scratch)) (hc0 : frame.locals[0]? = some (.i32 cell))
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (scratch + 8))).push (.i32 cell)).push (.i32 1055120)) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get 3, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 1055120] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ 3 (.i32 scratch) post hs (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 8 post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ scratch 8 post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 0 (.i32 cell) post hc0
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  apply wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 4) limits _ frame callers code 1055120 post
  · apply paid_credits s cfg.regularOpCost 4; exact hc.mono (by omega)
  · exact hnext

end WNear.Proofs.InterfaceSetBody
