import Proofs.DeallocateListGuards

/-! Actual eleven-instruction low-flag-preserving link writes in f575. -/
namespace WNear.Proofs.DeallocateListWrite
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP readI32 writeI32

def merged (memory : Memory) (destination source : Nat) :=
  (readI32 memory destination &&& 3) ||| (readI32 memory source &&& 4294967292)
def writeStore (s : Store NearState) (op index destinationOffset sourceOffset : Nat)
    (destination source : UInt32) (memory : Memory) :=
  storeI32 (paid s op 11) index (destination.toNat + destinationOffset) memory
    (merged memory (destination.toNat + destinationOffset) (source.toNat + sourceOffset))

private theorem normalize_gas {cfg : WasmConfig} {fuel : Nat} {c : StepResult NearState} {post : Post}
    (n rest : Nat) (h : WP cfg fuel c (cfg.regularOpCost + (n * cfg.regularOpCost + rest)) post) :
    WP cfg fuel c ((n + 1) * cfg.regularOpCost + rest) post := by
  have he : (n + 1) * cfg.regularOpCost + rest = cfg.regularOpCost + (n * cfg.regularOpCost + rest) := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [he]; exact h

/-- Both original words are read before the single destination write. The
contract keeps arbitrary source/destination aliasing and original low flags. -/
theorem wp_write (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (destinationSlot sourceSlot destinationOffset sourceOffset : Nat)
    (destination source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hd : frame.locals[destinationSlot]? = some (.i32 destination)) (hs : frame.locals[sourceSlot]? = some (.i32 source))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hdb : destination.toNat + destinationOffset + 4 ≤ memory.byteSize)
    (hsb : source.toNat + sourceOffset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (writeStore s cfg.regularOpCost index destinationOffset sourceOffset destination source memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 11) (.next (atCode s limits stack frame callers
      ([.local_get destinationSlot, .local_get destinationSlot, .load .i32 none {align := 2, offset := destinationOffset},
        .i32_const 3, .i32_binop .and, .local_get sourceSlot, .load .i32 none {align := 2, offset := sourceOffset},
        .i32_const 4294967292, .i32_binop .and, .i32_binop .or,
        .store .i32 none {align := 2, offset := destinationOffset}] ++ code)))
      (11 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let a := readI32 memory (destination.toNat + destinationOffset)
  let b := readI32 memory (source.toNat + sourceOffset)
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm6 : (paid s op 6).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm10 : (paid s op 10).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem6 : (paid s op 6).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem10 : (paid s op 10).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  let storeCode := .store .i32 none {align := 2, offset := destinationOffset} :: code
  let orCode := .i32_binop .or :: storeCode
  let andCode := .i32_binop .and :: orCode
  let constantCode := .i32_const 4294967292 :: andCode
  let loadCode := .load .i32 none {align := 2, offset := sourceOffset} :: constantCode
  let getCode := .local_get sourceSlot :: loadCode
  let firstAndCode := .i32_binop .and :: getCode
  let firstConstCode := .i32_const 3 :: firstAndCode
  let firstLoadCode := .load .i32 none {align := 2, offset := destinationOffset} :: firstConstCode
  let secondGetCode := .local_get destinationSlot :: firstLoadCode
  have st := wp_i32_store cfg fuel rest (paid s op 10) limits stack frame callers code {align := 2, offset := destinationOffset}
    destination ((a &&& 3) ||| (b &&& 4294967292)) mi index memory post hm10 hi hmem10 hdb
    (paid_credits s op 10 _ (hc.mono (by dsimp [op]; omega))) hnext
  have st1 : WP cfg (fuel + 1) (.next (atCode (paid s op 10) limits
      ((stack.push (.i32 destination)).push (.i32 ((a &&& 3) ||| (b &&& 4294967292)))) frame callers storeCode))
      (1 * cfg.regularOpCost + rest) post := by simpa only [Nat.one_mul, storeCode] using st
  have r2 := wp_i32_or cfg (fuel + 1) (1 * cfg.regularOpCost + rest) (paid s op 9) limits (stack.push (.i32 destination)) frame callers
    storeCode (a &&& 3) (b &&& 4294967292) post (paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))) st1
  have p2 := normalize_gas 1 rest r2
  have r3 := wp_i32_and cfg (fuel + 2) (2 * cfg.regularOpCost + rest) (paid s op 8) limits
    ((stack.push (.i32 destination)).push (.i32 (a &&& 3))) frame callers orCode b 4294967292 post
    (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) p2
  have p3 := normalize_gas 2 rest r3
  have r4 := wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s op 7) limits
    (((stack.push (.i32 destination)).push (.i32 (a &&& 3))).push (.i32 b)) frame callers andCode 4294967292 post
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) p3
  have p4 := normalize_gas 3 rest r4
  have r5 := wp_i32_load cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s op 6) limits
    ((stack.push (.i32 destination)).push (.i32 (a &&& 3))) frame callers constantCode {align := 2, offset := sourceOffset}
    source mi index memory post hm6 hi hmem6 hsb (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) p4
  have p5 := normalize_gas 4 rest r5
  have r6 := wp_local_get cfg (fuel + 5) (5 * cfg.regularOpCost + rest) (paid s op 5) limits
    ((stack.push (.i32 destination)).push (.i32 (a &&& 3))) frame callers loadCode sourceSlot (.i32 source) post hs
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) p5
  have p6 := normalize_gas 5 rest r6
  have r7 := wp_i32_and cfg (fuel + 6) (6 * cfg.regularOpCost + rest) (paid s op 4) limits (stack.push (.i32 destination)) frame callers
    getCode a 3 post (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) p6
  have p7 := normalize_gas 6 rest r7
  have r8 := wp_i32_const cfg (fuel + 7) (7 * cfg.regularOpCost + rest) (paid s op 3) limits
    ((stack.push (.i32 destination)).push (.i32 a)) frame callers firstAndCode 3 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) p7
  have p8 := normalize_gas 7 rest r8
  have r9 := wp_i32_load cfg (fuel + 8) (8 * cfg.regularOpCost + rest) (paid s op 2) limits (stack.push (.i32 destination)) frame callers
    firstConstCode {align := 2, offset := destinationOffset} destination mi index memory post hm2 hi hmem2 hdb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) p8
  have p9 := normalize_gas 8 rest r9
  have r10 := wp_local_get cfg (fuel + 9) (9 * cfg.regularOpCost + rest) (paid s op 1) limits (stack.push (.i32 destination)) frame callers
    firstLoadCode destinationSlot (.i32 destination) post hd (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) p9
  have p10 := normalize_gas 9 rest r10
  have r11 := wp_local_get cfg (fuel + 10) (10 * cfg.regularOpCost + rest) s limits stack frame callers secondGetCode destinationSlot (.i32 destination)
    post hd (hc.mono (by omega)) p10
  have p11 := normalize_gas 10 rest r11
  simpa only [secondGetCode, firstLoadCode, firstConstCode, firstAndCode, getCode, loadCode, constantCode, andCode, orCode, storeCode,
    List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using p11

end WNear.Proofs.DeallocateListWrite
