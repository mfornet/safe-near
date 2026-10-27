import Proofs.StateDispatchBorrow
import Proofs.ValueReturnDispatch

/-! Actual read-register receiver, register, destination and vtable loads. -/
namespace WNear.Proofs.StateDispatchReadArguments
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 ValueReturnDispatch.packed32
set_option maxRecDepth 16384

def register (memory : Memory) (input : UInt32) := readI64 memory input.toNat
def pointer (memory : Memory) (input : UInt32) := ValueReturnDispatch.packed32 memory input.toNat
def element (memory : Memory) (cell : UInt32) := readI32 memory ((readI32 memory (cell.toNat + 4)).toNat + 12)
def finalFrame (frame : CallFrame) (cell : UInt32) := {frame with locals := frame.locals.set! 4 (.i32 cell)}
def code : Expr := [.local_tee 4,.load .i32 none {align := 2,offset := 0},
  .local_get 1,.load .i64 none {align := 3,offset := 0},
  .local_get 2,.load .i64 (some ⟨32,false⟩) {align := 2,offset := 0},
  .local_get 4,.load .i32 none {align := 2,offset := 4},.load .i32 none {align := 2,offset := 12}]

theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : Expr) (cell registerInput pointerInput : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hreg : frame.locals[1]? = some (.i32 registerInput)) (hptr : frame.locals[2]? = some (.i32 pointerInput))
    (hn : 4 < frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hcell : cell.toNat + 8 ≤ memory.byteSize)
    (hrb : registerInput.toNat + 8 ≤ memory.byteSize) (hpb : pointerInput.toNat + 4 ≤ memory.byteSize)
    (hvtable : (readI32 memory (cell.toNat + 4)).toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      ((base ++ [Value.i32 (readI32 memory cell.toNat),.i64 (register memory registerInput),.i64 (pointer memory pointerInput)]).toArray.push
        (.i32 (element memory cell))) (finalFrame frame cell) callers suffix)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers (code ++ suffix)))
      (9 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := finalFrame frame cell
  let a := base.toArray.push (.i32 (readI32 memory cell.toNat))
  let b := a.push (.i64 (register memory registerInput))
  let c := b.push (.i64 (pointer memory pointerInput))
  have hc0 : cell.toNat + 0 + 4 ≤ memory.byteSize := by omega
  have hc4 : cell.toNat + 4 + 4 ≤ memory.byteSize := by omega
  have hr0 : registerInput.toNat + 0 + 8 ≤ memory.byteSize := by omega
  have hp0 : pointerInput.toNat + 0 + 4 ≤ memory.byteSize := by omega
  have hv : (readI32 memory (cell.toNat + 4)).toNat + 12 + 4 ≤ memory.byteSize := by omega
  have hr' : f.locals[1]? = some (.i32 registerInput) := by simpa [f,finalFrame] using hreg
  have hd' : f.locals[2]? = some (.i32 pointerInput) := by simpa [f,finalFrame] using hptr
  have hp : f.locals[4]? = some (.i32 cell) := by simp [f,finalFrame,hn]
  have hm' (n : Nat) : (paid s op n).modules[f.inst]? = some mi := by
    have h := congrArg (fun t : Store NearState => t.modules[frame.inst]?) (StorePairCaller.paid_resources s op n)
    exact h.trans hm
  have mem' (n : Nat) : (paid s op n).mems[index]? = some memory := by
    have h := congrArg (fun t : Store NearState => t.mems[index]?) (StorePairCaller.paid_resources s op n)
    exact h.trans hmem
  have stackEq : (base ++ [Value.i32 (readI32 memory cell.toNat),.i64 (register memory registerInput),.i64 (pointer memory pointerInput)]).toArray = c := by
    apply Array.toList_inj.mp; simp [c,b,a]
  have next : WP cfg fuel (.next (atCode (paid s op 9) limits (c.push (.i32 (element memory cell))) f callers suffix)) rest post := by
    simpa only [op,f,stackEq] using hnext
  have step8 := wp_i32_load cfg (fuel + 0) rest (paid s op 8) limits c f callers suffix
    {align := 2,offset := 12} (readI32 memory (cell.toNat + 4)) mi index memory post (hm' 8) hi (mem' 8) hv (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) next
  have step7 := wp_i32_load cfg (fuel + 1) (op + rest) (paid s op 7) limits c f callers (.load .i32 none {align := 2,offset := 12} :: suffix)
    {align := 2,offset := 4} cell mi index memory post (hm' 7) hi (mem' 7) hc4 (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) step8
  have step6 := wp_local_get cfg (fuel + 2) (op + (op + rest)) (paid s op 6) limits c f callers (.load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    4 (.i32 cell) post hp (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) step7
  have step5 := ValueReturnDispatch.wp_load32_u cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 5) limits b f callers (.local_get 4 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    {align := 2,offset := 0} pointerInput mi index memory post (hm' 5) hi (mem' 5) hp0 (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) step6
  have step4 := wp_local_get cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 4) limits b f callers (.load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .local_get 4 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    2 (.i32 pointerInput) post hd' (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) step5
  have step3 := wp_i64_load cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 3) limits a f callers (.local_get 2 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .local_get 4 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    {align := 3,offset := 0} registerInput mi index memory post (hm' 3) hi (mem' 3) hr0 (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) step4
  have step2 := wp_local_get cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) (paid s op 2) limits a f callers (.load .i64 none {align := 3,offset := 0} :: .local_get 2 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .local_get 4 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    1 (.i32 registerInput) post hr' (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) step3
  have step1 := wp_i32_load cfg (fuel + 7) (op + (op + (op + (op + (op + (op + (op + rest))))))) (paid s op 1) limits base.toArray f callers (.local_get 1 :: .load .i64 none {align := 3,offset := 0} :: .local_get 2 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .local_get 4 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    {align := 2,offset := 0} cell mi index memory post (hm' 1) hi (mem' 1) hc0 (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) step2
  have step0 := wp_local_tee cfg (fuel + 8) (op + (op + (op + (op + (op + (op + (op + (op + rest)))))))) s limits base.toArray frame callers (.load .i32 none {align := 2,offset := 0} :: .local_get 1 :: .load .i64 none {align := 3,offset := 0} :: .local_get 2 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .local_get 4 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 12} :: suffix)
    4 (.i32 cell) post (hc.mono (by dsimp [op]; omega)) step1
  simpa only [code,List.cons_append,List.nil_append,Nat.add_zero,
    show cfg.regularOpCost + (op + (op + (op + (op + (op + (op + (op + (op + rest)))))))) = 9 * cfg.regularOpCost + rest by dsimp [op]; omega] using step0

end WNear.Proofs.StateDispatchReadArguments
