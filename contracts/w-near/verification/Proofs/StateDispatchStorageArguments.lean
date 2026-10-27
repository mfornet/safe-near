import Proofs.StateDispatchBorrow
import Proofs.ValueReturnDispatch

/-! Actual ten-op storage-read argument preparation from current memory. -/
namespace WNear.Proofs.StateDispatchStorageArguments
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 ValueReturnDispatch.packed32
set_option maxRecDepth 16384

def keyLen (memory : Memory) (input : UInt32) := ValueReturnDispatch.packed32 memory (input.toNat + 4)
def keyPtr (memory : Memory) (input : UInt32) := ValueReturnDispatch.packed32 memory input.toNat
def element (memory : Memory) (cell : UInt32) := readI32 memory ((readI32 memory (cell.toNat + 4)).toNat + 188)
def finalFrame (frame : CallFrame) (cell : UInt32) := {frame with locals := frame.locals.set! 0 (.i32 cell)}
def code : Expr := [.local_tee 0,.load .i32 none {align := 2,offset := 0},
  .local_get 1,.load .i64 (some ⟨32,false⟩) {align := 2,offset := 4},
  .local_get 1,.load .i64 (some ⟨32,false⟩) {align := 2,offset := 0},.i64_const 0,
  .local_get 0,.load .i32 none {align := 2,offset := 4},.load .i32 none {align := 2,offset := 188}]

theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : Expr) (cell input : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[1]? = some (.i32 input)) (hn : 0 < frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hcell : cell.toNat + 8 ≤ memory.byteSize) (hinput : input.toNat + 8 ≤ memory.byteSize)
    (hvtable : (readI32 memory (cell.toNat + 4)).toNat + 192 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (10 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 10) limits
      ((base ++ [Value.i32 (readI32 memory cell.toNat),.i64 (keyLen memory input),.i64 (keyPtr memory input),.i64 0]).toArray.push
        (.i32 (element memory cell))) (finalFrame frame cell) callers suffix)) rest post) :
    WP cfg (fuel + 10) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers (code ++ suffix)))
      (10 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := finalFrame frame cell
  let a := base.toArray.push (.i32 (readI32 memory cell.toNat))
  let b := a.push (.i64 (keyLen memory input))
  let c := b.push (.i64 (keyPtr memory input))
  let d := c.push (.i64 0)
  have hc0 : cell.toNat + 0 + 4 ≤ memory.byteSize := by omega
  have hc4 : cell.toNat + 4 + 4 ≤ memory.byteSize := by omega
  have hi4 : input.toNat + 4 + 4 ≤ memory.byteSize := by omega
  have hi0 : input.toNat + 0 + 4 ≤ memory.byteSize := by omega
  have hv : (readI32 memory (cell.toNat + 4)).toNat + 188 + 4 ≤ memory.byteSize := by omega
  have hs' : f.locals[1]? = some (.i32 input) := by simpa [f,finalFrame] using hs
  have hp : f.locals[0]? = some (.i32 cell) := by simp [f,finalFrame,hn]
  have hm' (n : Nat) : (paid s op n).modules[f.inst]? = some mi := by
    have h := congrArg (fun t : Store NearState => t.modules[frame.inst]?) (StorePairCaller.paid_resources s op n)
    exact h.trans hm
  have mem' (n : Nat) : (paid s op n).mems[index]? = some memory := by
    have h := congrArg (fun t : Store NearState => t.mems[index]?) (StorePairCaller.paid_resources s op n)
    exact h.trans hmem
  have stackEq : (base ++ [Value.i32 (readI32 memory cell.toNat),.i64 (keyLen memory input),.i64 (keyPtr memory input),.i64 0]).toArray = d := by
    apply Array.toList_inj.mp; simp [d,c,b,a]
  have next : WP cfg fuel (.next (atCode (paid s op 10) limits (d.push (.i32 (element memory cell))) f callers suffix)) rest post := by
    simpa only [op,f,stackEq] using hnext
  have last := wp_i32_load cfg fuel rest (paid s op 9) limits d f callers suffix
    {align := 2,offset := 188} (readI32 memory (cell.toNat + 4)) mi index memory post (hm' 9) hi (mem' 9) hv
    (paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))) next
  have prev := wp_i32_load cfg (fuel + 1) (op + rest) (paid s op 8) limits d f callers
    (.load .i32 none {align := 2,offset := 188} :: suffix) {align := 2,offset := 4} cell mi index memory post
    (hm' 8) hi (mem' 8) hc4 (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) last
  have get0 := wp_local_get cfg (fuel + 2) (op + (op + rest)) (paid s op 7) limits d f callers
    (.load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix) 0 (.i32 cell) post hp
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) prev
  have zero := wp_i64_const cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 6) limits c f callers
    (.local_get 0 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix) 0 post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) get0
  have ptr := ValueReturnDispatch.wp_load32_u cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 5) limits b f callers
    (.i64_const 0 :: .local_get 0 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix)
    {align := 2,offset := 0} input mi index memory post (hm' 5) hi (mem' 5) hi0
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) zero
  have getPtr := wp_local_get cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 4) limits b f callers
    (.load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .i64_const 0 :: .local_get 0 ::
      .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix) 1 (.i32 input) post hs'
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) ptr
  have len := ValueReturnDispatch.wp_load32_u cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) (paid s op 3) limits a f callers
    (.local_get 1 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .i64_const 0 :: .local_get 0 ::
      .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix)
    {align := 2,offset := 4} input mi index memory post (hm' 3) hi (mem' 3) hi4
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) getPtr
  have getLen := wp_local_get cfg (fuel + 7) (op + (op + (op + (op + (op + (op + (op + rest))))))) (paid s op 2) limits a f callers
    (.load .i64 (some ⟨32,false⟩) {align := 2,offset := 4} :: .local_get 1 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} ::
      .i64_const 0 :: .local_get 0 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix)
    1 (.i32 input) post hs' (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) len
  have receiver := wp_i32_load cfg (fuel + 8) (op + (op + (op + (op + (op + (op + (op + (op + rest)))))))) (paid s op 1) limits base.toArray f callers
    (.local_get 1 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 4} :: .local_get 1 ::
      .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .i64_const 0 :: .local_get 0 ::
      .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix)
    {align := 2,offset := 0} cell mi index memory post (hm' 1) hi (mem' 1) hc0
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) getLen
  have first := wp_local_tee cfg (fuel + 9) (op + (op + (op + (op + (op + (op + (op + (op + (op + rest))))))))) s limits base.toArray frame callers
    (.load .i32 none {align := 2,offset := 0} :: .local_get 1 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 4} ::
      .local_get 1 :: .load .i64 (some ⟨32,false⟩) {align := 2,offset := 0} :: .i64_const 0 :: .local_get 0 ::
      .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 188} :: suffix) 0 (.i32 cell) post
    (hc.mono (by dsimp [op]; omega)) receiver
  simpa only [code,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (op + (op + (op + (op + (op + (op + (op + (op + rest))))))))) = 10 * cfg.regularOpCost + rest by dsimp [op]; omega] using first

end WNear.Proofs.StateDispatchStorageArguments
