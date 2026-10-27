import Proofs.ZeroFillIteration

/-! Symbolic induction over the actual f952 loop and its paid backedges. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode iterationStore written
set_option maxRecDepth 16384

def loopCost (n : Nat) := if n=0 then 0 else 13*n-1

def loopAfter (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value count : UInt32) : Nat → Store NearState
  | 0 => s
  | n+1 => loopAfter (chargedStore (iterationStore s op index memory ptr value) (if n=0 then op else 2*op)) op index
      (writeByte memory ptr.toNat value) (ptr+1) value (nextCount count) n

def loopFrameAfter (frame : CallFrame) (ptr count : UInt32) : Nat → CallFrame
  | 0 => frame
  | n+1 => loopFrameAfter (iterationFrame frame ptr count) (ptr+1) (nextCount count) n

theorem nextCount_toNat (count : UInt32) (h : 0<count.toNat) : (nextCount count).toNat=count.toNat-1 := by
  have lt := count.toNat_lt
  simp only [nextCount,UInt32.toNat_add,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem loopCost_succ (n : Nat) : loopCost (n+1)=11+(if n=0 then 1 else 2)+loopCost n := by
  cases n with
  | zero => rfl
  | succ n => simp [loopCost];omega

theorem iteration_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (ptr value : UInt32)
    (hc : s.host.gas.Credits (11*op+rest)) : (iterationStore s op index memory ptr value).host.gas.Credits rest := by
  have cut : 3*op+(8*op+rest)≤11*op+rest := by omega
  have cw : (written s op index memory ptr value).host.gas.Credits (8*op+rest) := by
    unfold written;rw [storeByte_host];exact paid_credits s op 3 _ (hc.mono cut)
  unfold iterationStore
  exact paid_credits _ op 8 rest cw

private theorem iteration_memory (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value : UInt32)
    (hm : s.mems[index]? = some  memory) :
    (iterationStore s op index memory ptr value).mems[index]? = some (writeByte memory ptr.toNat value) := by
  have h : (written s op index memory ptr value).mems[index]? = some (writeByte memory ptr.toNat value) := by
    unfold written
    exact storeByte_memory _ index ptr.toNat memory value (by simpa only [paid,chargedStore] using hm)
  simpa only [iterationStore,paid,chargedStore] using h

attribute [local irreducible] loopAfter loopFrameAfter

theorem loopCost_one : loopCost 1=12 := rfl

/-- A positive symbolic number of real loop iterations, including each actual
conditional branch. The last branch falls through; earlier ones pay a backedge. -/

theorem wp_loop_positive (cfg : WasmConfig) (n fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr value count : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hpos : 0<n) (hcount : count.toNat=n)
    (h1 : frame.locals[1]? = some (.i32 value)) (h2 : frame.locals[2]? = some (.i32 count)) (h3 : frame.locals[3]? = some (.i32 ptr))
    (hsize : 4≤frame.locals.size)
    (hm : s.modules[frame.inst]? = some  mi) (hi : mi.memAddrs[0]? = some  index) (hmem : s.mems[index]? = some  memory)
    (hw : memory.wf) (hspan : ptr.toNat+n≤memory.byteSize) (hwidth : ptr.toNat+n≤2^32)
    (hc : s.host.gas.Credits (loopCost n*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (loopAfter s cfg.regularOpCost index memory ptr value count n) limits stack
      (emptyLoopFrame (loopFrameAfter frame ptr count n) stack.size WNear.Binary.ZeroFill.loopBody code) callers [])) rest post) :
    WP cfg (fuel+12*n) (.next (atCode s limits stack (emptyLoopFrame frame stack.size WNear.Binary.ZeroFill.loopBody code) callers WNear.Binary.ZeroFill.loopBody))
      (loopCost n*cfg.regularOpCost+rest) post := by
  induction n generalizing s frame ptr count memory with
  | zero => omega
  | succ n ih =>
    let op := cfg.regularOpCost
    let iter := iterationStore s op index memory ptr value
    let f := iterationFrame frame ptr count
    have dec : (nextCount count).toNat=n := by rw [nextCount_toNat count (by omega)];omega
    have byteBound : ptr.toNat+1≤memory.byteSize := by omega
    have writtenShape := writeByte_spec memory ptr.toNat value hw byteBound
    have iterMem := iteration_memory s op index memory ptr value hmem
    have iterModule : iter.modules[frame.inst]? = some  mi := by
      simpa only [iter,iterationStore,written,storeByte_modules,paid,chargedStore] using hm
    have f1 : f.locals[1]? = some (.i32 value) := by simpa [f,iterationFrame,pointerFrame] using h1
    have f2 : f.locals[2]? = some (.i32 (nextCount count)) := by simp [f,iterationFrame,pointerFrame,show 2<frame.locals.size by omega]
    have f3 : f.locals[3]? = some (.i32 (ptr+1)) := by simp [f,iterationFrame,pointerFrame,show 3<frame.locals.size by omega]
    have fs : 4≤f.locals.size := by simpa [f,iterationFrame,pointerFrame] using hsize
    by_cases hz : n=0
    · cases hz
      simp only [Nat.reduceAdd,loopCost_one] at hc ⊢
      have zero : nextCount count=0 := by apply UInt32.toNat_inj.mp;simpa using dec
      have cr : iter.host.gas.Credits (op+rest) := iteration_credits s op index (op+rest) memory ptr value
        (hc.mono (by dsimp [op];omega))
      have bn : WP cfg fuel (.next (atCode (chargedStore iter cfg.regularOpCost) limits stack
          (emptyLoopFrame f stack.size WNear.Binary.ZeroFill.loopBody code) callers [])) rest post := by
        simpa only [loopAfter,loopFrameAfter,ite_true,iter,f,op] using hnext
      have branch := wp_br_if_zero cfg fuel rest iter limits stack (emptyLoopFrame f stack.size WNear.Binary.ZeroFill.loopBody code) callers [] 0 post cr bn
      have branchNext : WP cfg (fuel+1) (.next (atCode iter limits (stack.push (.i32 (nextCount count)))
          (iterationFrame (emptyLoopFrame frame stack.size WNear.Binary.ZeroFill.loopBody code) ptr count) callers [.br_if 0])) (op+rest) post := by
        simpa only [zero,f,iterationFrame,pointerFrame,emptyLoopFrame,op] using branch
      have step := wp_iteration cfg (fuel+1) (op+rest) s limits stack (emptyLoopFrame frame stack.size WNear.Binary.ZeroFill.loopBody code) callers [.br_if 0]
        ptr value count mi index memory post h1 h2 h3 hm hi hmem byteBound (hc.mono (by dsimp [op];omega)) branchNext
      simpa only [WNear.Binary.ZeroFill.loopBody,loopCost_one,Nat.reduceMul,Nat.reduceSub,Nat.add_assoc,Nat.reduceAdd,
        show 11*cfg.regularOpCost+(op+rest)=12*cfg.regularOpCost+rest by dsimp [op];omega] using step
    · have np : 0<n := by omega
      have nonzero : nextCount count≠0 := by intro h;have z:=congrArg UInt32.toNat h;rw [dec] at z;exact hz (by simpa using z)
      have ptrNext : (ptr+1).toNat=ptr.toNat+1 := by
        have lt := ptr.toNat_lt
        simp only [UInt32.toNat_add,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
        omega
      have cut : 11*op+(2*op+(loopCost n*op+rest))≤loopCost (n+1)*cfg.regularOpCost+rest := by
        rw [loopCost_succ,ite_eq_right hz];simp only [Nat.add_mul];dsimp [op];omega
      have cr : iter.host.gas.Credits (2*op+(loopCost n*op+rest)) := iteration_credits s op index _ memory ptr value (hc.mono cut)
      have cnext := (GasCounter.burn_credits iter.host.gas (2*op) (loopCost n*op+rest) cr).2.2.2
      have recursiveNext : WP cfg fuel (.next (atCode (loopAfter (chargedStore iter (2*op)) op index (writeByte memory ptr.toNat value) (ptr+1) value (nextCount count) n) limits stack
          (emptyLoopFrame (loopFrameAfter f (ptr+1) (nextCount count) n) stack.size WNear.Binary.ZeroFill.loopBody code) callers [])) rest post := by
        simpa only [loopAfter,loopFrameAfter,ite_eq_right hz,iter,f,op] using hnext
      have recProof := ih (s:=chargedStore iter (2*op)) (frame:=f) (ptr:=ptr+1) (count:=nextCount count) (memory:=writeByte memory ptr.toNat value)
        np dec f1 f2 f3 fs iterModule iterMem writtenShape.1
        (by rw [ptrNext,writtenShape.2.1];omega) (by rw [ptrNext];omega) cnext recursiveNext
      have branch := wp_br_if_loop_nonzero cfg (fuel+12*n) (loopCost n*op+rest) iter limits stack f callers WNear.Binary.ZeroFill.loopBody code [] (nextCount count) post nonzero cr recProof
      have branchNext : WP cfg (fuel+12*n+1) (.next (atCode iter limits (stack.push (.i32 (nextCount count)))
          (iterationFrame (emptyLoopFrame frame stack.size WNear.Binary.ZeroFill.loopBody code) ptr count) callers [.br_if 0])) (2*op+(loopCost n*op+rest)) post := by
        simpa only [f,iterationFrame,pointerFrame,emptyLoopFrame,op] using branch
      have step := wp_iteration cfg (fuel+12*n+1) (2*op+(loopCost n*op+rest)) s limits stack (emptyLoopFrame frame stack.size WNear.Binary.ZeroFill.loopBody code) callers [.br_if 0]
        ptr value count mi index memory post h1 h2 h3 hm hi hmem byteBound (hc.mono cut) branchNext
      have cost : 11*cfg.regularOpCost+(2*op+(loopCost n*op+rest))=loopCost (n+1)*cfg.regularOpCost+rest := by rw [loopCost_succ,ite_eq_right hz];simp only [Nat.add_mul];dsimp [op];omega
      simpa only [WNear.Binary.ZeroFill.loopBody,cost,Nat.mul_add,Nat.add_assoc,Nat.reduceAdd,Nat.mul_one] using step
end WNear.Proofs.ZeroFill
