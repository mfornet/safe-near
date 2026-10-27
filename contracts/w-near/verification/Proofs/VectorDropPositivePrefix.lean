import Proofs.VectorDropPositiveState

/-! Actual positive f68 execution through every wrapper to the pending f237
call. This prefix changes gas accounting alone and assumes no heap outcome. -/
namespace WNear.Proofs.VectorDropPositive
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.VectorDrop
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- The first three f68 instructions include the real empty f778 call. -/
theorem wp_before747 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame.inst p)
    (hv : frame.locals[0]? = some (.i32 p.vector)) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (before747 s cfg.regularOpCost) limits
      (base ++ [Value.i32 p.vector]).toArray frame callers (.call 747 :: code))) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits base.toArray frame callers (WNear.Binary.VectorDrop.body68 ++ code)))
      (12 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let first := paid s op 1
  let middle := entered first op
  have c1 := paid_credits s op 1 (11 * op + rest) (hc.mono (by dsimp [op]; omega))
  have c2 := entered_credits first op (op + rest) (c1.mono (by omega))
  have array : (base ++ [Value.i32 p.vector]).toArray = base.toArray.push (.i32 p.vector) := by
    apply Array.toList_inj.mp
    simp
  have get2Next : WP cfg fuel (.next (atCode (chargedStore middle cfg.regularOpCost) limits
      (base.toArray.push (.i32 p.vector)) frame callers (.call 747 :: code))) rest post := by
    simpa only [before747, first, middle, array, paid, op] using hnext
  have get2 := wp_local_get cfg fuel rest middle limits base.toArray frame callers (.call 747 :: code) 0 (.i32 p.vector) post hv c2 get2Next
  have hm1 : first.modules[frame.inst]? = some p.mi := by simpa only [first, paid, chargedStore] using hr.module
  have hf1 : first.funcs[p.address778]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function778) := by
    simpa only [first, paid, chargedStore] using hr.function778
  have empty := wp_call_empty cfg (fuel + 1) (op + rest) first limits base frame callers (.local_get 0 :: .call 747 :: code)
    p.vector p.mi p.address778 post hm1 hr.index778 hf1 hd (c1.mono (by omega)) get2
  have get1Next : WP cfg (fuel + 3) (.next (atCode (chargedStore s cfg.regularOpCost) limits (base.toArray.push (.i32 p.vector)) frame callers
      (.call 778 :: .local_get 0 :: .call 747 :: code))) (11 * op + rest) post := by
    simpa only [first, paid, array, Nat.add_assoc, Nat.reduceAdd,
      show 10 * cfg.regularOpCost + (op + rest) = 11 * op + rest by dsimp [op]; omega] using empty
  have get1 := wp_local_get cfg (fuel + 3) (11 * op + rest) s limits base.toArray frame callers (.call 778 :: .local_get 0 :: .call 747 :: code) 0 (.i32 p.vector) post hv
    (hc.mono (by dsimp [op]; omega)) get1Next
  simpa only [WNear.Binary.VectorDrop.body68, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (11 * op + rest) = 12 * cfg.regularOpCost + rest by dsimp [op]; omega] using get1

/-- Every actual nested call before the allocator is discharged from original
code and header facts. The next instruction is f237, with its real arguments
and saved wrapper frames, rather than an assumed allocator postcondition. -/
theorem wp_to237 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame.inst p)
    (hv : frame.locals[0]? = some (.i32 p.vector)) (hd : callers.length + 3 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (62 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (before237 s cfg.regularOpCost) limits
      (base ++ arguments p).toArray (forwardLeaf frame.inst base.length p)
      ([capacityBlocked frame.inst base.length p, vectorBlocked frame.inst base.length p, {frame with code}] ++ callers)
      [.call 237, .return])) rest post) :
    WP cfg (fuel + 27) (.next (atCode s limits base.toArray frame callers (WNear.Binary.VectorDrop.body68 ++ code)))
      (62 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let vf := vectorBlocked frame.inst base.length p
  let cf := capacityBlocked frame.inst base.length p
  let saved := {frame with code}
  have c311 := before311_credits s op (14 * op + rest) (hc.mono (by dsimp [op]; omega))
  have hm311 : (before311 s op).modules[cf.inst]? = some p.mi := by
    simpa only [before311, before777, before747, paid, entered, tripleEntry, chargedStore, cf, capacityBlocked, capacityLeaf, tripleFrame, emptyBlockFrame] using hr.module
  have hf311 : (before311 s op).funcs[p.address311]? = some (.wasm WNear.Binary.VectorDrop.tripleSignature cf.inst WNear.Binary.VectorDrop.function311) := by
    simpa only [before311, before777, before747, paid, entered, tripleEntry, chargedStore, cf, capacityBlocked, capacityLeaf, tripleFrame, emptyBlockFrame] using hr.function311
  have forwardNext : WP cfg fuel (.next (atCode (paid (tripleEntry (before311 s op) op) op 3) limits
      (base ++ [Value.i32 (pointer p), .i32 (capacity p), .i32 1]).toArray (tripleFrame cf.inst base.length (pointer p) (capacity p) 1)
      ({cf with code := []} :: vf :: saved :: callers) [.call 237, .return])) rest post := by
    simpa only [before237, arguments, forwardLeaf, cf, capacityBlocked, capacityLeaf, tripleFrame, emptyBlockFrame,
      List.cons_append, List.nil_append, vf, saved] using hnext
  have forward := wp_call_forward_prefix cfg fuel rest (before311 s op) limits base cf (vf :: saved :: callers) [] (pointer p) (capacity p) 1 p.mi p.address311 post
    hm311 hr.index311 hf311 (by simpa only [List.length_cons] using hd) c311 forwardNext
  have c777 := before777_credits s op (31 * op + rest) (hc.mono (by dsimp [op]; omega))
  have hm777 : (before777 s op).modules[vf.inst]? = some p.mi := by
    simpa only [before777, before747, paid, entered, chargedStore, vf, vectorBlocked, vectorLeaf, vectorFrame, capacityFrame, emptyBlockFrame] using hr.module
  have hf777 : (before777 s op).funcs[p.address777]? = some (.wasm WNear.Binary.VectorDrop.tripleSignature vf.inst WNear.Binary.VectorDrop.function777) := by
    simpa only [before777, before747, paid, entered, chargedStore, vf, vectorBlocked, vectorLeaf, vectorFrame, capacityFrame, emptyBlockFrame] using hr.function777
  have capacityNext : WP cfg (fuel + 4) (.next (atCode (paid (tripleEntry (before777 s op) op) op 6) limits
      (base ++ [Value.i32 (pointer p), .i32 (capacity p), .i32 1]).toArray
      (emptyBlockFrame (tripleFrame vf.inst base.length (pointer p) (capacity p) 1) base.toArray.size []) ({vf with code := []} :: saved :: callers) [.call 311])) (14 * op + rest) post := by
    simpa only [before311, cf, capacityBlocked, capacityLeaf, vf, vectorBlocked, vectorLeaf, vectorFrame, capacityFrame, emptyBlockFrame,
      List.size_toArray] using forward
  have capCall := wp_call_capacity_prefix cfg (fuel + 4) (14 * op + rest) (before777 s op) limits base vf (saved :: callers) [] (pointer p) (capacity p) 1 p.mi p.address777 post
    hm777 hr.index777 hf777 hr.positive (by have h := hd; simp only [List.length_cons]; omega) (c777.mono (by dsimp [op]; omega)) capacityNext
  have c747 := before747_credits s op (50 * op + rest) (hc.mono (by dsimp [op]; omega))
  have hm747 : (before747 s op).modules[frame.inst]? = some p.mi := by simpa only [before747, paid, entered, chargedStore] using hr.module
  have hmem747 : (before747 s op).mems[p.memoryIndex]? = some p.memory := by simpa only [before747, paid, entered, chargedStore] using hr.memory
  have hf747 : (before747 s op).funcs[p.address747]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747) := by
    simpa only [before747, paid, entered, chargedStore] using hr.function747
  have vectorNext : WP cfg (fuel + 12) (.next (atCode (paid (entered (before747 s op) op) op 9) limits
      (base ++ [Value.i32 (readI32 p.memory p.vector.toNat), .i32 (readI32 p.memory (p.vector.toNat + 4)), .i32 1]).toArray
      (emptyBlockFrame (capacityFrame (vectorFrame frame.inst base.length p.vector) (readI32 p.memory (p.vector.toNat + 4))) base.toArray.size [])
      ({frame with code} :: callers) [.call 777])) (31 * op + rest) post := by
    simpa only [before777, pointer, capacity, vf, vectorBlocked, vectorLeaf, saved, List.size_toArray, Nat.add_assoc, Nat.reduceAdd,
      show 17 * cfg.regularOpCost + (14 * op + rest) = 31 * op + rest by dsimp [op]; omega] using capCall
  have vectorCall := wp_call_vector_prefix cfg (fuel + 12) (31 * op + rest) (before747 s op) limits base frame callers code p.vector p.mi p.memoryIndex p.address747 p.memory post
    hm747 hr.memoryIndex hmem747 hr.index747 hf747 hr.bound hr.positive (by omega) (c747.mono (by dsimp [op]; omega)) vectorNext
  have initialNext : WP cfg (fuel + 23) (.next (atCode (before747 s op) limits (base ++ [Value.i32 p.vector]).toArray frame callers (.call 747 :: code))) (50 * op + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd,
      show 19 * cfg.regularOpCost + (31 * op + rest) = 50 * op + rest by dsimp [op]; omega] using vectorCall
  have start := wp_before747 cfg (fuel + 23) (50 * op + rest) s limits base frame callers code p post hr hv (by omega)
    (hc.mono (by dsimp [op]; omega)) initialNext
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show 12 * cfg.regularOpCost + (50 * op + rest) = 62 * cfg.regularOpCost + rest by dsimp [op]; omega] using start
end WNear.Proofs.VectorDropPositive
