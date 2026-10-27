import Proofs.SerializeMultiplyLow
import Proofs.SerializeMultiplyHigh

/-! Complete actual f954 active body, with both sequential output stores. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI64 writeI64
set_option maxRecDepth 16384

theorem lowStore_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (w : Words)
    (hc : s.host.gas.Credits (31*op+rest)) : (lowStore s op index memory w).host.gas.Credits rest :=
  paid_credits s op 31 rest hc

theorem after_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (w : Words)
    (hc : s.host.gas.Credits (60*op+rest)) : (after s op index memory w).host.gas.Credits rest := by
  have cut : 31*op+(29*op+rest) ≤ 60*op+rest := by omega
  exact paid_credits (lowStore s op index memory w) op 29 rest (lowStore_credits s op index _ memory w (hc.mono cut))

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (w : Words) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 w.out)) (h1 : frame.locals[1]?=some (.i64 w.aLo))
    (h2 : frame.locals[2]?=some (.i64 w.aHi)) (h3 : frame.locals[3]?=some (.i64 w.bLo))
    (h4 : frame.locals[4]?=some (.i64 w.bHi)) (hs : 12 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hw : memory.wf) (hb : w.out.toNat+16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (60*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory w) limits stack (finalFrame frame w) callers code)) rest post) :
    WP cfg (fuel+60) (.next (atCode s limits stack frame callers (WNear.Binary.SerializeMultiply.body++code)))
      (60*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have cut : 31*op+(29*op+rest) ≤ 60*cfg.regularOpCost+rest := by dsimp [op]; omega
  have c31 := lowStore_credits s op index (29*op+rest) memory w (hc.mono cut)
  have shape := writeI64_spec memory w.out.toNat (lowWord w) hw (by omega)
  have hb' : w.out.toNat+16 ≤ (lowMemory memory w).byteSize := by rw [show (lowMemory memory w).byteSize=memory.byteSize from shape.2.1]; exact hb
  have hm' : (lowStore s op index memory w).modules[(finalFrame frame w).inst]?=some mi := by
    simpa only [lowStore,storeI64_modules,paid,chargedStore,finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame] using hm
  have mem' : (lowStore s op index memory w).mems[index]?=some (lowMemory memory w) := by
    unfold lowStore lowMemory
    apply storeI64_memory
    simpa only [paid,chargedStore] using hmem
  have bounds : 5 < frame.locals.size ∧ 6 < frame.locals.size ∧ 7 < frame.locals.size ∧ 8 < frame.locals.size ∧
      9 < frame.locals.size ∧ 10 < frame.locals.size ∧ 11 < frame.locals.size := by omega
  have l0 : (finalFrame frame w).locals[0]?=some (.i32 w.out) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,h0]
  have l1 : (finalFrame frame w).locals[1]?=some (.i64 w.aLo) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,h1]
  have l2 : (finalFrame frame w).locals[2]?=some (.i64 w.aHi) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,h2]
  have l3 : (finalFrame frame w).locals[3]?=some (.i64 w.bLo) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,h3]
  have l4 : (finalFrame frame w).locals[4]?=some (.i64 w.bHi) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,h4]
  have l5 : (finalFrame frame w).locals[5]?=some (.i64 (lowWord w)) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,bounds]
  have l6 : (finalFrame frame w).locals[6]?=some (.i64 (a1 w)) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,bounds]
  have l7 : (finalFrame frame w).locals[7]?=some (.i64 (cross0 w)) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,bounds]
  have l8 : (finalFrame frame w).locals[8]?=some (.i64 (b1 w)) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,bounds]
  have l10 : (finalFrame frame w).locals[10]?=some (.i64 (cross w)) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,bounds]
  have l11 : (finalFrame frame w).locals[11]?=some (.i64 (shifted w)) := by
    simp [finalFrame,frame7,frame6,frame5,frame4,frame3,frame2,frame1,teeFrame,bounds]
  have nextHigh : WP cfg fuel (.next (atCode (highStore (lowStore s op index memory w) op index (lowMemory memory w) w)
      limits stack (finalFrame frame w) callers code)) rest post := by
    simpa only [highStore,after,op] using hnext
  have upper := wp_high cfg fuel rest (lowStore s op index memory w) limits stack (finalFrame frame w) callers code w mi index (lowMemory memory w) post
    l0 l1 l2 l3 l4 l5 l6 l7 l8 l10 l11 hm' hi mem' hb' c31 nextHigh
  have lower := wp_low cfg (fuel+29) (29*op+rest) s limits stack frame callers (WNear.Binary.SerializeMultiply.high++code) w mi index memory post
    h0 h1 h3 hs hm hi hmem (by omega) (hc.mono cut) upper
  simpa only [WNear.Binary.SerializeMultiply.body,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 31*cfg.regularOpCost+(29*op+rest)=60*cfg.regularOpCost+rest by dsimp [op]; omega] using lower

end WNear.Proofs.SerializeMultiply
