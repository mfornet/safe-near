import Proofs.AllocateSplit

/-! Tagged free-list pointer writes used by the actual f580 split path.
Reads use the current memory, retaining sequential alias behavior. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
attribute [local irreducible] WP atCode readI32 writeI32

def taggedValue (memory : Memory) (address : UInt32) (offset : Nat) (value : UInt32) :=
  (readI32 memory (address.toNat+offset) &&& 3) ||| value

def taggedPrefix (targetSlot sourceSlot valueSlot offset : Nat) : Expr :=
  [.local_get targetSlot,.local_get sourceSlot,.load .i32 none {align:=2,offset},
    .i32_const 3,.i32_binop .and,.local_get valueSlot,.i32_binop .or]

theorem wp_tagged_value (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (targetSlot sourceSlot valueSlot offset : Nat) (target source value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ht : frame.locals[targetSlot]? = some (.i32 target)) (hs : frame.locals[sourceSlot]? = some (.i32 source))
    (hv : frame.locals[valueSlot]? = some (.i32 value)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : source.toNat+offset+4 ≤ memory.byteSize) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      ((stack.push (.i32 target)).push (.i32 (taggedValue memory source offset value))) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      (taggedPrefix targetSlot sourceSlot valueSlot offset ++ code))) (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ s limits stack frame callers _ targetSlot (.i32 target) post ht (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ (paid s op 1) limits _ frame callers _ sourceSlot (.i32 source) post hs
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+4) _ (paid s op 2) limits (stack.push (.i32 target)) frame callers _
    {align:=2,offset} source mi index memory post hm2 hi hmem2 hr
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s op 3) limits _ frame callers _ 3 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+2) _ (paid s op 4) limits (stack.push (.i32 target)) frame callers _ (readI32 memory (source.toNat+offset)) 3 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+1) _ (paid s op 5) limits _ frame callers _ valueSlot (.i32 value) post hv
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_or cfg fuel rest (paid s op 6) limits (stack.push (.i32 target)) frame callers code
    (readI32 memory (source.toNat+offset) &&& 3) value post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

def taggedStore (s : Store NearState) (op index readOffset writeOffset : Nat)
    (memory : Memory) (target source value : UInt32) :=
  storeI32 (paid s op 8) index (target.toNat+writeOffset) memory (taggedValue memory source readOffset value)

/-- The tagged backlink update is an eight-opcode real memory operation. -/
theorem wp_tagged_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (targetSlot sourceSlot valueSlot readOffset writeOffset : Nat) (target source value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ht : frame.locals[targetSlot]? = some (.i32 target)) (hs : frame.locals[sourceSlot]? = some (.i32 source))
    (hv : frame.locals[valueSlot]? = some (.i32 value)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : source.toNat+readOffset+4 ≤ memory.byteSize) (hw : target.toNat+writeOffset+4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (taggedStore s cfg.regularOpCost index readOffset writeOffset memory target source value)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers
      (taggedPrefix targetSlot sourceSlot valueSlot readOffset ++ .store .i32 none {align:=2,offset:=writeOffset} :: code)))
      (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm7 : (paid s op 7).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem7 : (paid s op 7).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have last := wp_i32_store cfg fuel rest (paid s op 7) limits stack frame callers code
    {align:=2,offset:=writeOffset} target (taggedValue memory source readOffset value) mi index memory post hm7 hi hmem7 hw
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) hnext
  have result := wp_tagged_value cfg (fuel+1) (op+rest) s limits stack frame callers
    (.store .i32 none {align:=2,offset:=writeOffset} :: code) targetSlot sourceSlot valueSlot readOffset target source value
    mi index memory post ht hs hv hm hi hmem hr (hc.mono (by dsimp [op]; omega)) last
  have cost : 7*cfg.regularOpCost+(op+rest)=8*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.Allocate
