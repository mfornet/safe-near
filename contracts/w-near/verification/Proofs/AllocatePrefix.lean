import Binary.Allocate
import Proofs.DeallocateAlignNative
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules

/-! The real positive-size f581 prefix: checked word rounding through570/568,
then save the original allocator head in the caller's scratch record. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode readI32 writeI32

def roundedStore (s : Store NearState) (op : Nat) := paid (DeallocateAlign.after570 (paid s op 1) op) op 1
def roundedFrame (frame : CallFrame) (size : UInt32) :=
  {frame with locals := frame.locals.set! 4 (.i32 (DeallocateAlign.quotient size 4))}
def savedHead (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory) :=
  storeI32 (paid s op 4) index (scratch.toNat+12) memory (readI32 memory allocator.toNat)

theorem wp_save_head (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch allocator : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[3]? = some (.i32 scratch)) (ha : frame.locals[0]? = some (.i32 allocator))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : allocator.toNat+4 ≤ memory.byteSize)
    (hw : scratch.toNat+16 ≤ memory.byteSize) (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (savedHead s cfg.regularOpCost index scratch allocator memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      ([.local_get 3,.local_get 0,.load .i32 none {align:=2,offset:=0},
        .store .i32 none {align:=2,offset:=12}] ++ code))) (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hm3 : (paid s op 3).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hmem3 : (paid s op 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 3 (.i32 scratch) post hs (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+2) _ (paid s op 1) limits _ frame callers _ 0 (.i32 allocator) post ha
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+1) _ (paid s op 2) limits (stack.push (.i32 scratch)) frame callers _
    {align:=2,offset:=0} allocator mi index memory post hm2 hi hmem2 (by simpa using hb)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero]
  apply wp_i32_store cfg fuel rest (paid s op 3) limits stack frame callers code
    {align:=2,offset:=12} scratch (readI32 memory allocator.toNat) mi index memory post hm3 hi hmem3 (by omega)
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- The actual size-rounding call includes both deployed helper bodies. -/
theorem wp_round (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (size : UInt32) (mi : ModuleInst) (address568 address570 : Nat) (post : Post)
    (hl : frame.locals[1]? = some (.i32 size))
    (hm : s.modules[frame.inst]? = some mi) (hi568 : mi.funcAddrs[568]? = some address568)
    (hf568 : s.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hi570 : mi.funcAddrs[570]? = some address570)
    (hf570 : s.funcs[address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570))
    (hn : size.toNat+4 < 2^32) (hd : callers.length+2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (43*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (roundedStore s cfg.regularOpCost) limits base.toArray (roundedFrame frame size) callers code)) rest post) :
    WP cfg (fuel+27) (.next (atCode s limits base.toArray frame callers
      ([.local_get 1,.call 570,.local_set 4] ++ code))) (43*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have checks := DeallocateAlign.checks570 size hn
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hf568' : (paid s op 1).funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568) := by simpa only [paid,chargedStore] using hf568
  have hf570' : (paid s op 1).funcs[address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570) := by simpa only [paid,chargedStore] using hf570
  have push (value : Value) : base.toArray.push value = (base++[value]).toArray := by
    apply Array.toList_inj.mp
    simp
  have cc := paid_credits s op 1 (41*op+(op+rest)) (hc.mono (by dsimp [op]; omega))
  have ca := DeallocateAlign.after570_credits (paid s op 1) op (op+rest) cc
  have lastNext : WP cfg fuel (.next (atCode (chargedStore (DeallocateAlign.after570 (paid s op 1) op) op)
      limits base.toArray {frame with locals := frame.locals.set! 4 (.i32 (DeallocateAlign.quotient size 4))} callers code)) rest post := by
    simpa only [roundedStore,roundedFrame,paid,op] using hnext
  have last := wp_local_set cfg fuel rest (DeallocateAlign.after570 (paid s op 1) op) limits base.toArray frame callers code 4 (.i32 (DeallocateAlign.quotient size 4)) post ca lastNext
  have last' : WP cfg (fuel+1) (.next (atCode (DeallocateAlign.after570 (paid s op 1) op) limits
      (base++[Value.i32 (DeallocateAlign.quotient size 4)]).toArray frame callers (.local_set 4::code))) (op+rest) post := by
    simpa only [push] using last
  have call := DeallocateAlign.wp_call570 cfg (fuel+1) (op+rest) (paid s op 1) limits base frame callers
    (.local_set 4::code) size mi address568 address570 post hm1 hi568 hf568' hi570 hf570' checks.1 checks.2 hd cc last'
  have call' : WP cfg (fuel+26) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 size)) frame callers
      (.call 570::.local_set 4::code))) (42*op+rest) post := by
    have cost : 41*cfg.regularOpCost+(op+rest)=42*op+rest := by dsimp [op]; omega
    rw [cost] at call
    simpa only [push,Nat.add_assoc,Nat.reduceAdd] using call
  have result := wp_local_get cfg (fuel+26) (42*op+rest) s limits base.toArray frame callers _ 1 (.i32 size) post hl
    (hc.mono (by dsimp [op]; omega)) call'
  have cost : cfg.regularOpCost+(42*op+rest)=43*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append] using result

theorem roundedStore_resources (s : Store NearState) (op : Nat) :
    {roundedStore s op with host := s.host} = s := by
  simp only [roundedStore,DeallocateAlign.after570,DeallocateAlign.bodyAfter570,
    DeallocateAlign.after568,DeallocateAlign.entered568,DeallocateAlign.entered570,paid,chargedStore]

def prefixAfter (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory) :=
  savedHead (roundedStore s op) op index scratch allocator memory

/-- The actual positive-size prefix of f581, including both checked rounding
helpers and the original-head scratch write. No search result is assumed. -/
theorem wp_align_and_save (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (size scratch allocator : UInt32) (mi : ModuleInst)
    (index address568 address570 : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[1]? = some (.i32 size)) (hs : frame.locals[3]? = some (.i32 scratch))
    (ha : frame.locals[0]? = some (.i32 allocator))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : allocator.toNat+4 ≤ memory.byteSize)
    (hw : scratch.toNat+16 ≤ memory.byteSize)
    (hi568 : mi.funcAddrs[568]? = some address568)
    (hf568 : s.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hi570 : mi.funcAddrs[570]? = some address570)
    (hf570 : s.funcs[address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570))
    (hn : size.toNat+4 < 2^32) (hd : callers.length+2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (47*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (prefixAfter s cfg.regularOpCost index scratch allocator memory)
      limits base.toArray (roundedFrame frame size) callers code)) rest post) :
    WP cfg (fuel+31) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Allocate.alignAndSave ++ code)))
      (47*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have cr := DeallocateAlign.after570_credits (paid s op 1) op (5*op+rest)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have cp : (roundedStore s op).host.gas.Credits (4*op+rest) :=
    paid_credits (DeallocateAlign.after570 (paid s op 1) op) op 1 _ (cr.mono (by omega))
  have resource := roundedStore_resources s op
  have mm := congrArg (fun t=>t.modules) resource
  have mems := congrArg (fun t=>t.mems) resource
  simp only at mm mems
  have hm' : (roundedStore s op).modules[(roundedFrame frame size).inst]? = some mi := by
    rw [mm]; exact hm
  have hmem' : (roundedStore s op).mems[index]? = some memory := by rw [mems]; exact hmem
  have hs' : (roundedFrame frame size).locals[3]? = some (.i32 scratch) := by simp [roundedFrame,hs]
  have ha' : (roundedFrame frame size).locals[0]? = some (.i32 allocator) := by simp [roundedFrame,ha]
  have save := wp_save_head cfg fuel rest (roundedStore s op) limits base.toArray (roundedFrame frame size) callers code
    scratch allocator mi index memory post hs' ha' hm' hi hmem' hb hw cp hnext
  have result := wp_round cfg (fuel+4) (4*op+rest) s limits base frame callers
    ([.local_get 3,.local_get 0,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=12}] ++ code)
    size mi address568 address570 post hl hm hi568 hf568 hi570 hf570 hn hd
    (hc.mono (by dsimp [op]; omega)) save
  have cost : 43*cfg.regularOpCost+(4*op+rest)=47*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [WNear.Binary.Allocate.alignAndSave,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.Allocate
