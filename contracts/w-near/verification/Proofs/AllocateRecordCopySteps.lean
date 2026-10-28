import Proofs.AllocateLayoutWrapperSteps

/-! The690 word copies read their input sequentially, retaining alias behavior. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP readI32 writeI32

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih

def copyWord (s : Store NearState) (op index dstOffset srcOffset : Nat)
    (out source : UInt32) (memory : Memory) :=
  storeI32 (paid s op 4) index (out.toNat+dstOffset) memory (readI32 memory (source.toNat+srcOffset))

theorem wp_copy_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (outSlot sourceSlot dstOffset srcOffset : Nat) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[outSlot]?=some (.i32 out)) (hs : frame.locals[sourceSlot]?=some (.i32 source))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hr : source.toNat+srcOffset+4 ≤ memory.byteSize) (hw : out.toNat+dstOffset+4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copyWord s cfg.regularOpCost index dstOffset srcOffset out source memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      ([.local_get outSlot,.local_get sourceSlot,.load .i32 none {align:=2,offset:=srcOffset},
        .store .i32 none {align:=2,offset:=dstOffset}] ++ code))) (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have m3 : (paid s op 3).modules[frame.inst]?=some mi := hm
  have mm3 : (paid s op 3).mems[index]?=some memory := hmem
  have st := wp_i32_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=2,offset:=dstOffset}
    out (readI32 memory (source.toNat+srcOffset)) mi index memory post m3 hi mm3 hw
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have m2 : (paid s op 2).modules[frame.inst]?=some mi := hm
  have mm2 : (paid s op 2).mems[index]?=some memory := hmem
  have ld := wp_i32_load cfg (fuel+1) (op+rest) (paid s op 2) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=dstOffset}::code) {align:=2,offset:=srcOffset} source mi index memory post m2 hi mm2 hr
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) st
  have g2 := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.load .i32 none {align:=2,offset:=srcOffset}::.store .i32 none {align:=2,offset:=dstOffset}::code)
    sourceSlot (.i32 source) post hs (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) ld
  have g1 := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.local_get sourceSlot::.load .i32 none {align:=2,offset:=srcOffset}::.store .i32 none {align:=2,offset:=dstOffset}::code)
    outSlot (.i32 out) post ho (hc.mono (by dsimp [op]; omega)) g2
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp [op];omega] using g1

def firstMemory (memory : Memory) (out source : UInt32) :=
  writeI32 memory out.toNat (readI32 memory (source.toNat+8))
def finalMemory (memory : Memory) (out source : UInt32) :=
  writeI32 (firstMemory memory out source) (out.toNat+4) (readI32 (firstMemory memory out source) (source.toNat+12))
def copied (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) :=
  copyWord (copyWord s op index 0 8 out source memory) op index 4 12 out source (firstMemory memory out source)

attribute [local irreducible] copyWord firstMemory copied

theorem wp_copy (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[3]?=some (.i32 source))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hwf : memory.wf) (hr : source.toNat+16 ≤ memory.byteSize) (hw : out.toNat+8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copied s cfg.regularOpCost index out source memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers
      ([.local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=8},.store .i32 none {align:=2,offset:=0},
        .local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=4}] ++ code)))
      (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first := copyWord s op index 0 8 out source memory
  have fm : first.mems[index]?=some (firstMemory memory out source) := by
    have mm : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact hmem
    have z := storeI32_memory (paid s op 4) index out.toNat memory (readI32 memory (source.toNat+8)) mm
    simpa only [first,copyWord,firstMemory,Nat.add_zero] using z
  have md : first.modules[frame.inst]?=some mi := by rw [show first.modules=s.modules from by simp only [first,copyWord,storeI32_modules,modules_paid]];exact hm
  have fs := writeI32_spec memory out.toNat (readI32 memory (source.toNat+8)) hwf (by omega)
  have bound : (firstMemory memory out source).byteSize=memory.byteSize := by simpa only [firstMemory] using fs.2.1
  have cr : first.host.gas.Credits (4*op+rest) := by
    unfold first copyWord
    exact paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))
  have second := wp_copy_word cfg fuel rest first limits stack frame callers code 0 3 4 12 out source mi index
    (firstMemory memory out source) post ho hs md hi fm (by rw [bound];omega) (by rw [bound];omega) cr (by simpa only [copied,first,op] using hnext)
  have one := wp_copy_word cfg (fuel+4) (4*op+rest) s limits stack frame callers
    ([.local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=4}]++code)
    0 3 0 8 out source mi index memory post ho hs hm hi hmem (by omega) (by omega)
    (hc.mono (by dsimp [op];omega)) second
  simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4*cfg.regularOpCost+(4*op+rest)=8*cfg.regularOpCost+rest by dsimp [op];omega] using one

end WNear.Proofs.AllocateRecordCopy
