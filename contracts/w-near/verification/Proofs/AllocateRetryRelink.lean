import Proofs.AllocateRetryCheck

/-! Actual sequential new-head link and scratch-root stores in581. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode readI32 writeI32

def linkFrame (frame : CallFrame) (head : UInt32) := {frame with locals:=frame.locals.set! 1 (.i32 head)}
def linkOldFrom (s : Store NearState) (op index : Nat) (memory : Memory) (record head : UInt32) :=
  storeI32 (paid s op 6) index (head.toNat+8) memory (readI32 memory (record.toNat+12))
def linkNewFrom (s : Store NearState) (op index : Nat) (memory : Memory) (record head : UInt32) :=
  storeI32 (paid s op 3) index (record.toNat+12) memory head

theorem wp_link_new (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (record head : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 record)) (h1 : frame.locals[1]?=some (.i32 head))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : record.toNat+16≤memory.byteSize) (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (linkNewFrom s cfg.regularOpCost index memory record head) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      ([.local_get 3,.local_get 1,.store .i32 none {align:=2,offset:=12}]++code))) (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have store := wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset:=12} record head mi index memory post hm hi hmem hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hnext
  have get1 := wp_local_get cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 record)) frame callers _ 1 (.i32 head) post h1
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) store
  have get3 := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers _ 3 (.i32 record) post h3 (hc.mono (by dsimp [op];omega)) get1
  have cost : cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd,List.append_eq,List.cons_append,List.nil_append] using get3

theorem wp_link_old (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (record head : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 record)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : record.toNat+16≤memory.byteSize) (hh : head.toNat+12≤memory.byteSize)
    (hread : readI32 memory (record.toNat+4)=head)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (linkOldFrom s cfg.regularOpCost index memory record head) limits stack (linkFrame frame head) callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      ([.local_get 3,.load .i32 none {align:=2,offset:=4},.local_tee 1,.local_get 3,
        .load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=8}]++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := linkFrame frame head
  have h3f : ff.locals[3]?=some (.i32 record) := by simp [ff,linkFrame,h3]
  have hm5 : (paid s op 5).modules[ff.inst]?=some mi := by simpa only [paid,chargedStore,ff,linkFrame] using hm
  have mem5 : (paid s op 5).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have store := wp_i32_store cfg fuel rest (paid s op 5) limits stack ff callers code {align:=2,offset:=8} head
    (readI32 memory (record.toNat+12)) mi index memory post hm5 hi mem5 (by omega)
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [linkOldFrom,paid,op,ff] using hnext)
  have hm4 : (paid s op 4).modules[ff.inst]?=some mi := by simpa only [paid,chargedStore,ff,linkFrame] using hm
  have mem4 : (paid s op 4).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have load := wp_i32_load cfg (fuel+1) (op+rest) (paid s op 4) limits (stack.push (.i32 head)) ff callers
    (.store .i32 none {align:=2,offset:=8}::code) {align:=2,offset:=12} record mi index memory post hm4 hi mem4 hb
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) store
  have get3 := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 head)) ff callers _ 3 (.i32 record) post h3f
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) load
  have tee := wp_local_tee cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack frame callers _ 1 (.i32 head) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) get3
  have loadHead := wp_i32_load cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits stack frame callers
    (.local_tee 1::.local_get 3::.load .i32 none {align:=2,offset:=12}::.store .i32 none {align:=2,offset:=8}::code)
    {align:=2,offset:=4} record mi index memory post hm hi hmem (by change record.toNat+4+4≤memory.byteSize;omega)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [hread,paid,op,Nat.add_assoc,Nat.reduceAdd] using tee)
  have get := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack frame callers _ 3 (.i32 record) post h3
    (hc.mono (by dsimp [op];omega)) loadHead
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd,List.append_eq,List.cons_append,List.nil_append] using get

def linkFrom (s : Store NearState) (op index : Nat) (memory : Memory) (record head : UInt32) :=
  linkNewFrom (linkOldFrom s op index memory record head) op index
    (writeI32 memory (head.toNat+8) (readI32 memory (record.toNat+12))) record head

/-- Both actual stores, preserving the new head in local1 between them. -/
theorem wp_relink (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (record head : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 record)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb : record.toNat+16≤memory.byteSize) (hh : head.toNat+12≤memory.byteSize)
    (hread : readI32 memory (record.toNat+4)=head)
    (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (linkFrom s cfg.regularOpCost index memory record head) limits stack (linkFrame frame head) callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateRetry.relink++code)))
      (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first := linkOldFrom s op index memory record head
  let ff := linkFrame frame head
  let mem := writeI32 memory (head.toNat+8) (readI32 memory (record.toNat+12))
  have shape := writeI32_spec memory (head.toNat+8) (readI32 memory (record.toNat+12)) hw (by omega)
  have cm : first.host.gas.Credits (3*op+rest) := by
    unfold first linkOldFrom
    rw [storeI32_host]
    exact paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))
  have mf : first.mems[index]?=some mem := by
    apply storeI32_memory
    simpa only [paid,chargedStore] using hmem
  have moduleF : first.modules[ff.inst]?=some mi := by simpa only [first,linkOldFrom,storeI32_modules,paid,chargedStore,ff,linkFrame] using hm
  have h1 : ff.locals[1]?=some (.i32 head) := by
    have sz := (Array.getElem?_eq_some_iff.mp h3).1
    simp [ff,linkFrame,show 1<frame.locals.size by omega]
  have h3f : ff.locals[3]?=some (.i32 record) := by simp [ff,linkFrame,h3]
  have next := wp_link_new cfg fuel rest first limits stack ff callers code record head mi index mem post h3f h1 moduleF hi mf
    (by rw [show mem.byteSize=memory.byteSize from shape.2.1];exact hb) cm hnext
  have bridge : WP cfg (fuel+3) (.next (atCode first limits stack ff callers
      ([.local_get 3,.local_get 1,.store .i32 none {align:=2,offset:=12}]++code))) (3*op+rest) post := next
  have result := wp_link_old cfg (fuel+3) (3*op+rest) s limits stack frame callers
    ([.local_get 3,.local_get 1,.store .i32 none {align:=2,offset:=12}]++code) record head mi index memory post h3 hm hi hmem hb hh hread
    (hc.mono (by dsimp [op];omega)) bridge
  have cost : 6*cfg.regularOpCost+(3*op+rest)=9*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateRetry.relink,List.append_assoc,List.append_eq,List.cons_append,List.nil_append,cost,Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocateRetry
