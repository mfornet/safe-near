import Proofs.AllocateSkipControl
import Proofs.AllocateSkipNative
import Binary.AllocateSkip

/-! The actual root update and scan-loop backedge after rejecting a short node. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
attribute [local irreducible] WP atCode readI32 writeI32 WNear.Binary.AllocateSearch.scan WNear.Binary.AllocateSearch.exhausted
set_option maxRecDepth 16384

def advanceStore (s : Store NearState) (op : Nat) (p : Layout) :=
  chargedStore (storeI32 (paid s op 5) p.memoryIndex p.root.toNat p.memory (next p)) (2*op)
def advanceFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 1 (.i32 (next p))}

private theorem paid_succ (s : Store NearState) (op n : Nat) : chargedStore (paid s op n) op=paid s op (n+1) := rfl
private theorem paid_one (s : Store NearState) (op : Nat) : chargedStore s op=paid s op 1 := rfl

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem wp_store_link (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (target link value : UInt32) (post : Post)
    (ht : target.toNat+4≤memory.byteSize) (hl : link.toNat+4≤memory.byteSize)
    (hr : readI32 memory link.toNat=value)
    (h2 : frame.locals[2]?=some (.i32 target)) (h9 : frame.locals[9]?=some (.i32 link))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 5) index target.toNat memory value) limits stack
      {frame with locals:=frame.locals.set! 1 (.i32 value)} callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      ([.local_get 2,.local_get 9,.load .i32 none {align:=2,offset:=0},.local_tee 1,.store .i32 none {align:=2,offset:=0}]++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let uf := {frame with locals:=frame.locals.set! 1 (.i32 value)}
  have hm4 : (paid s op 4).modules[uf.inst]?=some mi := by rw [modules_paid];exact hm
  have mem4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have stored := wp_i32_store cfg fuel rest (paid s op 4) limits stack uf callers code
    {align:=2,offset:=0} target value mi index memory post hm4 hi mem4 (by simpa using ht)
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [op,uf,paid_succ,Nat.reduceAdd,Nat.add_zero] using hnext)
  have tee := wp_local_tee cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 target)) frame callers
    (.store .i32 none {align:=2,offset:=0}::code) 1 (.i32 value) post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [op,uf,paid_succ,Nat.reduceAdd] using stored)
  have hm2 : (paid s op 2).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have mem2 : (paid s op 2).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have loaded := wp_i32_load cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits (stack.push (.i32 target)) frame callers
    (.local_tee 1::.store .i32 none {align:=2,offset:=0}::code) {align:=2,offset:=0} link mi index memory post hm2 hi mem2
    (by simpa using hl) (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [op,Nat.add_zero,hr,paid_succ,Nat.add_assoc,Nat.reduceAdd] using tee)
  have get9 := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 target)) frame callers
    (.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::code) 9 (.i32 link) post h9
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) (by simpa only [op,paid_succ,Nat.add_assoc,Nat.reduceAdd] using loaded)
  have first := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.local_get 9::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::code) 2 (.i32 target) post h2
    (hc.mono (by dsimp [op];omega)) (by simpa only [op,paid_one] using get9)
  have ce : cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [List.cons_append,List.nil_append,ce] using first

 theorem wp_advance (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (p : Layout) (post : Post) (hn : Native p)
    (h2 : frame.locals[2]?=some (.i32 p.root)) (h9 : frame.locals[9]?=some (.i32 (head p+8)))
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.memAddrs[0]?=some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]?=some p.memory) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (advanceStore s cfg.regularOpCost p) limits stack
      (scanFrame (advanceFrame frame p) stack.size code) callers WNear.Binary.AllocateSearch.scan)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack
      (emptyBlockFrame (scanFrame frame stack.size code) stack.size []) callers WNear.Binary.AllocateSkip.advance))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let updated := advanceFrame frame p
  let written := storeI32 (paid s op 5) p.memoryIndex p.root.toNat p.memory (next p)
  have wn : WP cfg fuel (.next (atCode (chargedStore written (2*cfg.regularOpCost)) limits stack
      (scanFrame updated stack.size code) callers WNear.Binary.AllocateSearch.scan)) rest post := by
    simpa only [advanceStore,written,op] using hnext
  have back := wp_backedge cfg fuel rest written limits stack (emptyBlockFrame (outerFrame updated stack.size code) stack.size WNear.Binary.Allocate.commit) callers
    WNear.Binary.AllocateSearch.scan (WNear.Binary.AllocateSearch.exhausted.drop 1) [] [] post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) wn
  have bn : WP cfg (fuel+1) (.next (atCode written limits stack
      (advanceFrame (emptyBlockFrame (scanFrame frame stack.size code) stack.size []) p) callers [.br 1])) (2*op+rest) post := by
    simpa only [updated,advanceFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,op] using back
  have normal := hn.firstNormal
  have endLt := (DeallocateListSize.endWord p.memory (head p)).toNat_lt
  have addNat : (head p+8).toNat=(head p).toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    omega
  have linkRead : readI32 p.memory (head p+8).toNat=next p := by rw [addNat];rfl
  have first := wp_store_link cfg (fuel+1) (2*op+rest) s limits stack (emptyBlockFrame (scanFrame frame stack.size code) stack.size []) callers [.br 1]
    p.mi p.memoryIndex p.memory p.root (head p+8) (next p) post hn.rootBound (by rw [addNat];have:=hn.headBound;omega) linkRead h2 h9 hm hi hmem
    (hc.mono (by dsimp [op];omega)) bn
  have ce : 5*cfg.regularOpCost+(2*op+rest)=7*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateSkip.advance,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,ce] using first
end
end WNear.Proofs.AllocateSkip
