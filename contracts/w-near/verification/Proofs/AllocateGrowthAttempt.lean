import Binary.AllocateGrowth
import Proofs.AllocateGrowthRound
import NearVM.MeteredMemoryGrowRules
import NearVM.MeteredLoopRules
import NearVM.MeteredNumericRules
import NearVM.MeteredScalarRules

/-! Real page rounding and successful memory.grow of f577, with the exact linear fee. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode after569
set_option maxRecDepth 16384

def growPages (bytes : UInt32) := DeallocateAlign.quotient bytes 65536
def rounded (s : Store NearState) (op : Nat) := after569 (paid s op 1) op
def beforeGrowth (s : Store NearState) (op : Nat) := paid (rounded s op) op 1
def growthStore (cfg : WasmConfig) (s : Store NearState) (index : Nat) (grown : Memory) (bytes : UInt32) :=
  grownStore (chargedStore (beforeGrowth s cfg.regularOpCost) (memoryGrowCost cfg (growPages bytes))) index grown
def growthAfter (cfg : WasmConfig) (s : Store NearState) (index : Nat) (grown : Memory) (bytes : UInt32) :=
  paid (growthStore cfg s index grown bytes) cfg.regularOpCost 4
def pagesFrame (frame : CallFrame) (bytes : UInt32) := {frame with locals:=frame.locals.set! 3 (.i32 (growPages bytes))}
def growthFrame (frame : CallFrame) (bytes : UInt32) (memory : Memory) :=
  {pagesFrame frame bytes with locals:=(pagesFrame frame bytes).locals.set! 2 (.i32 (UInt32.ofNat memory.size))}

private theorem rounded_resources (s : Store NearState) (op : Nat) : {rounded s op with host:=s.host}=s := by
  simp only [rounded,after569,bodyAfter569,entered569,DeallocateAlign.after568,DeallocateAlign.entered568,paid,chargedStore]

/-- The actual inner grow block exits through its success branch, without running
its fallback. The memory API equation is about original memory data. -/
theorem wp_grow_attempt (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (bytes : UInt32) (mi : ModuleInst) (address568 address569 index : Nat) (memory grown : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 bytes)) (hs : 4≤frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hi568 : mi.funcAddrs[568]?=some address568)
    (hf568 : s.funcs[address568]?=some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hi569 : mi.funcAddrs[569]?=some address569)
    (hf569 : s.funcs[address569]?=some (.wasm WNear.Binary.AllocateGrowth.signature569 frame.inst WNear.Binary.AllocateGrowth.function569))
    (hbytes : bytes.toNat+65536<2^32) (hold : UInt32.ofNat memory.size≠4294967295)
    (hgrow : memory.grow (growPages bytes).toNat=some grown) (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits (47*cfg.regularOpCost+memoryGrowCost cfg (growPages bytes)+rest))
    (hnext : WP cfg fuel (.next (atCode (growthAfter cfg s index grown bytes) limits base.toArray
      (growthFrame frame bytes memory) callers code)) rest post) :
    WP cfg (fuel+33) (.next (atCode s limits base.toArray frame callers
      (.block .empty (WNear.Binary.AllocateGrowth.growAttempt++WNear.Binary.AllocateGrowth.growFailed)::code)))
      (47*cfg.regularOpCost+memoryGrowCost cfg (growPages bytes)+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (growPages bytes)
  let bf := emptyBlockFrame frame base.length code
  let pf := pagesFrame bf bytes
  let ff := growthFrame frame bytes memory
  let g := growthStore cfg s index grown bytes
  let old := UInt32.ofNat memory.size
  have ffs : 3<frame.locals.size := by omega
  have rFields := congrArg (fun t : Store NearState => (t.modules,t.funcs,t.mems)) (rounded_resources s op)
  simp only at rFields
  have cm : (rounded s op).host.gas.Credits (op+(fee+(4*op+rest))) := by
    exact after569_credits (paid s op 1) op _ (paid_credits s op 1 _ (hc.mono (by simp only [op,fee];omega)))
  have beforeCredits := paid_credits (rounded s op) op 1 (fee+(4*op+rest)) (cm.mono (by omega))
  have cg : g.host.gas.Credits (4*op+rest) :=
    (grownStore_gas cfg (growPages bytes) (beforeGrowth s op) index (4*op+rest) grown beforeCredits).2.2.1
  have brNext : WP cfg fuel (.next (atCode (chargedStore (paid g op 3) cfg.regularOpCost) limits base.toArray ff callers code)) rest post := by
    simpa only [growthAfter,g,op,paid,ff] using hnext
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid g op 3) limits base.toArray ff callers code
    WNear.Binary.AllocateGrowth.growFailed 1 post (by decide) (paid_credits g op 3 _ (cg.mono (by dsimp [op];omega))) brNext
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid g op 2) limits base.toArray
    (growthFrame bf bytes memory) callers (.br_if 0::WNear.Binary.AllocateGrowth.growFailed) .ne old 4294967295 post
    (paid_credits g op 2 _ (cg.mono (by dsimp [op];omega)))
    (by simpa only [ff,bf,growthFrame,pagesFrame,emptyBlockFrame,Numeric.irelop32,Numeric.bool,
      show (old != 4294967295)=true by simpa only [bne_iff_ne] using hold,ite_true,paid,op,List.size_toArray] using branch)
  have constant := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid g op 1) limits (base.toArray.push (.i32 old))
    (growthFrame bf bytes memory) callers (.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed) 4294967295 post
    (paid_credits g op 1 _ (cg.mono (by dsimp [op];omega))) rel
  have tee := wp_local_tee cfg (fuel+3) (op+(op+(op+rest))) g limits base.toArray pf callers
    (.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed) 2 (.i32 old) post
    (cg.mono (by dsimp [op];omega)) (by simpa only [growthFrame,pf,old,paid,op] using constant)
  have grownNext : WP cfg (fuel+4) (.next (atCode g limits (base.toArray.push (.i32 old)) pf callers
      (.local_tee 2::.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed))) (4*op+rest) post := by
    simpa only [show cfg.regularOpCost+(op+(op+(op+rest)))=4*op+rest by dsimp [op];omega] using tee
  have moduleBefore : (beforeGrowth s op).modules[pf.inst]?=some mi := by
    have m := congrArg (fun t : Store NearState => t.modules) (rounded_resources s op)
    simpa only [beforeGrowth,paid,chargedStore,pf,pagesFrame,bf,emptyBlockFrame,m] using hm
  have memoryBefore : (beforeGrowth s op).mems[index]?=some memory := by
    have m := congrArg (fun t : Store NearState => t.mems) (rounded_resources s op)
    simpa only [beforeGrowth,paid,chargedStore,m] using hmem
  have grow := wp_memory_grow cfg (fuel+4) (4*op+rest) (beforeGrowth s op) limits base.toArray pf callers
    (.local_tee 2::.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed)
    (growPages bytes) mi index memory grown post moduleBefore hi memoryBefore hgrow beforeCredits
    (by simpa only [g,growthStore,op,old] using grownNext)
  have pagesNext : WP cfg (fuel+5) (.next (atCode (chargedStore (rounded s op) cfg.regularOpCost) limits
      (base.toArray.push (.i32 (growPages bytes))) pf callers
      (.memory_grow::.local_tee 2::.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed))) (fee+(4*op+rest)) post := by
    simpa only [beforeGrowth,paid,fee,op] using grow
  have teePages := wp_local_tee cfg (fuel+5) (fee+(4*op+rest)) (rounded s op) limits base.toArray bf callers
    (.memory_grow::.local_tee 2::.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed) 3 (.i32 (growPages bytes)) post cm
    (by simpa only [pf,pagesFrame] using pagesNext)
  have checks := checks569 bytes hbytes
  have m1 : (paid s op 1).modules[bf.inst]?=some mi := by simpa only [paid,chargedStore,bf,emptyBlockFrame] using hm
  have f568 : (paid s op 1).funcs[address568]?=some (.wasm WNear.Binary.DeallocateAlign.signature568 bf.inst WNear.Binary.DeallocateAlign.function568) := by simpa only [paid,chargedStore,bf,emptyBlockFrame] using hf568
  have f569 : (paid s op 1).funcs[address569]?=some (.wasm WNear.Binary.AllocateGrowth.signature569 bf.inst WNear.Binary.AllocateGrowth.function569) := by simpa only [paid,chargedStore,bf,emptyBlockFrame] using hf569
  have arr : (base++[Value.i32 bytes]).toArray=base.toArray.push (.i32 bytes) := by apply Array.toList_inj.mp;simp
  have arrResult : (base++[Value.i32 (growPages bytes)]).toArray=base.toArray.push (.i32 (growPages bytes)) := by apply Array.toList_inj.mp;simp
  have call := wp_call569 cfg (fuel+6) (op+(fee+(4*op+rest))) (paid s op 1) limits base bf callers
    (.local_tee 3::.memory_grow::.local_tee 2::.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed)
    bytes mi address568 address569 post m1 hi568 f568 hi569 f569 checks.1 checks.2 hd
    (paid_credits s op 1 _ (hc.mono (by simp only [op,fee];omega)))
    (by simpa only [rounded,growPages,op,Nat.add_assoc,Nat.reduceAdd] using (arrResult ▸ teePages))
  have get := wp_local_get cfg (fuel+31) (41*op+(op+(fee+(4*op+rest)))) s limits base.toArray bf callers
    (.call 569::.local_tee 3::.memory_grow::.local_tee 2::.i32_const 4294967295::.i32_relop .ne::.br_if 0::WNear.Binary.AllocateGrowth.growFailed)
    3 (.i32 bytes) post h3 (hc.mono (by omega)) (by simpa only [arr,paid,op,Nat.add_assoc,Nat.reduceAdd] using call)
  have inner : WP cfg (fuel+32) (.next (atCode s limits base.toArray bf callers
      (WNear.Binary.AllocateGrowth.growAttempt++WNear.Binary.AllocateGrowth.growFailed))) (47*op+fee+rest) post := by
    have cost : cfg.regularOpCost+(41*op+(op+(fee+(4*op+rest))))=47*op+fee+rest := by dsimp [op];omega
    dsimp only [op] at cost
    rw [cost] at get
    simpa only [WNear.Binary.AllocateGrowth.growAttempt,List.cons_append,List.nil_append,op,Nat.add_assoc,Nat.reduceAdd] using get
  have whole := wp_block_empty cfg (fuel+32) (47*op+fee+rest) s limits base.toArray frame callers
    (WNear.Binary.AllocateGrowth.growAttempt++WNear.Binary.AllocateGrowth.growFailed) code post hc (by simpa only [bf,List.size_toArray] using inner)
  simpa only [op,fee,Nat.add_assoc,Nat.reduceAdd] using whole
end WNear.Proofs.AllocateGrowth
