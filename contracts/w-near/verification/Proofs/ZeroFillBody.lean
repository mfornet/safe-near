import Proofs.ZeroFillStart
import Proofs.ZeroFillFrame

/-! Complete actual symbolic f952 body, including both normal label endings. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode loopAfter loopFrameAfter iterationStore written
set_option maxRecDepth 16384

def positiveStart (s : Store NearState) (op : Nat) := chargedStore (paid s op 5) op
def positiveAfter (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :=
  paid (loopAfter (positiveStart s op) op index memory ptr value len len.toNat) op 1
def positiveFrame (frame : CallFrame) (ptr len : UInt32) := loopFrameAfter (startFrame frame ptr) ptr len len.toNat

def bodyCost (len : UInt32) := if len=0 then 4 else 13*len.toNat+6
def bodySteps (len : UInt32) := if len=0 then 5 else 12*len.toNat+10
def after (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :=
  if len=0 then paid s op 4 else positiveAfter s op index memory ptr value len
def finalFrame (frame : CallFrame) (ptr len : UInt32) := if len=0 then frame else positiveFrame frame ptr len

private theorem loopFrame_block (frame : CallFrame) (ptr count : UInt32) (n height : Nat) (code : Expr) :
    loopFrameAfter (emptyBlockFrame frame height code) ptr count n = emptyBlockFrame (loopFrameAfter frame ptr count n) height code := by
  induction n generalizing frame ptr count with
  | zero => simp only [loopFrameAfter]
  | succ n ih =>
    simp only [loopFrameAfter]
    have eq : iterationFrame (emptyBlockFrame frame height code) ptr count = emptyBlockFrame (iterationFrame frame ptr count) height code := rfl
    rw [eq,ih]

 theorem wp_body_positive (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr value len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 ptr)) (h1 : frame.locals[1]? = some (.i32 value)) (h2 : frame.locals[2]? = some (.i32 len)) (hs : 4≤frame.locals.size)
    (hn : len≠0) (hm : s.modules[frame.inst]? = some  mi) (hi : mi.memAddrs[0]? = some  index) (hmem : s.mems[index]? = some  memory)
    (hw : memory.wf) (hb : ptr.toNat+len.toNat≤memory.byteSize) (hwidth : ptr.toNat+len.toNat≤2^32)
    (hc : s.host.gas.Credits ((13*len.toNat+6)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (positiveAfter s cfg.regularOpCost index memory ptr value len) limits
      (stack.push (.i32 ptr)) (positiveFrame frame ptr len) callers code)) rest post) :
    WP cfg (fuel+12*len.toNat+10) (.next (atCode s limits stack frame callers (WNear.Binary.ZeroFill.body++code)))
      ((13*len.toNat+6)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let n := len.toNat
  have z : len.toNat≠0 := by
    intro h
    apply hn
    exact UInt32.toNat_inj.mp h
  have np : 0<n := by dsimp [n]; omega
  have costCount : loopCost n+7=13*n+6 := by simp only [loopCost,ite_eq_right (by omega : ¬n=0)];omega
  have cost : 5*op+(op+(loopCost n*op+(op+rest)))=(13*n+6)*cfg.regularOpCost+rest := by
    rw [←costCount];simp only [Nat.add_mul];dsimp [op];omega
  let bf := emptyBlockFrame frame stack.size (.local_get 0::code)
  let sf := startFrame frame ptr
  let start := positiveStart s op
  let finish := loopAfter start op index memory ptr value len n
  let ff := positiveFrame frame ptr len
  have cs : start.host.gas.Credits (loopCost n*op+(op+rest)) := by
    have c5 := paid_credits s op 5 (op+(loopCost n*op+(op+rest))) (hc.mono (by rw [cost]; exact Nat.le_refl _))
    exact StorePair.charged_credits (paid s op 5) op _ c5
  have cf : finish.host.gas.Credits (op+rest) := loopAfter_credits start op index (op+rest) memory ptr value len n cs
  have ff0 : ff.locals[0]? = some (.i32 ptr) := by
    have h := (loopFrameAfter_shape sf ptr len n).2.2.2.2.1
    simpa only [ff,positiveFrame,sf,startFrame] using h.trans (by simpa [sf,startFrame] using h0)
  have getNext : WP cfg fuel (.next (atCode (chargedStore finish cfg.regularOpCost) limits (stack.push (.i32 ptr)) ff callers code)) rest post := by
    simpa only [positiveAfter,finish,start,n,op,paid,ff] using hnext
  have get := wp_local_get cfg fuel rest finish limits stack ff callers code 0 (.i32 ptr) post ff0 cf getNext
  let outerLabel : Label := ⟨0,stack.size,.local_get 0::code,none⟩
  have endBlock := wp_end_label cfg (fuel+1) (op+rest) finish limits stack ff callers outerLabel post cf get
  let loopLabel : Label := ⟨0,stack.size,[],some WNear.Binary.ZeroFill.loopBody⟩
  have endLoop := wp_end_label cfg (fuel+2) (op+rest) finish limits stack (emptyBlockFrame ff stack.size (.local_get 0::code)) callers loopLabel post cf
    (by simpa only [emptyBlockFrame,outerLabel] using endBlock)
  have ln : WP cfg (fuel+3) (.next (atCode (loopAfter start op index memory ptr value len n) limits stack
      (emptyLoopFrame (loopFrameAfter (startFrame bf ptr) ptr len n) stack.size WNear.Binary.ZeroFill.loopBody []) callers [])) (op+rest) post := by
    have initEq : startFrame bf ptr=emptyBlockFrame sf stack.size (.local_get 0::code) := rfl
    rw [initEq,loopFrame_block]
    simpa only [emptyLoopFrame,emptyBlockFrame,loopLabel,ff,positiveFrame,sf,n,finish,Nat.add_assoc,Nat.reduceAdd] using endLoop
  have sf1 : (startFrame bf ptr).locals[1]? = some (.i32 value) := by simpa [startFrame,bf,emptyBlockFrame] using h1
  have sf2 : (startFrame bf ptr).locals[2]? = some (.i32 len) := by simpa [startFrame,bf,emptyBlockFrame] using h2
  have sf3 : (startFrame bf ptr).locals[3]? = some (.i32 ptr) := by simp [startFrame,bf,emptyBlockFrame,show 3<frame.locals.size by omega]
  have sfs : 4≤(startFrame bf ptr).locals.size := by simpa [startFrame,bf,emptyBlockFrame] using hs
  have moduleStart : start.modules[(startFrame bf ptr).inst]? = some  mi := by simpa only [start,positiveStart,paid,chargedStore,startFrame,bf,emptyBlockFrame] using hm
  have memoryStart : start.mems[index]? = some  memory := by simpa only [start,positiveStart,paid,chargedStore] using hmem
  have loopProof := wp_loop_positive cfg n (fuel+3) (op+rest) start limits stack (startFrame bf ptr) callers [] ptr value len mi index memory post np rfl sf1 sf2 sf3 sfs moduleStart hi memoryStart hw hb hwidth cs ln
  have loopNext : WP cfg (fuel+3+12*n) (.next (atCode (chargedStore (paid s op 5) cfg.regularOpCost) limits stack
      (emptyLoopFrame (startFrame bf ptr) stack.size WNear.Binary.ZeroFill.loopBody []) callers WNear.Binary.ZeroFill.loopBody)) (loopCost n*op+(op+rest)) post := by
    simpa only [start,positiveStart,op] using loopProof
  have entry := wp_loop_empty cfg (fuel+3+12*n) (loopCost n*op+(op+rest)) (paid s op 5) limits stack (startFrame bf ptr) callers WNear.Binary.ZeroFill.loopBody [] post
    (paid_credits s op 5 _ (hc.mono (by rw [cost]; exact Nat.le_refl _))) loopNext
  have startNext : WP cfg (fuel+3+12*n+1) (.next (atCode (paid s op 5) limits stack (startFrame bf ptr) callers [.loop .empty WNear.Binary.ZeroFill.loopBody]))
      (op+(loopCost n*op+(op+rest))) post := by simpa only [op] using entry
  have headProof := wp_start_positive cfg (fuel+3+12*n+1) (op+(loopCost n*op+(op+rest))) s limits stack bf callers [.loop .empty WNear.Binary.ZeroFill.loopBody] ptr len post h0 h2 hn
    (hc.mono (by rw [cost]; exact Nat.le_refl _)) startNext
  have headNext : WP cfg (fuel+3+12*n+1+5) (.next (atCode s limits stack bf callers WNear.Binary.ZeroFill.guarded))
      ((13*n+6)*cfg.regularOpCost+rest) post := by
    simpa only [WNear.Binary.ZeroFill.guarded,List.append_eq,List.cons_append,List.nil_append,cost,op] using headProof
  have result := wp_block_empty cfg (fuel+3+12*n+1+5) ((13*n+6)*cfg.regularOpCost+rest) s limits stack frame callers WNear.Binary.ZeroFill.guarded (.local_get 0::code) post hc headNext
  have fuelEq : fuel+3+12*n+1+5+1=fuel+12*len.toNat+10 := by dsimp [n]; omega
  rw [fuelEq] at result
  simpa only [WNear.Binary.ZeroFill.body,List.append_eq,List.cons_append,List.nil_append,n] using result

/-- Complete symbolic memset body, with no specialisation of pointer, byte or count. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr value len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 ptr)) (h1 : frame.locals[1]? = some (.i32 value))
    (h2 : frame.locals[2]? = some (.i32 len)) (hs : 4≤frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hw : memory.wf) (hb : ptr.toNat+len.toNat≤memory.byteSize) (hwidth : ptr.toNat+len.toNat≤2^32)
    (hc : s.host.gas.Credits (bodyCost len*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory ptr value len) limits
      (stack.push (.i32 ptr)) (finalFrame frame ptr len) callers code)) rest post) :
    WP cfg (fuel+bodySteps len) (.next (atCode s limits stack frame callers (WNear.Binary.ZeroFill.body++code)))
      (bodyCost len*cfg.regularOpCost+rest) post := by
  by_cases hz : len=0
  · subst len
    simpa only [bodyCost,bodySteps,after,finalFrame,ite_true] using
      wp_body_zero cfg fuel rest s limits stack frame callers code ptr post h0 h2 hc hnext
  · simp only [bodyCost,bodySteps,after,finalFrame,ite_eq_right hz] at hc hnext ⊢
    exact wp_body_positive cfg fuel rest s limits stack frame callers code ptr value len mi index memory post h0 h1 h2 hs hz hm hi hmem hw hb hwidth hc hnext

/-- Residual gas for the exact deterministic body store. -/
theorem after_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (ptr value len : UInt32)
    (hc : s.host.gas.Credits (bodyCost len*op+rest)) :
    (after s op index memory ptr value len).host.gas.Credits rest := by
  by_cases hz : len=0
  · simpa only [after,bodyCost,ite_eq_left hz] using paid_credits s op 4 rest (by simpa only [bodyCost,ite_eq_left hz] using hc)
  · have np : 0<len.toNat := by
      have nz : len.toNat≠0 := by intro h; apply hz; exact UInt32.toNat_inj.mp h
      omega
    have costCount : loopCost len.toNat+7=13*len.toNat+6 := by
      simp only [loopCost,ite_eq_right (by omega : ¬len.toNat=0)]; omega
    have cost : 5*op+(op+(loopCost len.toNat*op+(1*op+rest)))=bodyCost len*op+rest := by
      simp only [bodyCost,ite_eq_right hz]
      rw [←costCount]
      simp only [Nat.add_mul]
      omega
    have first := paid_credits s op 5 (op+(loopCost len.toNat*op+(1*op+rest))) (hc.mono (by rw [cost]; exact Nat.le_refl _))
    have entered := StorePair.charged_credits (paid s op 5) op _ first
    have loop := loopAfter_credits (positiveStart s op) op index (1*op+rest) memory ptr value len len.toNat entered
    simpa only [after,ite_eq_right hz,positiveAfter] using paid_credits _ op 1 rest loop

end WNear.Proofs.ZeroFill
