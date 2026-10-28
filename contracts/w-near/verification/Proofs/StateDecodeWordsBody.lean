import Proofs.StateDecodeWordsCopy

/-! Complete actual accepted fixed-width word-reader bodies. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode lowStore highStore copyAfter

def width (wide : Bool) : UInt32 := if wide then 16 else 8
def widthNat (wide : Bool) : Nat := if wide then 16 else 8
def finalFrame (frame : CallFrame) := flagFrame (flagFrame frame 1) 0

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

private theorem copy_shape (wide : Bool) (m : Memory) (out source : UInt32)
    (hwf : m.wf) (ho : out.toNat+(widthNat wide+1)≤m.byteSize) (hwidth : m.byteSize≤2^32) :
    (copiedMemory wide m out source).wf ∧ (copiedMemory wide m out source).byteSize=m.byteSize := by
  cases wide
  · have h := writeI64_spec m (out.toNat+1) (readI64 m source.toNat) hwf (by simpa only [widthNat,ite_false,Bool.false_eq_true] using ho)
    exact ⟨h.1,h.2.1⟩
  · have span : out.toNat+17≤m.byteSize := ho
    have ha : (out+9).toNat=out.toNat+9 := by
      rw [UInt32.toNat_add];simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
      exact Nat.mod_eq_of_lt (by omega)
    have h := copiedMemory_spec true m out source hwf span ha
    exact ⟨h.1,h.2.1⟩

theorem wp_body (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[1]?=some (.i32 source))
    (h2 : frame.locals[2]?=some (.i32 (width wide))) (hn : 4≤frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hwf : memory.wf) (hb : source.toNat+widthNat wide≤memory.byteSize)
    (hw : out.toNat+(widthNat wide+1)≤memory.byteSize) (hwidth : memory.byteSize≤2^32)
    (hc : s.host.gas.Credits (bodyCost wide*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after wide s cfg.regularOpCost index memory out source)
      limits stack (finalFrame frame) callers code)) rest post) :
    WP cfg (fuel+bodySteps wide) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeWords.body wide++code)))
      (bodyCost wide*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let c:=copyCost wide
  let initial:=paid s op 2
  let beforeCopy:=paid s op 6
  let copied:=copyAfter wide beforeCopy op index memory out source
  let reset:=paid copied op 2
  let f1:=flagFrame frame 1
  let f0:=finalFrame frame
  let bf:=emptyBlockFrame f1 stack.size (WNear.Binary.StateDecodeWords.status++code)
  have cut : 6*op+(copyCost wide*op+(5*op+rest))≤bodyCost wide*cfg.regularOpCost+rest := by
    simp only [bodyCost,Nat.add_mul]
    dsimp [op]
    omega
  have cb : beforeCopy.host.gas.Credits (copyCost wide*op+(5*op+rest)) :=
    paid_credits s op 6 _ (hc.mono cut)
  have co : copied.host.gas.Credits (5*op+rest) := copyAfter_credits wide beforeCopy op index (5*op+rest) memory out source cb
  have rs : reset.host.gas.Credits (3*op+rest) := paid_credits copied op 2 _ (co.mono (by omega))
  have cm : copied.mems[index]?=some (copiedMemory wide memory out source) := copyAfter_memory wide beforeCopy op index memory out source (by rw [mems_paid];exact hmem)
  have mm : reset.mems[index]?=some (copiedMemory wide memory out source) := by rw [mems_paid];exact cm
  have md : reset.modules[frame.inst]?=some mi := by
    rw [modules_paid,copyAfter_modules,modules_paid];exact hm
  have shape := copy_shape wide memory out source hwf hw hwidth
  have outB : out.toNat+1≤(copiedMemory wide memory out source).byteSize := by
    rw [shape.2]
    have positive : 0<widthNat wide := by cases wide <;> decide
    omega
  have l0 : f0.locals[0]?=some (.i32 out) := by simpa [f0,finalFrame,flagFrame] using ho
  have l3 : f0.locals[3]?=some (.i32 0) := by simp [f0,finalFrame,flagFrame,show 3<frame.locals.size by omega]
  have status := wp_status cfg fuel rest reset limits stack f0 callers code out mi index (copiedMemory wide memory out source) post
    l0 l3 md hi mm outB rs hnext
  let label : Label := {arity:=0,height:=stack.size,loop:=none,rest:=WNear.Binary.StateDecodeWords.status++code}
  have ended := wp_end_label cfg (fuel+3) (3*op+rest) reset limits stack f0 callers label post rs status
  have resetNext : WP cfg (fuel+4) (.next (atCode reset limits stack (flagFrame bf 0) callers [])) (3*op+rest) post := by
    simpa only [f0,finalFrame,f1,bf,emptyBlockFrame,flagFrame,label] using ended
  have set0 := wp_set_flag cfg (fuel+4) (3*op+rest) copied limits stack bf callers [] 0 post (co.mono (by dsimp[op];omega)) resetNext
  have o1 : bf.locals[0]?=some (.i32 out) := by simpa [bf,emptyBlockFrame,f1,flagFrame] using ho
  have s1 : bf.locals[1]?=some (.i32 source) := by simpa [bf,emptyBlockFrame,f1,flagFrame] using hs
  have m0 : beforeCopy.modules[bf.inst]?=some mi := by rw [modules_paid];exact hm
  have mem0 : beforeCopy.mems[index]?=some memory := by rw [mems_paid];exact hmem
  have ha : wide=true → (out+9).toNat=out.toNat+9 := by
    intro he;subst wide
    rw [UInt32.toNat_add];simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    change out.toNat+17≤memory.byteSize at hw
    omega
  have hp : wide=true → (source+8).toNat=source.toNat+8 := by
    intro he;subst wide
    rw [UInt32.toNat_add];simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    change source.toNat+16≤memory.byteSize at hb
    omega
  have cp := wp_copy wide cfg (fuel+6) (5*op+rest) beforeCopy limits stack bf callers (WNear.Binary.StateDecodeWords.setFlag 0)
    out source mi index memory post o1 s1 m0 hi mem0 hwf hb (by cases wide <;> simpa [widthNat] using hw) ha hp
    (paid_credits s op 6 _ (hc.mono (by dsimp[beforeCopy,c,op];simp only [bodyCost,Nat.add_mul];omega)))
    (by simpa only [List.append_nil,copied,op,Nat.add_assoc,Nat.reduceAdd,show 2*cfg.regularOpCost+(3*cfg.regularOpCost+rest)=5*cfg.regularOpCost+rest by omega] using set0)
  have hlen : bf.locals[2]?=some (.i32 (width wide)) := by simpa [bf,emptyBlockFrame,f1,flagFrame] using h2
  have gd := wp_guard cfg (fuel+6+c) (c*op+(5*op+rest)) initial limits stack bf callers
    (WNear.Binary.StateDecodeWords.low++(if wide then WNear.Binary.StateDecodeWords.high else [])++WNear.Binary.StateDecodeWords.setFlag 0)
    (width wide) post hlen (paid_credits s op 2 _ (hc.mono (by dsimp[c,op];simp only [bodyCost,Nat.add_mul];omega)))
    (by simpa only [initial,beforeCopy,c,op,ValueReturnBorrow.paid_add] using cp)
  have fuelG : fuel+6+c+4=fuel+10+c := by omega
  have costG : 4*cfg.regularOpCost+(c*op+(5*op+rest))=(c+9)*op+rest := by dsimp[op];simp only[Nat.add_mul];omega
  have block := wp_block_empty cfg (fuel+10+c) ((c+9)*op+rest) initial limits stack f1 callers
    (WNear.Binary.StateDecodeWords.guard (width wide)++WNear.Binary.StateDecodeWords.low++
      (if wide then WNear.Binary.StateDecodeWords.high else [])++WNear.Binary.StateDecodeWords.setFlag 0)
    (WNear.Binary.StateDecodeWords.status++code) post
    (paid_credits s op 2 _ (hc.mono (by dsimp[c,op];simp only [bodyCost,Nat.add_mul];omega)))
    (by simpa only [bf,List.append_assoc,fuelG,costG] using gd)
  have fuelB : fuel+10+c+1=fuel+11+c := by omega

  have init := wp_set_flag cfg (fuel+11+c) ((c+9)*op+rest) s limits stack frame callers
    ([.block .empty (WNear.Binary.StateDecodeWords.guard (width wide)++WNear.Binary.StateDecodeWords.low++
      (if wide then WNear.Binary.StateDecodeWords.high else [])++WNear.Binary.StateDecodeWords.setFlag 0)]++WNear.Binary.StateDecodeWords.status++code) 1 post
    (hc.mono (by dsimp[c,op];simp only [bodyCost,Nat.add_mul];omega))
    (by simpa only [initial,f1,op,List.singleton_append,List.cons_append,List.nil_append,fuelB] using block)
  have fuelI : fuel+11+c+2=fuel+bodySteps wide := by dsimp[c,bodySteps,bodyCost];omega
  have costI : 2*cfg.regularOpCost+((c+9)*op+rest)=bodyCost wide*cfg.regularOpCost+rest := by dsimp[c,op,bodyCost];simp only[Nat.add_mul];omega
  simpa only [WNear.Binary.StateDecodeWords.body,width,List.append_assoc,fuelI,costI] using init

end WNear.Proofs.StateDecodeWords
