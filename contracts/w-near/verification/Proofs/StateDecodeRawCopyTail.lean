import Proofs.StateDecodeRawCopyState
import Proofs.InterfaceStack

/-! The actual f769 low-then-high copies use their sequential memories, then
restore the sixteen-byte shadow stack. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def copyLowMemory (memory : Memory) (source out : UInt32) :=
  writeI32 memory out.toNat (readI32 memory (source.toNat+8))
def lowCopyStore (s : Store NearState) (op index : Nat) (memory : Memory) (source out : UInt32) :=
  PanicAllocateCopy.copyStore s op index 8 0 source out memory
def highCopyStore (s : Store NearState) (op index : Nat) (memory : Memory) (source out : UInt32) :=
  PanicAllocateCopy.copyStore (lowCopyStore s op index memory source out) op index 12 4 source out (copyLowMemory memory source out)
def copyTailAfter (s : Store NearState) (op index gi : Nat) (memory : Memory) (source out : UInt32) :=
  setGlobal (paid (highCopyStore s op index memory source out) op 4) gi (.i32 (source+16))
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_copy_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (source out : UInt32) (mi : ModuleInst) (index gi : Nat) (memory : Memory) (global : GlobalInst) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h3 : frame.locals[3]?=some (.i32 source))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hgi : mi.globalAddrs[0]?=some gi)
    (hmem : s.mems[index]?=some memory) (hg : s.globals[gi]?=some global)
    (hw : memory.wf) (hbS : source.toNat+16≤memory.byteSize) (hbO : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copyTailAfter s cfg.regularOpCost index gi memory source out)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeRaw.lowCopy++WNear.Binary.StateDecodeRaw.highCopy++WNear.Binary.StateDecodeRaw.restore 3 16++code)))
      (12*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let low:=lowCopyStore s op index memory source out
  let high:=highCopyStore s op index memory source out
  have cl:low.host.gas.Credits (8*op+rest):=PanicAllocateCopy.copyStore_credits s op index 8 0 _ source out memory (hc.mono (by dsimp[op];omega))
  have ch:high.host.gas.Credits (4*op+rest):=PanicAllocateCopy.copyStore_credits low op index 12 4 _ source out (copyLowMemory memory source out) (cl.mono (by omega))
  have lm:low.mems[index]?=some (copyLowMemory memory source out):=by
    unfold low lowCopyStore PanicAllocateCopy.copyStore copyLowMemory
    apply storeI32_memory
    rw[mems_paid];exact hmem
  have lmod:low.modules[frame.inst]?=some mi:=by
    unfold low lowCopyStore PanicAllocateCopy.copyStore
    rw[storeI32_modules,modules_paid];exact hm
  have hmod:high.modules[frame.inst]?=some mi:=by
    unfold high highCopyStore PanicAllocateCopy.copyStore
    rw[storeI32_modules,modules_paid];exact lmod
  have hg':high.globals[gi]?=some global:=by
    unfold high highCopyStore lowCopyStore PanicAllocateCopy.copyStore
    rw[storeI32_globals,globals_paid,storeI32_globals,globals_paid];exact hg
  have shape:=writeI32_spec memory out.toNat (readI32 memory (source.toNat+8)) hw (by omega)
  have restore:=InterfaceStack.wp_restore cfg fuel rest high limits stack frame callers code mi gi global source 3 16 post
    h3 hmod hgi hg' ch hnext
  have upper:=PanicAllocateCopy.wp_copy cfg (fuel+4) (4*op+rest) low limits stack frame callers (WNear.Binary.StateDecodeRaw.restore 3 16++code)
    3 0 12 4 source out mi index (copyLowMemory memory source out) post h3 h0 lmod hi lm
    (by rw[show (copyLowMemory memory source out).byteSize=memory.byteSize from shape.2.1];exact hbS)
    (by rw[show (copyLowMemory memory source out).byteSize=memory.byteSize from shape.2.1];exact hbO)
    (cl.mono (by omega)) restore
  have lower:=PanicAllocateCopy.wp_copy cfg (fuel+8) (4*op+(4*op+rest)) s limits stack frame callers
    (WNear.Binary.StateDecodeRaw.highCopy++WNear.Binary.StateDecodeRaw.restore 3 16++code)
    3 0 8 0 source out mi index memory post h3 h0 hm hi hmem (by omega) (by omega)
    (hc.mono (by dsimp[op];omega))
    (by simpa only[low,lowCopyStore,op,WNear.Binary.StateDecodeRaw.highCopy,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using upper)
  simpa only[WNear.Binary.StateDecodeRaw.lowCopy,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4*cfg.regularOpCost+(4*op+(4*op+rest))=12*cfg.regularOpCost+rest by dsimp[op];omega] using lower
end WNear.Proofs.StateDecodeRaw
