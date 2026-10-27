import Proofs.DeallocateCoreState

/-! Header-mark adapter using a named native header address. -/
namespace WNear.Proofs.DeallocateCore
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def markedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 p.header)}
def savedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 4 (.i32 (oldHead p))}
def headFrame (frame : CallFrame) (p : Layout) := markedFrame (savedFrame frame p) p

/-- Actual nine instructions, with the header calculation linked by a primitive
word equation, avoid evaluating a wrapping address inside memory expressions. -/
theorem wp_mark_at (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hp : frame.locals[1]? = some (.i32 p.pointer)) (hs : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (he : p.pointer + 4294967288 = p.header) (hb : p.header.toNat + 4 ≤ p.memory.byteSize)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 9) p.memoryIndex p.header.toNat
      p.memory (readI32 p.memory p.header.toNat &&& 4294967294)) limits stack (markedFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits stack frame callers (WNear.Binary.Deallocate.markFree ++ code)))
      (9 * cfg.regularOpCost + rest) post := by
  have hheader : Deallocate.header p.pointer = p.header := he
  have hn : WP cfg fuel (.next (atCode (Deallocate.markedStore s cfg.regularOpCost p.memoryIndex p.memory p.pointer)
      limits stack (Deallocate.markedFrame frame p.pointer) callers code)) rest post := by
    simpa only [Deallocate.markedStore,Deallocate.markedWord,hheader,Deallocate.markedFrame,markedFrame] using hnext
  exact Deallocate.wp_mark cfg fuel rest s limits stack frame callers code p.pointer p.mi p.memoryIndex p.memory post hp hs hm hi hmem
    (by rw [hheader]; exact hb) hc hn

end WNear.Proofs.DeallocateCore
