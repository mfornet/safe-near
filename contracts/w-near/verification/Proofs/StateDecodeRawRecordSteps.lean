import Binary.StateDecodeRaw
import Proofs.AllocateRecordSteps
import Proofs.AllocateRecordResources
import Proofs.AllocateRecordGas

/-! Actual f770 uses the same high-length-first, low-pointer-second six stores as f689. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

/-- Arguments are length then pointer, matching local slots1 and2 of f770. -/
def recordStore (s : Store NearState) (op index : Nat) (memory : Memory) (out size pointer : UInt32) :=
  AllocateRecord.recordStore s op index memory out pointer size

theorem wp_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory) (out size pointer : UInt32) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 size))
    (h2 : frame.locals[2]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordStore s cfg.regularOpCost index memory out size pointer)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeRaw.recordWrites++code))) (6*cfg.regularOpCost+rest) post := by
  simpa only [WNear.Binary.StateDecodeRaw.recordWrites,WNear.Binary.AllocateRecord.record] using
    AllocateRecord.wp_record cfg fuel rest s limits stack frame callers code mi index memory out pointer size post
      h0 h1 h2 hm hi hmem hw hb hc hnext

theorem recordStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out size pointer : UInt32)
    (hm : s.mems[index]?=some memory) :
    (recordStore s op index memory out size pointer).mems[index]?=
      some (writeI32 (writeI32 memory (out.toNat+4) size) out.toNat pointer) :=
  AllocateRecord.recordStore_memory s op index memory out pointer size hm

theorem recordStore_gas (s : Store NearState) (op index : Nat) (memory : Memory) (out size pointer : UInt32) :
    AllocateSearch.GasUnits s (recordStore s op index memory out size pointer) op 6 :=
  AllocateRecord.recordStore_gas s op index memory out pointer size
end WNear.Proofs.StateDecodeRaw
