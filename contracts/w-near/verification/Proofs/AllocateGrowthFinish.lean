import Proofs.AllocateGrowthCommitFrame
import NearVM.MeteredRules

/-! Opaque-prestore commit/return capsule for f577's successful growth branch. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def finishStore (s : Store NearState) (op index : Nat) (memory : Memory) (record oldPages bytes : UInt32) :=
  recordStore (freshStore s op index memory (pageBytes oldPages) bytes) op index
    (freshMemory memory (pageBytes oldPages) bytes) record (pageBytes oldPages)

theorem wp_finish (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (record oldPages bytes : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 record)) (h2 : frame.locals[2]?=some (.i32 oldPages))
    (h4 : frame.locals[4]?=some (.i32 bytes)) (hs : 5≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hheader : (pageBytes oldPages).toNat+12≤memory.byteSize) (hrecord : record.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (25*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (finishStore s cfg.regularOpCost index memory record oldPages bytes) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+26) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.length WNear.Binary.AllocateGrowth.recordReturn) (caller::callers) WNear.Binary.AllocateGrowth.freshHeader))
      (25*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let header := pageBytes oldPages
  let fresh := freshStore s op index memory header bytes
  let ff := freshFrame frame header
  have specs := freshMemory_spec memory header bytes hw hheader
  have cm := (freshStore_gas s op index memory header bytes (7*op+rest) (hc.mono (by dsimp [op];omega))).2.2
  have fields := freshStore_frame s op index memory header bytes
  have module : fresh.modules[ff.inst]?=some mi := by simpa only [fresh,ff,freshFrame,fields.2.1] using hm
  have memoryEq := freshStore_memory s op index memory header bytes hmem
  have ff0 : ff.locals[0]?=some (.i32 record) := by simpa [ff,freshFrame] using h0
  have ff2 : ff.locals[2]?=some (.i32 header) := by simp [ff,freshFrame,show 2<frame.locals.size by omega]
  have ff3 : ff.locals[3]?=some (.i32 0) := by simp [ff,freshFrame,show 3<frame.locals.size by omega]
  have next : WP cfg fuel (.next (atCode (recordStore fresh op index (freshMemory memory header bytes) record header) limits base.toArray caller callers caller.code)) rest post := by
    simpa only [finishStore,fresh,header,op] using hnext
  have ret := wp_record_return cfg fuel rest fresh limits base ff caller callers [] record header mi index (freshMemory memory header bytes) post
    ff0 ff2 ff3 (by simpa only [ff,freshFrame] using ha) (by simpa only [ff,freshFrame] using hh) module hi memoryEq specs.1 (by rw [specs.2.1];exact hrecord) cm next
  let label : Label := ⟨0,base.length,WNear.Binary.AllocateGrowth.recordReturn,none⟩
  have ending := wp_end_label cfg (fuel+7) (7*op+rest) fresh limits base.toArray ff (caller::callers) label post cm
    (by simpa only [label,List.append_nil,op] using ret)
  have freshNext : WP cfg (fuel+8) (.next (atCode fresh limits base.toArray
      (freshFrame (emptyBlockFrame frame base.length WNear.Binary.AllocateGrowth.recordReturn) header) (caller::callers) [])) (7*op+rest) post := by
    simpa only [ff,freshFrame,emptyBlockFrame,label,Nat.add_assoc,Nat.reduceAdd] using ending
  have full := wp_fresh_header cfg (fuel+8) (7*op+rest) s limits base.toArray
    (emptyBlockFrame frame base.length WNear.Binary.AllocateGrowth.recordReturn) (caller::callers) [] oldPages bytes mi index memory post
    h2 h4 hs hm hi hmem hw hheader (hc.mono (by dsimp [op];omega)) freshNext
  have cost : 18*cfg.regularOpCost+(7*op+rest)=25*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,List.append_nil,Nat.add_assoc,Nat.reduceAdd] using full
end WNear.Proofs.AllocateGrowth
