import NearVM.MeteredI32MemoryRules
import Binary.StateReadStorageOuter
import Proofs.StorePairCallerState

/-! Actual548 high-length then low-pointer stores, with sequential memory. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode writeI32

def savedWord (s : Store NearState) (op index : Nat) (memory : Memory) (scratch value : UInt32) (offset : Nat) :=
  storeI32 (paid s op 3) index (scratch.toNat+offset) memory value

theorem wp_save_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch value : UInt32) (slot offset : Nat) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hv : frame.locals[slot]?=some (.i32 value))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+offset+4≤memory.byteSize)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (savedWord s cfg.regularOpCost index memory scratch value offset) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get 3::.local_get slot::.store .i32 none {align:=2,offset}::code)))
      (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have st := wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset}
    scratch value mi index memory post hm hi hmem hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hnext
  have get := wp_local_get cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.store .i32 none {align:=2,offset}::code) slot (.i32 value) post hv
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) st
  have first := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.local_get slot::.store .i32 none {align:=2,offset}::code) 3 (.i32 scratch) post h3
    (hc.mono (by dsimp [op];omega)) get
  simpa only [show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp [op];omega] using first

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def savedKey (s : Store NearState) (op index : Nat) (memory : Memory) (scratch key len : UInt32) :=
  savedWord (savedWord s op index memory scratch len 12) op index (writeI32 memory (scratch.toNat+12) len) scratch key 8

theorem wp_save_key (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch key len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (h1 : frame.locals[1]?=some (.i32 key))
    (h2 : frame.locals[2]?=some (.i32 len))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hwf : memory.wf) (hb : scratch.toNat+16≤memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (savedKey s cfg.regularOpCost index memory scratch key len) limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateReadStorageOuter.saveLength++WNear.Binary.StateReadStorageOuter.savePointer++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let one := savedWord s op index memory scratch len 12
  have spec := writeI32_spec memory (scratch.toNat+12) len hwf (by omega)
  have me : one.mems[index]?=some (writeI32 memory (scratch.toNat+12) len) := by
    have mp : (paid s op 3).mems[index]?=some memory := by rw [mems_paid];exact hmem
    exact storeI32_memory (paid s op 3) index (scratch.toNat+12) memory len mp
  have mo : one.modules[frame.inst]?=some mi := by
    simp only [one,savedWord,storeI32_modules,modules_paid];exact hm
  have credits : one.host.gas.Credits (3*op+rest) := by
    simpa only [one,savedWord,storeI32_host] using paid_credits s op 3 (3*op+rest) (hc.mono (by dsimp [op];omega))
  have low := wp_save_word cfg fuel rest one limits stack frame callers code scratch key 1 8 mi index
    (writeI32 memory (scratch.toNat+12) len) post h3 h1 mo hi me (by rw [spec.2.1];omega) credits hnext
  have high := wp_save_word cfg (fuel+3) (3*op+rest) s limits stack frame callers
    (WNear.Binary.StateReadStorageOuter.savePointer++code) scratch len 2 12 mi index memory post h3 h2 hm hi hmem (by omega)
    (hc.mono (by dsimp [op];omega)) low
  simpa only [WNear.Binary.StateReadStorageOuter.saveLength,WNear.Binary.StateReadStorageOuter.savePointer,
    List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp [op];omega] using high

theorem savedKey_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (scratch key len : UInt32)
    (hc : s.host.gas.Credits (6*op+rest)) :
    (savedKey s op index memory scratch key len).host.gas.Credits rest := by
  have first : (savedWord s op index memory scratch len 12).host.gas.Credits (3*op+rest) := by
    simpa only [savedWord,storeI32_host] using paid_credits s op 3 (3*op+rest) (hc.mono (by omega))
  simpa only [savedKey,savedWord,storeI32_host] using
    paid_credits (savedWord s op index memory scratch len 12) op 3 rest first
end WNear.Proofs.StateReadStorageOuter
