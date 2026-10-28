import Binary.StateDecodeRaw
import Proofs.AllocateVectorSteps

/-! f767 snapshots the actual f769 result before either caller output write. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocateVector (loadedFrame)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

def cacheFrame (frame : CallFrame) (memory : Memory) (scratch : UInt32) :=
  loadedFrame (loadedFrame frame 5 (readI32 memory (scratch.toNat+20))) 2 (readI32 memory (scratch.toNat+16))
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_cache (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory) (hb : scratch.toNat+24≤memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack (cacheFrame frame memory scratch) callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeRaw.rawCache++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let ff:=loadedFrame frame 5 (readI32 memory (scratch.toNat+20))
  have h3f : ff.locals[3]?=some (.i32 scratch) := by simp [ff,loadedFrame,h3]
  have mm : (paid s op 3).modules[ff.inst]?=some mi := by rw [paid_modules];simpa only [ff,loadedFrame] using hm
  have me : (paid s op 3).mems[index]?=some memory := by rw [paid_mems];exact hmem
  have low := AllocateVector.wp_load_local cfg fuel rest (paid s op 3) limits stack ff callers code 3 2 16 scratch mi index memory post
    h3f mm hi me (by omega) (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [cacheFrame,ff,paid,op] using hnext)
  have high := AllocateVector.wp_load_local cfg (fuel+3) (3*op+rest) s limits stack frame callers
    ([.local_get 3,.load .i32 none {align:=2,offset:=16},.local_set 2]++code) 3 5 20 scratch mi index memory post
    h3 hm hi hmem (by omega) (hc.mono (by dsimp[op];omega)) low
  simpa only [WNear.Binary.StateDecodeRaw.rawCache,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp[op];omega] using high
end WNear.Proofs.StateDecodeRaw
