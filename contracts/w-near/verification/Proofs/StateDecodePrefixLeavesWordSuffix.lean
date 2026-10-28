import Proofs.StateDecodePrefixLeavesWordSteps
import Proofs.ValueReturnBorrow

namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32

theorem wp_read_pack (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (ptr : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h0:frame.locals[0]?=some (.i32 ptr)) (hsize:2≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi) (hi:mi.memAddrs[0]?=some i) (he:s.mems[i]?=some m) (hb:ptr.toNat+4≤m.byteSize)
    (hc:s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 12) limits
      (stack.push (.i64 (packedWord (readI32 m ptr.toNat)))) (wordFrame frame m ptr) callers code)) rest post) :
    WP cfg (fuel+13) (.next (atCode s limits stack
      (emptyBlockFrame frame stack.size (WNear.Binary.StateDecodePrefixLeaves.pack++code)) callers WNear.Binary.StateDecodePrefixLeaves.read))
      (12*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let w:=readI32 m ptr.toNat
  let f:=wordFrame frame m ptr
  let bs:=paid s op 5
  have f0:f.locals[0]?=some (.i32 w):=by simp[f,w,wordFrame,Array.set!,show 0<frame.locals.size by omega]
  have f1:f.locals[1]?=some (.i32 0):=by simp[f,wordFrame,Array.set!,show 1<frame.locals.size by omega]
  have cr:bs.host.gas.Credits (7*op+rest):=paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  have pn:WP cfg fuel (.next (atCode (paid bs op 7) limits (stack.push (.i64 (packedWord w))) f callers code)) rest post:=by
    simpa only[bs,f,w,op,ValueReturnBorrow.paid_add] using hn
  have pack:=wp_word_pack cfg fuel rest bs limits stack f callers code w post f0 f1 cr pn
  have en:=wp_end_label cfg (fuel+7) (7*op+rest) bs limits stack f callers
    {arity:=0,height:=stack.size,rest:=WNear.Binary.StateDecodePrefixLeaves.pack++code,loop:=none} post cr pack
  let outer:=emptyBlockFrame frame stack.size (WNear.Binary.StateDecodePrefixLeaves.pack++code)
  have rn:WP cfg (fuel+8) (.next (atCode bs limits stack (wordFrame outer m ptr) callers [])) (7*op+rest) post:=by
    simpa only[outer,emptyBlockFrame,wordFrame,f] using en
  have rd:=wp_word_read cfg (fuel+8) (7*op+rest) s limits stack outer callers [] ptr mi i m post h0 hm hi he hb
    (hc.mono (by dsimp[op];omega)) rn
  simpa only[List.append_nil,show 5*cfg.regularOpCost+(7*op+rest)=12*cfg.regularOpCost+rest by dsimp[op];omega] using rd
end WNear.Proofs.StateDecodePrefixLeaves
