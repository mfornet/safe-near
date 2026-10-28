import Proofs.StateDecodePrefixLeavesWordBody
import Proofs.StateDecodePrefixLeavesRecordCall

/-! Typed accepted765 call returns the original u32 packed with a zero error tag. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32

def wordCallAfter (cfg : WasmConfig) (s : Store NearState) := paid (recordEntered s cfg.regularOpCost) cfg.regularOpCost 16
def wordLeaf (inst height : Nat) (ptr : UInt32) : CallFrame := {locals:=#[.i32 ptr,.i32 4],inst,arity:=1,height,labels:=[],code:=[]}

theorem wordCallAfter_credits (cfg : WasmConfig) (s : Store NearState) (rest : Nat)
    (hc:s.host.gas.Credits (26*cfg.regularOpCost+rest)) : (wordCallAfter cfg s).host.gas.Credits rest := by
  let op:=cfg.regularOpCost
  have c0:=StorePair.charged_credits s op (9*op+(16*op+rest)) (hc.mono (by dsimp[op];omega))
  have c1:=StorePair.charged_credits (chargedStore s op) (9*op) (16*op+rest) c0
  exact paid_credits (recordEntered s op) op 16 rest c1

private theorem modules_entered (s : Store NearState) (op : Nat) : (recordEntered s op).modules=s.modules:=rfl
private theorem mems_entered (s : Store NearState) (op : Nat) : (recordEntered s op).mems=s.mems:=rfl

theorem wp_call_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (ptr : UInt32) (mi : ModuleInst) (i address : Nat) (m : Memory) (post : Post)
    (hm:s.modules[frame.inst]?=some mi) (hfi:mi.funcAddrs[765]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.wordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.wordFunction))
    (hi:mi.memAddrs[0]?=some i) (he:s.mems[i]?=some m) (hb:ptr.toNat+4≤m.byteSize)
    (hd:callers.length+1<limits.maxCallDepth) (hc:s.host.gas.Credits (26*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (wordCallAfter cfg s) limits (base++[Value.i64 (packedWord (readI32 m ptr.toNat))]).toArray frame callers code)) rest post) :
    WP cfg (fuel+21) (.next (atCode s limits (base++[Value.i32 ptr,.i32 4]).toArray frame callers (.call 765::code)))
      (26*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=recordEntered s op
  let leaf:=wordLeaf frame.inst base.length ptr
  let saved:={frame with code}
  let result:=packedWord (readI32 m ptr.toNat)
  have c0:=StorePair.charged_credits s op (9*op+(16*op+rest)) (hc.mono (by dsimp[op];omega))
  have ca:=StorePair.charged_credits (chargedStore s op) (9*op) (16*op+rest) c0
  have cf:=wordCallAfter_credits cfg s rest hc
  have leaveNext:WP cfg fuel (.next (atCode (wordCallAfter cfg s) limits (base++[Value.i64 result]).toArray saved callers saved.code)) rest post:=by
    simpa only[saved,atCode,result] using hn
  have leave:=wp_leave_wasm cfg fuel rest (wordCallAfter cfg s) limits base [.i64 result] (wordFrame leaf m ptr) saved callers post rfl rfl rfl cf leaveNext
  have arr:(base++[Value.i64 result]).toArray=base.toArray.push (.i64 result):=by apply Array.toList_inj.mp;simp
  have bn:WP cfg (fuel+1) (.next (atCode (paid active op 16) limits (base.toArray.push (.i64 result)) (wordFrame leaf m ptr) (saved::callers) [])) rest post:=by
    simpa only[wordCallAfter,active,op,arr] using leave
  have mh:active.modules[leaf.inst]?=some mi:=by rw[modules_entered];exact hm
  have eh:active.mems[i]?=some m:=by rw[mems_entered];exact he
  have body:=wp_word_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] ptr mi i m post rfl rfl (by simp[leaf,wordLeaf]) mh hi eh hb ca bn
  have activationEq:activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodePrefixLeaves.wordFunction [.i32 ptr,.i32 4])=9*op:=
    WNear.Binary.StateDecodePrefixLeaves.activation765 cfg ptr 4
  have cc:s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.StateDecodePrefixLeaves.wordFunction [.i32 ptr,.i32 4])+(16*op+rest))):=by
    rw[activationEq]
    exact hc.mono (by dsimp[op];omega)
  have call:=wp_call_wasm cfg (fuel+20) (16*op+rest) s limits base [.i32 ptr,.i32 4] frame callers code 765 address mi
    WNear.Binary.StateDecodePrefixLeaves.wordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.wordFunction post hm hfi hf rfl hd cc
  rw[activationEq] at call
  have actual:WP cfg (fuel+20) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateDecodePrefixLeaves.wordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.wordFunction [.i32 ptr,.i32 4])) (16*op+rest) post:=by
    simpa [WNear.Binary.StateDecodePrefixLeaves.wordFunction,WNear.Binary.StateDecodePrefixLeaves.wordSignature,leaf,wordLeaf,
      wasmCallee,wasmLocals,atCode,saved,op] using body
  have proof:=call actual
  simpa only[show fuel+20+1=fuel+21 by omega,show cfg.regularOpCost+(9*op+(16*op+rest))=26*cfg.regularOpCost+rest by dsimp[op];omega] using proof
end WNear.Proofs.StateDecodePrefixLeaves
