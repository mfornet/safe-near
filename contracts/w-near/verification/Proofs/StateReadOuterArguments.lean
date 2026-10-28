import Binary.StateReadOuter
import Proofs.StateReadOuterState
import Proofs.InterfaceStack
import Proofs.StateDecodeBorshWrapperArguments

/-! Actual219 prologue and scalar argument cells, with arbitrary operand prefixes. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_setup(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(post:Post)
    (hm:s.modules[frame.inst]?=some p.mi)(hi:p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg:s.globals[p.globalIndex]?=some p.global219)(hv:p.global219.value=.i32 p.sp219)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (reserved s cfg.regularOpCost p) limits stack (reservedFrame frame p) callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadOuter.setup++code)))
      (5*cfg.regularOpCost+rest) post:=by
  simpa only[WNear.Binary.StateReadOuter.setup,WNear.Binary.StateReadOuter.body,WNear.Binary.StateReadOuter.function,
    reserved,reservedFrame,scratch,List.take_succ_cons,List.take_zero] using
    InterfaceStack.wp_reserve cfg fuel rest s limits stack frame callers code p.mi p.globalIndex p.global219 p.sp219 1 96 post hm hi hg hv hc hnext

def storageArgumentsCode:Expr:=[.local_get 1,.i32_const 8,.i32_binop .add,.i32_const 1049788,.i32_const 5]
theorem storage_arguments_code:WNear.Binary.StateReadOuter.storageArguments=storageArgumentsCode:=by kernel_rfl
theorem wp_storage_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r _out:UInt32)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (r+8))).push (.i32 1049788)).push (.i32 5)) frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (storageArgumentsCode++code)))
      (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  unfold storageArgumentsCode
  rw[show 5*cfg.regularOpCost+rest=op+(4*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+4) _ s limits stack frame callers _ 1 (.i32 r) post h1 (hc.mono (by dsimp[op];omega))
  rw[show 4*op+rest=op+(3*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s op 1) limits (stack.push (.i32 r)) frame callers _ 8 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
  rw[show 3*op+rest=op+(2*op+rest) by dsimp[op];omega]
  apply wp_i32_add cfg (fuel+2) _ (paid s op 2) limits stack frame callers _ r 8 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
  rw[show 2*op+rest=op+(1*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+1) _ (paid s op 3) limits (stack.push (.i32 (r+8))) frame callers _ 1049788 post (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
  simp only[Nat.one_mul]
  apply wp_i32_const cfg fuel _ (paid s op 4) limits ((stack.push (.i32 (r+8))).push (.i32 1049788)) frame callers _ 5 post (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega)))
  simpa only[paid,op,List.append_eq,List.nil_append] using hnext

def packArgumentsCode:Expr:=[.local_get 1,.local_get 1,.i32_const 24,.i32_binop .add]
theorem pack_arguments_code:(WNear.Binary.StateReadOuter.packSlice.take 4)=packArgumentsCode:=by kernel_rfl
theorem wp_pack_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r _out:UInt32)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 r)).push (.i32 (r+24))) frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (packArgumentsCode++code)))
      (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  unfold packArgumentsCode
  rw[show 4*cfg.regularOpCost+rest=op+(3*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 1 (.i32 r) post h1 (hc.mono (by dsimp[op];omega))
  rw[show 3*op+rest=op+(2*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+2) _ (paid s op 1) limits (stack.push (.i32 r)) frame callers _ 1 (.i32 r) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
  rw[show 2*op+rest=op+(1*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+1) _ (paid s op 2) limits ((stack.push (.i32 r)).push (.i32 r)) frame callers _ 24 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
  simp only[Nat.one_mul]
  apply wp_i32_add cfg fuel _ (paid s op 3) limits (stack.push (.i32 r)) frame callers _ r 24 post (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
  simpa only[paid,op,List.append_eq,List.nil_append] using hnext

def decodeArgumentsCode:Expr:=[.local_get 1,.i32_const 40,.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4}]
theorem decode_arguments_code:(WNear.Binary.StateReadOuter.decode.take 7)=decodeArgumentsCode:=by kernel_rfl
theorem wp_decode_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r _out:UInt32)(mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:r.toNat+8≤memory.byteSize)
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 (r+40))).push (.i32 (readI32 memory (r.toNat+0)))).push (.i32 (readI32 memory (r.toNat+4)))) frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (decodeArgumentsCode++code)))
      (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  unfold decodeArgumentsCode
  rw[show 7*cfg.regularOpCost+rest=op+(6*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+6) _ s limits stack frame callers _ 1 (.i32 r) post h1 (hc.mono (by dsimp[op];omega))
  rw[show 6*op+rest=op+(5*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+5) _ (paid s op 1) limits (stack.push (.i32 r)) frame callers _ 40 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
  rw[show 5*op+rest=op+(4*op+rest) by dsimp[op];omega]
  apply wp_i32_add cfg (fuel+4) _ (paid s op 2) limits stack frame callers _ r 40 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
  rw[show 4*op+rest=op+(3*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+3) _ (paid s op 3) limits (stack.push (.i32 (r+40))) frame callers _ 1 (.i32 r) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
  rw[show 3*op+rest=op+(2*op+rest) by dsimp[op];omega]
  apply wp_i32_load cfg (fuel+2) _ (paid s op 4) limits (stack.push (.i32 (r+40))) frame callers _ {align:=2,offset:=0} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by dsimp;omega) (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega)))
  rw[show 2*op+rest=op+(1*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+1) _ (paid s op 5) limits ((stack.push (.i32 (r+40))).push (.i32 (readI32 memory (r.toNat+0)))) frame callers _ 1 (.i32 r) post h1 (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega)))
  simp only[Nat.one_mul]
  apply wp_i32_load cfg fuel _ (paid s op 6) limits ((stack.push (.i32 (r+40))).push (.i32 (readI32 memory (r.toNat+0)))) frame callers _ {align:=2,offset:=4} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by dsimp;omega) (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega)))
  simpa only[paid,op,List.append_eq,List.nil_append] using hnext

def copyArgumentsCode:Expr:=[.local_get 0,.local_get 1,.i32_const 40,.i32_binop .add,.i32_const 8,.i32_binop .add,.i32_const 40]
theorem copy_arguments_code:(WNear.Binary.StateReadOuter.copyResult.take 7)=copyArgumentsCode:=by kernel_rfl
theorem wp_copy_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r out:UInt32)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))(h0:frame.locals[0]?=some (.i32 out))
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 out)).push (.i32 ((r+40)+8))).push (.i32 40)) frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (copyArgumentsCode++code)))
      (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  unfold copyArgumentsCode
  rw[show 7*cfg.regularOpCost+rest=op+(6*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+6) _ s limits stack frame callers _ 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega))
  rw[show 6*op+rest=op+(5*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+5) _ (paid s op 1) limits (stack.push (.i32 out)) frame callers _ 1 (.i32 r) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
  rw[show 5*op+rest=op+(4*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+4) _ (paid s op 2) limits ((stack.push (.i32 out)).push (.i32 r)) frame callers _ 40 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
  rw[show 4*op+rest=op+(3*op+rest) by dsimp[op];omega]
  apply wp_i32_add cfg (fuel+3) _ (paid s op 3) limits (stack.push (.i32 out)) frame callers _ r 40 post (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
  rw[show 3*op+rest=op+(2*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 4) limits ((stack.push (.i32 out)).push (.i32 (r+40))) frame callers _ 8 post (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega)))
  rw[show 2*op+rest=op+(1*op+rest) by dsimp[op];omega]
  apply wp_i32_add cfg (fuel+1) _ (paid s op 5) limits (stack.push (.i32 out)) frame callers _ (r+40) 8 post (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega)))
  simp only[Nat.one_mul]
  apply wp_i32_const cfg fuel _ (paid s op 6) limits ((stack.push (.i32 out)).push (.i32 ((r+40)+8))) frame callers _ 40 post (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega)))
  simpa only[paid,op,List.append_eq,List.nil_append] using hnext

def releaseArgumentsCode:Expr:=[.local_get 1,.i32_const 24,.i32_binop .add]
theorem release_arguments_code:(WNear.Binary.StateReadOuter.release.take 3)=releaseArgumentsCode:=by kernel_rfl
theorem wp_release_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r _out:UInt32)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (stack.push (.i32 (r+24))) frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (releaseArgumentsCode++code)))
      (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  unfold releaseArgumentsCode
  rw[show 3*cfg.regularOpCost+rest=op+(2*op+rest) by dsimp[op];omega]
  apply wp_local_get cfg (fuel+2) _ s limits stack frame callers _ 1 (.i32 r) post h1 (hc.mono (by dsimp[op];omega))
  rw[show 2*op+rest=op+(1*op+rest) by dsimp[op];omega]
  apply wp_i32_const cfg (fuel+1) _ (paid s op 1) limits (stack.push (.i32 r)) frame callers _ 24 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
  simp only[Nat.one_mul]
  apply wp_i32_add cfg fuel _ (paid s op 2) limits stack frame callers _ r 24 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
  simpa only[paid,op,List.append_eq,List.nil_append] using hnext
end WNear.Proofs.StateReadOuter
