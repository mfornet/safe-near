import Binary.StateDecodePrefix
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredScalarRules

/-! The actual316 copy-helper argument code has seven paid instructions. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def copyArgumentsCode:Expr:=[.local_get 2,.i32_const 48,.i32_binop .add,.local_get 2,.load .i32 none {align:=2,offset:=16},.local_get 2,.load .i32 none {align:=2,offset:=20}]
theorem copy_arguments_exact : WNear.Binary.StateDecodePrefix.copyArguments=copyArgumentsCode++[.call 374]:=rfl

theorem wp_copy_arguments (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:scratch.toNat+24≤memory.byteSize)(hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 (scratch+48))).push (.i32 (readI32 memory (scratch.toNat+16)))).push (.i32 (readI32 memory (scratch.toNat+20))))
      frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (copyArgumentsCode++code))) (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let out:=scratch+48
  let source:=readI32 memory (scratch.toNat+16)
  let size:=readI32 memory (scratch.toNat+20)
  have p6:=wp_i32_load cfg fuel rest (paid s op 6) limits ((stack.push (.i32 out)).push (.i32 source)) frame callers code
    {align:=2,offset:=20} scratch mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) hn
  have p5:=wp_local_get cfg (fuel+1) (op+rest) (paid s op 5) limits ((stack.push (.i32 out)).push (.i32 source)) frame callers
    (.load .i32 none {align:=2,offset:=20}::code) 2 (.i32 scratch) post h2 (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) p6
  have p4:=wp_i32_load cfg (fuel+2) (op+(op+rest)) (paid s op 4) limits (stack.push (.i32 out)) frame callers
    (.local_get 2::.load .i32 none {align:=2,offset:=20}::code) {align:=2,offset:=16} scratch mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by dsimp;omega)
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) p5
  have p3:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) (paid s op 3) limits (stack.push (.i32 out)) frame callers
    (.load .i32 none {align:=2,offset:=16}::.local_get 2::.load .i32 none {align:=2,offset:=20}::code) 2 (.i32 scratch) post h2
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) p4
  have p2:=wp_i32_add cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 2) limits stack frame callers
    (.local_get 2::.load .i32 none {align:=2,offset:=16}::.local_get 2::.load .i32 none {align:=2,offset:=20}::code) scratch 48 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) p3
  have p1:=wp_i32_const cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 2::.load .i32 none {align:=2,offset:=16}::.local_get 2::.load .i32 none {align:=2,offset:=20}::code) 48 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) s limits stack frame callers
    (.i32_const 48::.i32_binop .add::.local_get 2::.load .i32 none {align:=2,offset:=16}::.local_get 2::.load .i32 none {align:=2,offset:=20}::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp[op];omega)) p1
  simpa only[copyArgumentsCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+rest))))))=7*cfg.regularOpCost+rest by dsimp[op];omega] using p0
end WNear.Proofs.StateDecodePrefix
