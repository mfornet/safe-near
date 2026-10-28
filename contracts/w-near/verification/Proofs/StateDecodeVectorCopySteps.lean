import Proofs.StateDecodeVectorSteps
import NearVM.MeteredNumericRules

/-! Actual374's four copy arguments and four post-copy instructions. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem modules_paid (s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def argumentsCode:Expr:=[.local_get 0,.load .i32 none {align:=2,offset:=0},.local_get 1,.local_get 2]
def finishCode:Expr:=[.drop,.local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=8}]
def finishStore (s:Store NearState)(op index:Nat)(memory:Memory)(out size:UInt32):=
  storeI32 (paid s op 4) index (out.toNat+8) memory size

theorem wp_arguments (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)
    (out source size:UInt32)(mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h1:frame.locals[1]?=some (.i32 source))(h2:frame.locals[2]?=some (.i32 size))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:out.toNat+4≤memory.byteSize)(hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      (((base.push (.i32 (readI32 memory out.toNat))).push (.i32 source)).push (.i32 size)) frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits base frame callers (argumentsCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have c1:=paid_credits s op 1 (3*op+rest) (hc.mono (by dsimp[op];omega))
  have c2:=paid_credits s op 2 (2*op+rest) (hc.mono (by dsimp[op];omega))
  have c3:=paid_credits s op 3 (op+rest) (hc.mono (by dsimp[op];omega))
  have l2:=wp_local_get cfg fuel rest (paid s op 3) limits ((base.push (.i32 (readI32 memory out.toNat))).push (.i32 source)) frame callers code 2 (.i32 size) post h2 c3 hn
  have l1:=wp_local_get cfg (fuel+1) (op+rest) (paid s op 2) limits (base.push (.i32 (readI32 memory out.toNat))) frame callers (.local_get 2::code) 1 (.i32 source) post h1 (c2.mono (by omega)) l2
  have hm1:(paid s op 1).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have he1:(paid s op 1).mems[index]?=some memory:=by rw[mems_paid];exact he
  simp only[show fuel+1+1=fuel+2 by omega,show cfg.regularOpCost+(op+rest)=2*op+rest by dsimp[op];omega] at l1
  have load:=wp_i32_load cfg (fuel+2) (2*op+rest) (paid s op 1) limits base frame callers (.local_get 1::.local_get 2::code)
    {align:=2,offset:=0} out mi index memory post hm1 hi he1 hb (c1.mono (by omega)) l1
  simp only[show fuel+2+1=fuel+3 by omega,show cfg.regularOpCost+(2*op+rest)=3*op+rest by dsimp[op];omega] at load
  have get:=wp_local_get cfg (fuel+3) (3*op+rest) s limits base frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 1::.local_get 2::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) load
  simpa only[argumentsCode,List.cons_append,List.nil_append,show fuel+3+1=fuel+4 by omega,
    show cfg.regularOpCost+(3*op+rest)=4*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_finish (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)
    (out size:UInt32)(returned:Value)(mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 size))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:out.toNat+12≤memory.byteSize)(hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (finishStore s cfg.regularOpCost index memory out size) limits base frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits (base.push returned) frame callers (finishCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have c1:=paid_credits s op 1 (3*op+rest) (hc.mono (by dsimp[op];omega))
  have c2:=paid_credits s op 2 (2*op+rest) (hc.mono (by dsimp[op];omega))
  have c3:=paid_credits s op 3 (op+rest) (hc.mono (by dsimp[op];omega))
  have hm3:(paid s op 3).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have he3:(paid s op 3).mems[index]?=some memory:=by rw[mems_paid];exact he
  have store:=wp_i32_store cfg fuel rest (paid s op 3) limits base frame callers code {align:=2,offset:=8} out size mi index memory post hm3 hi he3 hb c3 hn
  have get2:=wp_local_get cfg (fuel+1) (op+rest) (paid s op 2) limits (base.push (.i32 out)) frame callers (.store .i32 none {align:=2,offset:=8}::code) 2 (.i32 size) post h2 (c2.mono (by omega)) store
  simp only[show fuel+1+1=fuel+2 by omega,show cfg.regularOpCost+(op+rest)=2*op+rest by dsimp[op];omega] at get2
  have get0:=wp_local_get cfg (fuel+2) (2*op+rest) (paid s op 1) limits base frame callers (.local_get 2::.store .i32 none {align:=2,offset:=8}::code) 0 (.i32 out) post h0 (c1.mono (by omega)) get2
  simp only[show fuel+2+1=fuel+3 by omega,show cfg.regularOpCost+(2*op+rest)=3*op+rest by dsimp[op];omega] at get0
  have drop:=wp_drop cfg (fuel+3) (3*op+rest) s limits base frame callers (.local_get 0::.local_get 2::.store .i32 none {align:=2,offset:=8}::code) returned post (hc.mono (by dsimp[op];omega)) get0
  simpa only[finishCode,List.cons_append,List.nil_append,show fuel+3+1=fuel+4 by omega,
    show cfg.regularOpCost+(3*op+rest)=4*cfg.regularOpCost+rest by dsimp[op];omega] using drop
end WNear.Proofs.StateDecodeVectorCopy
