import Binary.StateDecodeBorsh
import Proofs.StateDecodeBorshSavePrefix

/-! Actual425 wide-result copies, retaining every intermediate memory read. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def saveWideFirstStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch source:UInt32):=storeI64 (paid s op 8) index (((scratch+32)+8).toNat+0) memory (readI64 memory (source.toNat+0))

theorem wp_saveWideFirst(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch source:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(h4:frame.locals[4]?=some (.i32 source))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hbT:((scratch+32)+8).toNat+0+8≤memory.byteSize)(hbS:source.toNat+0+8≤memory.byteSize)
    (hc:s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (saveWideFirstStore s cfg.regularOpCost index memory scratch source) limits stack frame callers code)) rest post):
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers ([.local_get 2,.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (8*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have step7:=wp_i64_store cfg (fuel+0) (0*op+rest) (paid s op 7) limits stack frame callers (code) {align:=3,offset:=0} ((scratch+32)+8) (readI64 memory (source.toNat+0)) mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbT (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) (by simpa only[saveWideFirstStore,paid,op,Nat.add_zero,Nat.zero_mul,Nat.zero_add] using hnext)
  have chain7:WP cfg (fuel+1) (.next (atCode (paid s op 7) limits ((stack.push (.i32 ((scratch+32)+8))).push (.i64 (readI64 memory (source.toNat+0)))) frame callers ([.store .i64 none {align:=3,offset:=0}]++code))) (1*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(0*cfg.regularOpCost+rest)=1*cfg.regularOpCost+rest by omega] using step7
  have step6:=wp_i64_load cfg (fuel+1) (1*op+rest) (paid s op 6) limits (stack.push (.i32 ((scratch+32)+8))) frame callers ([.store .i64 none {align:=3,offset:=0}]++code) {align:=2,offset:=0} source mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbS (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain7)
  have chain6:WP cfg (fuel+2) (.next (atCode (paid s op 6) limits ((stack.push (.i32 ((scratch+32)+8))).push (.i32 source)) frame callers ([.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (2*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(1*cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega] using step6
  have step5:=wp_local_get cfg (fuel+2) (2*op+rest) (paid s op 5) limits (stack.push (.i32 ((scratch+32)+8))) frame callers ([.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code) 4 (.i32 source) post h4 (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain6)
  have chain5:WP cfg (fuel+3) (.next (atCode (paid s op 5) limits (stack.push (.i32 ((scratch+32)+8))) frame callers ([.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (3*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(2*cfg.regularOpCost+rest)=3*cfg.regularOpCost+rest by omega] using step5
  have step4:=wp_i32_add cfg (fuel+3) (3*op+rest) (paid s op 4) limits stack frame callers ([.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code) (scratch+32) 8 post (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain5)
  have chain4:WP cfg (fuel+4) (.next (atCode (paid s op 4) limits ((stack.push (.i32 (scratch+32))).push (.i32 8)) frame callers ([.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (4*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(3*cfg.regularOpCost+rest)=4*cfg.regularOpCost+rest by omega] using step4
  have step3:=wp_i32_const cfg (fuel+4) (4*op+rest) (paid s op 3) limits (stack.push (.i32 (scratch+32))) frame callers ([.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code) 8 post (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain4)
  have chain3:WP cfg (fuel+5) (.next (atCode (paid s op 3) limits (stack.push (.i32 (scratch+32))) frame callers ([.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (5*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(4*cfg.regularOpCost+rest)=5*cfg.regularOpCost+rest by omega] using step3
  have step2:=wp_i32_add cfg (fuel+5) (5*op+rest) (paid s op 2) limits stack frame callers ([.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code) scratch 32 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain3)
  have chain2:WP cfg (fuel+6) (.next (atCode (paid s op 2) limits ((stack.push (.i32 scratch)).push (.i32 32)) frame callers ([.i32_binop .add,.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (6*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(5*cfg.regularOpCost+rest)=6*cfg.regularOpCost+rest by omega] using step2
  have step1:=wp_i32_const cfg (fuel+6) (6*op+rest) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers ([.i32_binop .add,.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code) 32 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain2)
  have chain1:WP cfg (fuel+7) (.next (atCode (paid s op 1) limits (stack.push (.i32 scratch)) frame callers ([.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (7*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(6*cfg.regularOpCost+rest)=7*cfg.regularOpCost+rest by omega] using step1
  have step0:=wp_local_get cfg (fuel+7) (7*op+rest) (paid s op 0) limits stack frame callers ([.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code) 2 (.i32 scratch) post h2 (paid_credits s op 0 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain1)
  have chain0:WP cfg (fuel+8) (.next (atCode (paid s op 0) limits stack frame callers ([.local_get 2,.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,.local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0}]++code))) (8*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(7*cfg.regularOpCost+rest)=8*cfg.regularOpCost+rest by omega] using step0
  simpa only[paid,op] using chain0

def saveWideSecondStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch _source:UInt32):=storeI32 (paid s op 8) index ((scratch+48).toNat+0) memory (readI32 memory ((scratch+76).toNat+0))

theorem wp_saveWideSecond(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch source:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(_h4:frame.locals[4]?=some (.i32 source))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hbT:(scratch+48).toNat+0+4≤memory.byteSize)(hbS:(scratch+76).toNat+0+4≤memory.byteSize)
    (hc:s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (saveWideSecondStore s cfg.regularOpCost index memory scratch source) limits stack frame callers code)) rest post):
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers ([.local_get 2,.i32_const 48,.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (8*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have step7:=wp_i32_store cfg (fuel+0) (0*op+rest) (paid s op 7) limits stack frame callers (code) {align:=2,offset:=0} (scratch+48) (readI32 memory ((scratch+76).toNat+0)) mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbT (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) (by simpa only[saveWideSecondStore,paid,op,Nat.add_zero,Nat.zero_mul,Nat.zero_add] using hnext)
  have chain7:WP cfg (fuel+1) (.next (atCode (paid s op 7) limits ((stack.push (.i32 (scratch+48))).push (.i32 (readI32 memory ((scratch+76).toNat+0)))) frame callers ([.store .i32 none {align:=2,offset:=0}]++code))) (1*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(0*cfg.regularOpCost+rest)=1*cfg.regularOpCost+rest by omega] using step7
  have step6:=wp_i32_load cfg (fuel+1) (1*op+rest) (paid s op 6) limits (stack.push (.i32 (scratch+48))) frame callers ([.store .i32 none {align:=2,offset:=0}]++code) {align:=2,offset:=0} (scratch+76) mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbS (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain7)
  have chain6:WP cfg (fuel+2) (.next (atCode (paid s op 6) limits ((stack.push (.i32 (scratch+48))).push (.i32 (scratch+76))) frame callers ([.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (2*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(1*cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega] using step6
  have step5:=wp_i32_add cfg (fuel+2) (2*op+rest) (paid s op 5) limits (stack.push (.i32 (scratch+48))) frame callers ([.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code) scratch 76 post (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain6)
  have chain5:WP cfg (fuel+3) (.next (atCode (paid s op 5) limits (((stack.push (.i32 (scratch+48))).push (.i32 scratch)).push (.i32 76)) frame callers ([.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (3*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(2*cfg.regularOpCost+rest)=3*cfg.regularOpCost+rest by omega] using step5
  have step4:=wp_i32_const cfg (fuel+3) (3*op+rest) (paid s op 4) limits ((stack.push (.i32 (scratch+48))).push (.i32 scratch)) frame callers ([.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code) 76 post (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain5)
  have chain4:WP cfg (fuel+4) (.next (atCode (paid s op 4) limits ((stack.push (.i32 (scratch+48))).push (.i32 scratch)) frame callers ([.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (4*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(3*cfg.regularOpCost+rest)=4*cfg.regularOpCost+rest by omega] using step4
  have step3:=wp_local_get cfg (fuel+4) (4*op+rest) (paid s op 3) limits (stack.push (.i32 (scratch+48))) frame callers ([.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code) 2 (.i32 scratch) post h2 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain4)
  have chain3:WP cfg (fuel+5) (.next (atCode (paid s op 3) limits (stack.push (.i32 (scratch+48))) frame callers ([.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (5*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(4*cfg.regularOpCost+rest)=5*cfg.regularOpCost+rest by omega] using step3
  have step2:=wp_i32_add cfg (fuel+5) (5*op+rest) (paid s op 2) limits stack frame callers ([.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code) scratch 48 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain3)
  have chain2:WP cfg (fuel+6) (.next (atCode (paid s op 2) limits ((stack.push (.i32 scratch)).push (.i32 48)) frame callers ([.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (6*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(5*cfg.regularOpCost+rest)=6*cfg.regularOpCost+rest by omega] using step2
  have step1:=wp_i32_const cfg (fuel+6) (6*op+rest) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers ([.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code) 48 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain2)
  have chain1:WP cfg (fuel+7) (.next (atCode (paid s op 1) limits (stack.push (.i32 scratch)) frame callers ([.i32_const 48,.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (7*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(6*cfg.regularOpCost+rest)=7*cfg.regularOpCost+rest by omega] using step1
  have step0:=wp_local_get cfg (fuel+7) (7*op+rest) (paid s op 0) limits stack frame callers ([.i32_const 48,.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code) 2 (.i32 scratch) post h2 (paid_credits s op 0 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain1)
  have chain0:WP cfg (fuel+8) (.next (atCode (paid s op 0) limits stack frame callers ([.local_get 2,.i32_const 48,.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (8*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(7*cfg.regularOpCost+rest)=8*cfg.regularOpCost+rest by omega] using step0
  simpa only[paid,op] using chain0

def saveWideLastStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch _source:UInt32):=storeI64 (paid s op 4) index (scratch.toNat+32) memory (readI64 memory (scratch.toNat+60))

theorem wp_saveWideLast(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch source:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(_h4:frame.locals[4]?=some (.i32 source))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hbT:scratch.toNat+32+8≤memory.byteSize)(hbS:scratch.toNat+60+8≤memory.byteSize)
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (saveWideLastStore s cfg.regularOpCost index memory scratch source) limits stack frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers ([.local_get 2,.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have step3:=wp_i64_store cfg (fuel+0) (0*op+rest) (paid s op 3) limits stack frame callers (code) {align:=3,offset:=32} scratch (readI64 memory (scratch.toNat+60)) mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbT (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[saveWideLastStore,paid,op,Nat.add_zero,Nat.zero_mul,Nat.zero_add] using hnext)
  have chain3:WP cfg (fuel+1) (.next (atCode (paid s op 3) limits ((stack.push (.i32 scratch)).push (.i64 (readI64 memory (scratch.toNat+60)))) frame callers ([.store .i64 none {align:=3,offset:=32}]++code))) (1*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(0*cfg.regularOpCost+rest)=1*cfg.regularOpCost+rest by omega] using step3
  have step2:=wp_i64_load cfg (fuel+1) (1*op+rest) (paid s op 2) limits (stack.push (.i32 scratch)) frame callers ([.store .i64 none {align:=3,offset:=32}]++code) {align:=2,offset:=60} scratch mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbS (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain3)
  have chain2:WP cfg (fuel+2) (.next (atCode (paid s op 2) limits ((stack.push (.i32 scratch)).push (.i32 scratch)) frame callers ([.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]++code))) (2*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(1*cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega] using step2
  have step1:=wp_local_get cfg (fuel+2) (2*op+rest) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers ([.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]++code) 2 (.i32 scratch) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain2)
  have chain1:WP cfg (fuel+3) (.next (atCode (paid s op 1) limits (stack.push (.i32 scratch)) frame callers ([.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]++code))) (3*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(2*cfg.regularOpCost+rest)=3*cfg.regularOpCost+rest by omega] using step1
  have step0:=wp_local_get cfg (fuel+3) (3*op+rest) (paid s op 0) limits stack frame callers ([.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]++code) 2 (.i32 scratch) post h2 (paid_credits s op 0 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using chain1)
  have chain0:WP cfg (fuel+4) (.next (atCode (paid s op 0) limits stack frame callers ([.local_get 2,.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]++code))) (4*op+rest) post:=by
    simpa only[List.cons_append,List.nil_append,paid,op,Nat.add_assoc,Nat.reduceAdd,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(3*cfg.regularOpCost+rest)=4*cfg.regularOpCost+rest by omega] using step0
  simpa only[paid,op] using chain0
end WNear.Proofs.StateDecodeBorsh
