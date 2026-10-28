import Binary.StateDecodeBorsh
import Proofs.StorePairCallerState
import NearVM.MeteredMemoryRules
import NearVM.MeteredScalarRules
import NearVM.MeteredI32MemoryRules

/-! Actual425 saves the narrow result high word first, then reads the packed
low word from that updated memory. No source/destination separation is assumed. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules_store(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl

def narrowSavedHighMemory(memory:Memory)(scratch:UInt32):=writeI32 memory ((scratch+80)+8).toNat (readI32 memory ((scratch+56)+12).toNat)
def narrowHighStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch:UInt32):=
  storeI32 (paid s op 12) index ((scratch+80)+8).toNat memory (readI32 memory ((scratch+56)+12).toNat)
def narrowLowStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch:UInt32):=
  storeI64 (paid s op 4) index (scratch.toNat+80) memory (readI64 memory (scratch.toNat+60))
def narrowSavedStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch:UInt32):=
  narrowLowStore (narrowHighStore s op index memory scratch) op index (narrowSavedHighMemory memory scratch) scratch

def narrowLowCode : Expr := [.local_get 2,.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=80}]
def narrowHighCode : Expr := [.local_get 2,.i32_const 80,.i32_binop .add,.i32_const 8,.i32_binop .add,
  .local_get 2,.i32_const 56,.i32_binop .add,.i32_const 12,.i32_binop .add,
  .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]

theorem wp_save_narrow_low (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hr:scratch.toNat+60+8≤memory.byteSize)(hb:scratch.toNat+80+8≤memory.byteSize)
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (narrowLowStore s cfg.regularOpCost index memory scratch) limits stack frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (narrowLowCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let value:=readI64 memory (scratch.toNat+60)
  have store:=wp_i64_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=3,offset:=80} scratch value mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have load:=wp_i64_load cfg (fuel+1) (op+rest) (paid s op 2) limits (stack.push (.i32 scratch)) frame callers
    (.store .i64 none {align:=3,offset:=80}::code) {align:=2,offset:=60} scratch mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hr
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) store
  have inner:=wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.load .i64 none {align:=2,offset:=60}::.store .i64 none {align:=3,offset:=80}::code) 2 (.i32 scratch) post h2
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) load
  have outer:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.local_get 2::.load .i64 none {align:=2,offset:=60}::.store .i64 none {align:=3,offset:=80}::code) 2 (.i32 scratch) post h2
    (hc.mono (by dsimp[op];omega)) inner
  simpa only[narrowLowCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using outer

theorem wp_save_narrow_high (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hr:((scratch+56)+12).toNat+4≤memory.byteSize)(hb:((scratch+80)+8).toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (narrowHighStore s cfg.regularOpCost index memory scratch) limits stack frame callers code)) rest post):
    WP cfg (fuel+12) (.next (atCode s limits stack frame callers (narrowHighCode++code))) (12*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have step11:=wp_i32_store cfg (fuel+0) (rest) (paid s op 11) limits stack frame callers code {align:=2,offset:=0} ((scratch+80)+8) (readI32 memory ((scratch+56)+12).toNat) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 11 _ (hc.mono (by dsimp[op];omega))) hn
  have step10:=wp_i32_load cfg (fuel+1) (op+(rest)) (paid s op 10) limits (stack.push (.i32 ((scratch+80)+8))) frame callers (.store .i32 none {align:=2,offset:=0}::code) {align:=2,offset:=0} ((scratch+56)+12) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hr)
    (paid_credits s op 10 _ (hc.mono (by dsimp[op];omega))) step11
  have step9:=wp_i32_add cfg (fuel+2) (op+(op+(rest))) (paid s op 9) limits (stack.push (.i32 ((scratch+80)+8))) frame callers (.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) (scratch+56) 12 post
    (paid_credits s op 9 _ (hc.mono (by dsimp[op];omega))) step10
  have step8:=wp_i32_const cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 8) limits ((stack.push (.i32 ((scratch+80)+8))).push (.i32 (scratch+56))) frame callers (.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 12 post
    (paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))) step9
  have step7:=wp_i32_add cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 7) limits (stack.push (.i32 ((scratch+80)+8))) frame callers (.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) scratch 56 post
    (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) step8
  have step6:=wp_i32_const cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 6) limits ((stack.push (.i32 ((scratch+80)+8))).push (.i32 scratch)) frame callers (.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 56 post
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) step7
  have step5:=wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 5) limits (stack.push (.i32 ((scratch+80)+8))) frame callers (.i32_const 56::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 2 (.i32 scratch) post h2
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) step6
  have step4:=wp_i32_add cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) (paid s op 4) limits stack frame callers (.local_get 2::.i32_const 56::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) (scratch+80) 8 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) step5
  have step3:=wp_i32_const cfg (fuel+8) (op+(op+(op+(op+(op+(op+(op+(op+(rest))))))))) (paid s op 3) limits (stack.push (.i32 (scratch+80))) frame callers (.i32_binop .add::.local_get 2::.i32_const 56::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 8 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) step4
  have step2:=wp_i32_add cfg (fuel+9) (op+(op+(op+(op+(op+(op+(op+(op+(op+(rest)))))))))) (paid s op 2) limits stack frame callers (.i32_const 8::.i32_binop .add::.local_get 2::.i32_const 56::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) scratch 80 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) step3
  have step1:=wp_i32_const cfg (fuel+10) (op+(op+(op+(op+(op+(op+(op+(op+(op+(op+(rest))))))))))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers (.i32_binop .add::.i32_const 8::.i32_binop .add::.local_get 2::.i32_const 56::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 80 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) step2
  have step0:=wp_local_get cfg (fuel+11) (op+(op+(op+(op+(op+(op+(op+(op+(op+(op+(op+(rest)))))))))))) s limits stack frame callers (.i32_const 80::.i32_binop .add::.i32_const 8::.i32_binop .add::.local_get 2::.i32_const 56::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 2 (.i32 scratch) post h2
    (hc.mono (by dsimp[op];omega)) step1
  simpa only[narrowHighCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(op+(op+(op+(op+(rest))))))))))))=12*cfg.regularOpCost+rest by dsimp[op];omega] using step0
/-- All16 actual instructions, preserving the frame and arbitrary operand
prefix. The low load sees narrowSavedHighMemory, including any aliasing write. -/
theorem wp_save_narrow (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hw:memory.wf)
    (hr:((scratch+56)+12).toNat+4≤memory.byteSize)(hb:((scratch+80)+8).toNat+4≤memory.byteSize)
    (hrLow:scratch.toNat+60+8≤memory.byteSize)(hbLow:scratch.toNat+80+8≤memory.byteSize)
    (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (narrowSavedStore s cfg.regularOpCost index memory scratch) limits stack frame callers code)) rest post):
    WP cfg (fuel+16) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.saveNarrow++code)))
      (16*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=narrowHighStore s op index memory scratch
  let m:=narrowSavedHighMemory memory scratch
  have shape:=writeI32_spec memory ((scratch+80)+8).toNat (readI32 memory ((scratch+56)+12).toNat) hw hb
  have tm:t.modules[frame.inst]?=some mi:=by unfold t narrowHighStore;rw[modules_store,modules_paid];exact hm
  have te:t.mems[index]?=some m:=storeI32_memory _ _ _ _ _ (by rw[mems_paid];exact he)
  have tc:t.host.gas.Credits (4*op+rest):=by
    simpa only[t,narrowHighStore,storeI32_host] using paid_credits s op 12 (4*op+rest) (hc.mono (by dsimp[op];omega))
  have readLow:scratch.toNat+60+8≤m.byteSize:=by change _≤(writeI32 _ _ _).byteSize;rw[shape.2.1];exact hrLow
  have writeLow:scratch.toNat+80+8≤m.byteSize:=by change _≤(writeI32 _ _ _).byteSize;rw[shape.2.1];exact hbLow
  have low:=wp_save_narrow_low cfg fuel rest t limits stack frame callers code scratch mi index m post
    h2 tm hi te readLow writeLow tc hn
  have high:=wp_save_narrow_high cfg (fuel+4) (4*op+rest) s limits stack frame callers (narrowLowCode++code)
    scratch mi index memory post h2 hm hi he hr hb (hc.mono (by dsimp[op];omega)) low
  simpa only[WNear.Binary.StateDecodeBorsh.saveNarrow,narrowHighCode,narrowLowCode,List.cons_append,List.nil_append,
    show fuel+4+12=fuel+16 by omega,
    show 12*cfg.regularOpCost+(4*op+rest)=16*cfg.regularOpCost+rest by dsimp[op];omega] using high
end WNear.Proofs.StateDecodeBorsh
