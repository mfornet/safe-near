import Binary.StateDecodeBorsh
import Proofs.StateDecodeBorshSavePrefix

/-! Actual425 caches the vector length, writes it, and then reads the packed
record from the updated memory. No separation hypothesis changes that order. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules_store(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl

def vectorHighFrame(frame:CallFrame)(m:Memory)(r:UInt32):=
  {frame with locals:=frame.locals.set! 1 (.i32 (readI32 m ((r+16)+8).toNat))}
def cacheVectorHighMemory(m:Memory)(r:UInt32):=writeI32 m (r+8).toNat (readI32 m ((r+16)+8).toNat)
def vectorHighStore(s:Store NearState)(op index:Nat)(m:Memory)(r:UInt32):=
  storeI32 (paid s op 11) index (r+8).toNat m (readI32 m ((r+16)+8).toNat)
def vectorCachedFrame(frame:CallFrame)(m:Memory)(r:UInt32):=
  {vectorHighFrame frame m r with locals:=(vectorHighFrame frame m r).locals.set! 6 (.i64 (readI64 (cacheVectorHighMemory m r) (r.toNat+16)))}
def vectorCachedStore(s:Store NearState)(op index:Nat)(m:Memory)(r:UInt32):=
  storeI64 (paid (vectorHighStore s op index m r) op 5) index r.toNat (cacheVectorHighMemory m r) (readI64 (cacheVectorHighMemory m r) (r.toNat+16))

theorem wp_cache_vector (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 r))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hw:memory.wf)(bs:((r+16)+8).toNat+4≤memory.byteSize)
    (bh:(r+8).toNat+4≤memory.byteSize)(bl:r.toNat+24≤memory.byteSize)
    (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (vectorCachedStore s cfg.regularOpCost index memory r) limits stack
      (vectorCachedFrame frame memory r) callers code)) rest post):
    WP cfg (fuel+16) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.cacheVector++code)))
      (16*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=vectorHighFrame frame memory r
  let g:=vectorCachedFrame frame memory r
  let t:=vectorHighStore s op index memory r
  let m:=cacheVectorHighMemory memory r
  let v:=readI64 m (r.toNat+16)
  have sh:=writeI32_spec memory (r+8).toNat (readI32 memory ((r+16)+8).toNat) hw bh
  have fm:f.inst=frame.inst:=rfl
  have gm:g.inst=frame.inst:=rfl
  have f2:f.locals[2]?=some (.i32 r):=by simp[f,vectorHighFrame,h2]
  have tm:t.modules[frame.inst]?=some mi:=by unfold t vectorHighStore;rw[modules_store,modules_paid];exact hm
  have te:t.mems[index]?=some m:=storeI32_memory _ _ _ _ _ (by rw[mems_paid];exact he)
  have tc:t.host.gas.Credits (5*op+rest):=by
    simpa only[t,vectorHighStore,storeI32_host] using paid_credits s op 11 (5*op+rest) (hc.mono (by dsimp[op];omega))
  have st:=wp_i64_store cfg fuel rest (paid t op 4) limits stack g callers code {align:=3,offset:=0} r v mi index m post
    (by rw[modules_paid,gm];exact tm) hi (by rw[mems_paid];exact te)
    (by change r.toNat+0+8≤m.byteSize;unfold m cacheVectorHighMemory;rw[sh.2.1];omega)
    (paid_credits t op 4 _ (tc.mono (by dsimp[op];omega))) hn
  have tee:=wp_local_tee cfg (fuel+1) (op+rest) (paid t op 3) limits (stack.push (.i32 r)) f callers
    (.store .i64 none {align:=3,offset:=0}::code) 6 (.i64 v) post
    (paid_credits t op 3 _ (tc.mono (by dsimp[op];omega))) st
  have load:=wp_i64_load cfg (fuel+2) (op+(op+rest)) (paid t op 2) limits (stack.push (.i32 r)) f callers
    (.local_tee 6::.store .i64 none {align:=3,offset:=0}::code) {align:=3,offset:=16} r mi index m post
    (by rw[modules_paid,fm];exact tm) hi (by rw[mems_paid];exact te)
    (by change r.toNat+16+8≤m.byteSize;unfold m cacheVectorHighMemory;rw[sh.2.1];exact bl)
    (paid_credits t op 2 _ (tc.mono (by dsimp[op];omega))) tee
  have inner:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) (paid t op 1) limits (stack.push (.i32 r)) f callers
    (.load .i64 none {align:=3,offset:=16}::.local_tee 6::.store .i64 none {align:=3,offset:=0}::code) 2 (.i32 r) post f2
    (paid_credits t op 1 _ (tc.mono (by dsimp[op];omega))) load
  have tail:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) t limits stack f callers
    (.local_get 2::.load .i64 none {align:=3,offset:=16}::.local_tee 6::.store .i64 none {align:=3,offset:=0}::code) 2 (.i32 r) post f2
    (tc.mono (by dsimp[op];omega)) inner
  let suffix:Expr:=[.local_get 2,.local_get 2,.load .i64 none {align:=3,offset:=16},.local_tee 6,.store .i64 none {align:=3,offset:=0}]++code
  have tail':WP cfg (fuel+5) (.next (atCode t limits stack f callers suffix)) (5*op+rest) post:=by
    simpa only[suffix,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*op+rest by dsimp[op];omega] using tail
  have p10:=wp_i32_store cfg (fuel+5) (5*op+rest) (paid s op 10) limits stack f callers suffix {align:=2,offset:=0} (r+8) (readI32 memory ((r+16)+8).toNat) mi index memory post (by rw[modules_paid,fm];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using bh) (paid_credits s op 10 _ (hc.mono (by dsimp[op];omega))) tail'
  have p9:=wp_local_tee cfg (fuel+6) (6*op+rest) (paid s op 9) limits (stack.push (.i32 (r+8))) frame callers (.store .i32 none {align:=2,offset:=0}::suffix) 1 (.i32 (readI32 memory ((r+16)+8).toNat)) post (paid_credits s op 9 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(5*op+rest)=6*op+rest by dsimp[op];omega] using p10)
  have p8:=wp_i32_load cfg (fuel+7) (7*op+rest) (paid s op 8) limits (stack.push (.i32 (r+8))) frame callers (.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) {align:=2,offset:=0} ((r+16)+8) mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using bs) (paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(6*op+rest)=7*op+rest by dsimp[op];omega] using p9)
  have p7:=wp_i32_add cfg (fuel+8) (8*op+rest) (paid s op 7) limits (stack.push (.i32 (r+8))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) (r+16) 8 post (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(7*op+rest)=8*op+rest by dsimp[op];omega] using p8)
  have p6:=wp_i32_const cfg (fuel+9) (9*op+rest) (paid s op 6) limits ((stack.push (.i32 (r+8))).push (.i32 (r+16))) frame callers (.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) 8 post (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(8*op+rest)=9*op+rest by dsimp[op];omega] using p7)
  have p5:=wp_i32_add cfg (fuel+10) (10*op+rest) (paid s op 5) limits (stack.push (.i32 (r+8))) frame callers (.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) r 16 post (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(9*op+rest)=10*op+rest by dsimp[op];omega] using p6)
  have p4:=wp_i32_const cfg (fuel+11) (11*op+rest) (paid s op 4) limits ((stack.push (.i32 (r+8))).push (.i32 r)) frame callers (.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) 16 post (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(10*op+rest)=11*op+rest by dsimp[op];omega] using p5)
  have p3:=wp_local_get cfg (fuel+12) (12*op+rest) (paid s op 3) limits (stack.push (.i32 (r+8))) frame callers (.i32_const 16::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) 2 (.i32 r) post h2 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(11*op+rest)=12*op+rest by dsimp[op];omega] using p4)
  have p2:=wp_i32_add cfg (fuel+13) (13*op+rest) (paid s op 2) limits stack frame callers (.local_get 2::.i32_const 16::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) r 8 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(12*op+rest)=13*op+rest by dsimp[op];omega] using p3)
  have p1:=wp_i32_const cfg (fuel+14) (14*op+rest) (paid s op 1) limits (stack.push (.i32 r)) frame callers (.i32_binop .add::.local_get 2::.i32_const 16::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) 8 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(13*op+rest)=14*op+rest by dsimp[op];omega] using p2)
  have p0:=wp_local_get cfg (fuel+15) (15*op+rest) s limits (stack) frame callers (.i32_const 8::.i32_binop .add::.local_get 2::.i32_const 16::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_tee 1::.store .i32 none {align:=2,offset:=0}::suffix) 2 (.i32 r) post h2 (hc.mono (by dsimp[op];omega)) (by simpa only[paid,op,f,vectorHighFrame,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(14*op+rest)=15*op+rest by dsimp[op];omega] using p1)
  simpa only[WNear.Binary.StateDecodeBorsh.cacheVector,suffix,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(15*op+rest)=16*cfg.regularOpCost+rest by dsimp[op];omega] using p0
end WNear.Proofs.StateDecodeBorsh
