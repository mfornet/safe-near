import Binary.StateReadOuter
import Proofs.StateDecodeBorshReadExit

/-! Actual219 storage-result copies. The packed low source is reloaded after
its preceding length store; every UInt32 address addition is retained. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

private theorem word_modules(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl

def storageHighMemory(m:Memory)(r:UInt32):=writeI32 m ((r+24)+8).toNat (readI32 m ((r+8)+8).toNat)
def storageHighStore(s:Store NearState)(op index:Nat)(m:Memory)(r:UInt32):=
  storeI32 (paid s op 12) index ((r+24)+8).toNat m (readI32 m ((r+8)+8).toNat)
def storageLowMemory(m:Memory)(r:UInt32):=writeI64 m (r.toNat+24) (readI64 m (r.toNat+8))
def storageLowStore(s:Store NearState)(op index:Nat)(m:Memory)(r:UInt32):=
  storeI64 (paid s op 4) index (r.toNat+24) m (readI64 m (r.toNat+8))
def storageHighCode:Expr:=[.local_get 1,.i32_const 24,.i32_binop .add,.i32_const 8,.i32_binop .add,
  .local_get 1,.i32_const 8,.i32_binop .add,.i32_const 8,.i32_binop .add,
  .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]
def storageLowCode:Expr:=[.local_get 1,.local_get 1,.load .i64 none {align:=3,offset:=8},.store .i64 none {align:=3,offset:=24}]
theorem storage_copy_code:WNear.Binary.StateReadOuter.copyStorage=storageHighCode++storageLowCode:=by kernel_rfl

theorem wp_storage_high(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (hr:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)
    (he:s.mems[index]?=some memory)(hbS:((r+8)+8).toNat+4≤memory.byteSize)(hbT:((r+24)+8).toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (storageHighStore s cfg.regularOpCost index memory r) limits stack frame callers code)) rest post):
    WP cfg (fuel+12) (.next (atCode s limits stack frame callers (storageHighCode++code))) (12*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  rw[show 12*cfg.regularOpCost+rest=op+(11*op+rest) by dsimp[op];omega]
  unfold storageHighCode
  apply wp_local_get cfg (fuel+11) _ s limits stack frame callers _ 1 (.i32 r) post hr (hc.mono (by dsimp[op];omega))
  rw[show 11*op+rest=op+(10*op+rest) by omega]
  apply wp_i32_const cfg (fuel+10) _ (paid s op 1) limits _ frame callers _ 24 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))
  rw[show 10*op+rest=op+(9*op+rest) by omega]
  apply wp_i32_add cfg (fuel+9) _ (paid s op 2) limits stack frame callers _ r 24 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))
  rw[show 9*op+rest=op+(8*op+rest) by omega]
  apply wp_i32_const cfg (fuel+8) _ (paid s op 3) limits _ frame callers _ 8 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))
  rw[show 8*op+rest=op+(7*op+rest) by omega]
  apply wp_i32_add cfg (fuel+7) _ (paid s op 4) limits stack frame callers _ (r+24) 8 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))
  rw[show 7*op+rest=op+(6*op+rest) by omega]
  apply wp_local_get cfg (fuel+6) _ (paid s op 5) limits _ frame callers _ 1 (.i32 r) post hr
  · exact paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  rw[show 6*op+rest=op+(5*op+rest) by omega]
  apply wp_i32_const cfg (fuel+5) _ (paid s op 6) limits _ frame callers _ 8 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))
  rw[show 5*op+rest=op+(4*op+rest) by omega]
  apply wp_i32_add cfg (fuel+4) _ (paid s op 7) limits _ frame callers _ r 8 post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))
  rw[show 4*op+rest=op+(3*op+rest) by omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s op 8) limits _ frame callers _ 8 post
  · exact paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))
  rw[show 3*op+rest=op+(2*op+rest) by omega]
  apply wp_i32_add cfg (fuel+2) _ (paid s op 9) limits _ frame callers _ (r+8) 8 post
  · exact paid_credits s op 9 _ (hc.mono (by dsimp[op];omega))
  rw[show 2*op+rest=op+(op+rest) by omega]
  apply wp_i32_load cfg (fuel+1) _ (paid s op 10) limits (stack.push (.i32 ((r+24)+8))) frame callers _ {align:=2,offset:=0} ((r+8)+8) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hbS)
  · exact paid_credits s op 10 _ (hc.mono (by dsimp[op];omega))
  simp only[Nat.add_zero]
  have store:=wp_i32_store cfg fuel rest (paid s op 11) limits stack frame callers code {align:=2,offset:=0}
    ((r+24)+8) (readI32 memory ((r+8)+8).toNat) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hbT)
    (paid_credits s op 11 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[storageHighStore,paid,Nat.add_zero,op] using hnext)
  simpa only[List.append_eq,List.cons_append,List.nil_append,paid,op] using store

theorem wp_storage_low(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (hr:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)
    (he:s.mems[index]?=some memory)(hbS:r.toNat+8+8≤memory.byteSize)(hbT:r.toNat+24+8≤memory.byteSize)
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (storageLowStore s cfg.regularOpCost index memory r) limits stack frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (storageLowCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  rw[show 4*cfg.regularOpCost+rest=op+(3*op+rest) by dsimp[op];omega]
  unfold storageLowCode
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 1 (.i32 r) post hr (hc.mono (by dsimp[op];omega))
  rw[show 3*op+rest=op+(2*op+rest) by omega]
  apply wp_local_get cfg (fuel+2) _ (paid s op 1) limits _ frame callers _ 1 (.i32 r) post hr
  · exact paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))
  rw[show 2*op+rest=op+(op+rest) by omega]
  apply wp_i64_load cfg (fuel+1) _ (paid s op 2) limits (stack.push (.i32 r)) frame callers _ {align:=3,offset:=8} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbS
  · exact paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))
  have store:=wp_i64_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=3,offset:=24}
    r (readI64 memory (r.toNat+8)) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbT
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hnext
  simpa only[List.append_eq,List.cons_append,List.nil_append,storageLowStore,paid,op] using store

def copiedStorageMemory(m:Memory)(r:UInt32):=storageLowMemory (storageHighMemory m r) r
def copiedStorage(s:Store NearState)(op index:Nat)(m:Memory)(r:UInt32):=
  storageLowStore (storageHighStore s op index m r) op index (storageHighMemory m r) r
attribute [local irreducible] storageHighMemory storageLowMemory storageHighStore storageLowStore

theorem wp_copy_storage(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (hr:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)
    (he:s.mems[index]?=some memory)(hw:memory.wf)
    (hbS:((r+8)+8).toNat+4≤memory.byteSize)(hbT:((r+24)+8).toNat+4≤memory.byteSize)
    (hbL:r.toNat+8+8≤memory.byteSize)(hbU:r.toNat+24+8≤memory.byteSize)
    (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (copiedStorage s cfg.regularOpCost index memory r) limits stack frame callers code)) rest post):
    WP cfg (fuel+16) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadOuter.copyStorage++code)))
      (16*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=storageHighStore s op index memory r
  have shape: (storageHighMemory memory r).byteSize=memory.byteSize:=by
    unfold storageHighMemory
    exact (writeI32_spec memory ((r+24)+8).toNat (readI32 memory ((r+8)+8).toNat) hw hbT).2.1
  have tm:t.modules[frame.inst]?=some mi:=by dsimp only[t];rw[storageHighStore,word_modules,modules_paid];exact hm
  have te:t.mems[index]?=some (storageHighMemory memory r):=by
    unfold t storageHighStore storageHighMemory
    apply storeI32_memory
    rw[mems_paid];exact he
  have tc:t.host.gas.Credits (4*op+rest):=by
    unfold t storageHighStore
    rw[storeI32_host]
    exact paid_credits s op 12 _ (hc.mono (by dsimp[op];omega))
  have low:=wp_storage_low cfg fuel rest t limits stack frame callers code r mi index (storageHighMemory memory r) post
    hr tm hi te (by rw[shape];exact hbL) (by rw[shape];exact hbU) tc hnext
  have high:=wp_storage_high cfg (fuel+4) (4*op+rest) s limits stack frame callers (storageLowCode++code) r mi index memory post
    hr hm hi he hbS hbT (hc.mono (by dsimp[op];omega)) low
  simpa only[storage_copy_code,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 12*cfg.regularOpCost+(4*op+rest)=16*cfg.regularOpCost+rest by dsimp[op];omega] using high
end WNear.Proofs.StateReadOuter
