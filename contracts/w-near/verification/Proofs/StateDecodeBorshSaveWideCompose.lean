import Proofs.StateDecodeBorshSaveWide

/-! Composition of all twenty deployed wide-result save instructions.
Every source load uses the memory left by the preceding write. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64

def saveWideMemory1(memory:Memory)(r source:UInt32):=
  writeI64 memory (((r+32)+8).toNat+0) (readI64 memory (source.toNat+0))
def saveWideMemory2(memory:Memory)(r source:UInt32):=
  writeI32 (saveWideMemory1 memory r source) ((r+48).toNat+0)
    (readI32 (saveWideMemory1 memory r source) ((r+76).toNat+0))
def saveWideStore(s:Store NearState)(op index:Nat)(memory:Memory)(r source:UInt32):=
  saveWideLastStore (saveWideSecondStore (saveWideFirstStore s op index memory r source)
    op index (saveWideMemory1 memory r source) r source)
    op index (saveWideMemory2 memory r source) r source

private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules_store64(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):(storeI64 s i a m v).modules=s.modules:=rfl
private theorem modules_store32(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl

theorem wp_save_wide(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r source:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 r))(h4:frame.locals[4]?=some (.i32 source))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hw:memory.wf)
    (hb1:((r+32)+8).toNat+0+8≤memory.byteSize)(hs1:source.toNat+0+8≤memory.byteSize)
    (hb2:(r+48).toNat+0+4≤memory.byteSize)(hs2:(r+76).toNat+0+4≤memory.byteSize)
    (hb3:r.toNat+32+8≤memory.byteSize)(hs3:r.toNat+60+8≤memory.byteSize)
    (hc:s.host.gas.Credits (20*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (saveWideStore s cfg.regularOpCost index memory r source)
      limits stack frame callers code)) rest post):
    WP cfg (fuel+20) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeBorsh.saveWide++code))) (20*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let s1:=saveWideFirstStore s op index memory r source
  let m1:=saveWideMemory1 memory r source
  let s2:=saveWideSecondStore s1 op index m1 r source
  let m2:=saveWideMemory2 memory r source
  have first:=writeI64_spec memory (((r+32)+8).toNat+0) (readI64 memory (source.toNat+0)) hw hb1
  have second:=writeI32_spec m1 ((r+48).toNat+0) (readI32 m1 ((r+76).toNat+0)) first.1 (by change _≤(writeI64 _ _ _).byteSize;rw[first.2.1];exact hb2)
  have sm1:s1.modules[frame.inst]?=some mi:=by unfold s1 saveWideFirstStore;rw[modules_store64,modules_paid];exact hm
  have sm2:s2.modules[frame.inst]?=some mi:=by unfold s2 saveWideSecondStore;rw[modules_store32,modules_paid];exact sm1
  have se1:s1.mems[index]?=some m1:=by
    apply storeI64_memory
    rw[mems_paid];exact he
  have se2:s2.mems[index]?=some m2:=by
    apply storeI32_memory
    rw[mems_paid];exact se1
  have sc1:s1.host.gas.Credits (12*op+rest):=by
    simpa only[s1,saveWideFirstStore,storeI64_host] using paid_credits s op 8 (12*op+rest) (hc.mono (by dsimp[op];omega))
  have sc2:s2.host.gas.Credits (4*op+rest):=by
    simpa only[s2,saveWideSecondStore,storeI32_host] using paid_credits s1 op 8 (4*op+rest) (sc1.mono (by omega))
  have last:=wp_saveWideLast cfg fuel rest s2 limits stack frame callers code r source mi index m2 post
    h2 h4 sm2 hi se2
    (by change _≤(writeI32 _ _ _).byteSize;rw[second.2.1];change _≤(writeI64 _ _ _).byteSize;rw[first.2.1];exact hb3)
    (by change _≤(writeI32 _ _ _).byteSize;rw[second.2.1];change _≤(writeI64 _ _ _).byteSize;rw[first.2.1];exact hs3)
    sc2 hnext
  let lastCode:Expr:=[.local_get 2,.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]
  have middle:=wp_saveWideSecond cfg (fuel+4) (4*op+rest) s1 limits stack frame callers (lastCode++code) r source mi index m1 post h2 h4 sm1 hi se1
    (by change _≤(writeI64 _ _ _).byteSize;rw[first.2.1];exact hb2)
    (by change _≤(writeI64 _ _ _).byteSize;rw[first.2.1];exact hs2)
    (sc1.mono (by dsimp[op];omega)) last
  let middleCode:Expr:=[.local_get 2,.i32_const 48,.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]
  have firstCall:=wp_saveWideFirst cfg ((fuel+4)+8) (8*op+(4*op+rest)) s limits stack frame callers
    (middleCode++lastCode++code) r source mi index memory post h2 h4 hm hi he hb1 hs1
    (hc.mono (by dsimp[op];omega))
    (by simpa only[List.append_assoc] using middle)
  simpa only[WNear.Binary.StateDecodeBorsh.saveWide,middleCode,lastCode,List.cons_append,List.nil_append,
    Nat.add_assoc,Nat.reduceAdd,show 8*cfg.regularOpCost+(8*op+(4*op+rest))=20*cfg.regularOpCost+rest by dsimp[op];omega] using firstCall
end WNear.Proofs.StateDecodeBorsh
