import Proofs.StateDecodeBorshOutput
import Proofs.StateDecodeBorshExit
import Proofs.AllocateSearchGasCost

/-! Opaque cached-output capsule: actual28 stores then branch3+restore96.
Only the caller's four block labels are removed; operand prefixes are retained. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
attribute [local irreducible] WP atCode
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules32(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl
private theorem modules64(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):(storeI64 s i a m v).modules=s.modules:=rfl
private theorem globals32(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl
private theorem globals64(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):(storeI64 s i a m v).globals=s.globals:=rfl

private theorem output_fields(s:Store NearState)(op index:Nat)(m:Memory)(out:UInt32)(a b c d:UInt64)(n:UInt32):
    (cachedOutputStore s op index m out a b c d n).modules=s.modules ∧
    (cachedOutputStore s op index m out a b c d n).globals=s.globals:=by
  simp only[cachedOutputStore,StateDecodeScalar.store64Added,store32Added,StateDecodePrefix.outputTagStore,
    modules32,modules64,modules_paid,globals32,globals64,globals_paid,and_self]
private theorem units32(s:Store NearState)(op n index address:Nat)(memory:Memory)(v:UInt32):
    GasUnits s (storeI32 (paid s op n) index address memory v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem units64(s:Store NearState)(op n index address:Nat)(memory:Memory)(v:UInt64):
    GasUnits s (storeI64 (paid s op n) index address memory v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem output_units(s:Store NearState)(op index:Nat)(m:Memory)(out:UInt32)(a b c d:UInt64)(n:UInt32):
    GasUnits s (cachedOutputStore s op index m out a b c d n) op 28:=by
  let m1:=writeI64 m (out+16).toNat a
  let t1:=StateDecodeScalar.store64Added s op index m out 16 a
  let m2:=writeI64 m1 (out+8).toNat b
  let t2:=StateDecodeScalar.store64Added t1 op index m1 out 8 b
  let m3:=writeI64 m2 (out+24).toNat c
  let t3:=StateDecodeScalar.store64Added t2 op index m2 out 24 c
  let m4:=writeI64 m3 (out+32).toNat d
  let t4:=StateDecodeScalar.store64Added t3 op index m3 out 32 d
  let m5:=writeI32 m4 (out+40).toNat n
  let t5:=store32Added t4 op index m4 out 40 n
  have h1:=units64 s op 5 index (out+16).toNat m a
  have h2:=units64 t1 op 5 index (out+8).toNat m1 b
  have h3:=units64 t2 op 5 index (out+24).toNat m2 c
  have h4:=units64 t3 op 5 index (out+32).toNat m3 d
  have h5:=units32 t4 op 5 index (out+40).toNat m4 n
  have h6:=units32 t5 op 3 index out.toNat m5 0
  simpa only[cachedOutputStore,t5,t4,t3,t2,t1,m5,m4,m3,m2,m1,StateDecodeScalar.store64Added,store32Added,StateDecodePrefix.outputTagStore,Nat.reduceAdd] using ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6

def cachedExitStore(s:Store NearState)(op index gi:Nat)(m:Memory)(out scratch:UInt32)
    (high low usage packed:UInt64)(length:UInt32):=
  exitStore (cachedOutputStore s op index m out high low usage packed length) op gi scratch

theorem wp_output_exit(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code outer middle inner discarded:Expr)
    (out scratch:UInt32)(high low usage packed:UInt64)(length:UInt32)
    (mi:ModuleInst)(index gi:Nat)(global:GlobalInst)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 scratch))
    (h3:frame.locals[3]?=some (.i64 high))(h5:frame.locals[5]?=some (.i64 low))
    (h7:frame.locals[7]?=some (.i64 usage))(h6:frame.locals[6]?=some (.i64 packed))
    (h1:frame.locals[1]?=some (.i32 length))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hgi:mi.globalAddrs[0]?=some gi)(hg:s.globals[gi]?=some global)
    (hw:memory.wf)(b16:(out+16).toNat+8≤memory.byteSize)(b8:(out+8).toNat+8≤memory.byteSize)
    (b24:(out+24).toNat+8≤memory.byteSize)(b32:(out+32).toNat+8≤memory.byteSize)
    (b40:(out+40).toNat+4≤memory.byteSize)(b0:out.toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (33*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (cachedExitStore s cfg.regularOpCost index gi memory out scratch high low usage packed length)
      limits stack frame callers code)) rest post):
    WP cfg (fuel+33) (.next (atCode s limits stack (exitNested frame stack.size code outer middle inner) callers
      (WNear.Binary.StateDecodeBorsh.output++.br 3::discarded))) (33*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=cachedOutputStore s op index memory out high low usage packed length
  let f:=exitNested frame stack.size code outer middle inner
  have fields:=output_fields s op index memory out high low usage packed length
  have credits: t.host.gas.Credits (5*op+rest):=
    (output_units s op index memory out high low usage packed length (5*op+rest)
      (hc.mono (by dsimp[op];omega))).2.2
  have exit:=wp_exit cfg fuel rest t limits stack frame callers code outer middle inner discarded mi gi global scratch post h2
    (by rw[fields.1];exact hm) hgi (by rw[fields.2];exact hg) credits hn
  have output:=wp_output cfg (fuel+5) (5*op+rest) s limits stack f callers (.br 3::discarded)
    out scratch high low usage packed length mi index memory post h0 h2 h3 h5 h7 h6 h1 hm hi he hw b16 b8 b24 b32 b40 b0
    (hc.mono (by dsimp[op];omega)) exit
  simpa only[Nat.add_assoc,Nat.reduceAdd,
    show 28*cfg.regularOpCost+(5*op+rest)=33*cfg.regularOpCost+rest by dsimp[op];omega] using output
end WNear.Proofs.StateDecodeBorsh
