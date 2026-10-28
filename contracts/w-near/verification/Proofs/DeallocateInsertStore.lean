import Proofs.DeallocateInsertPhases

/-! The insertion path's actual local-get/local-get/store fragments. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

theorem wp_store_locals(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)
    (address value:UInt32)(addressLocal valueLocal:Nat)(mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (ha:frame.locals[addressLocal]?=some (.i32 address))(hv:frame.locals[valueLocal]?=some (.i32 value))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:address.toNat+4≤memory.byteSize)(hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 3) index address.toNat memory value)
      limits stack frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get addressLocal::.local_get valueLocal::.store .i32 none {align:=2,offset:=0}::code)))
      (3*cfg.regularOpCost+rest) post:=by
  have c1:=paid_credits s cfg.regularOpCost 1 (2*cfg.regularOpCost+rest) (hc.mono (by omega))
  have c2:=paid_credits s cfg.regularOpCost 2 (cfg.regularOpCost+rest) (hc.mono (by omega))
  have module2:(paid s cfg.regularOpCost 2).modules[frame.inst]?=some mi:=by simpa only[paid,chargedStore] using hm
  have mem2:(paid s cfg.regularOpCost 2).mems[index]?=some memory:=by simpa only[paid,chargedStore] using he
  have store:=wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align:=2,offset:=0} address value mi index memory post module2 hi mem2 (by simpa using hb) c2
    (by simpa only[paid,Nat.add_zero] using hnext)
  have getValue:=wp_local_get cfg (fuel+1) (cfg.regularOpCost+rest) (paid s cfg.regularOpCost 1) limits
    (stack.push (.i32 address)) frame callers (.store .i32 none {align:=2,offset:=0}::code) valueLocal (.i32 value) post hv
    (c1.mono (by omega)) (by simpa only[paid] using store)
  have getAddress:=wp_local_get cfg (fuel+2) (2*cfg.regularOpCost+rest) s limits stack frame callers
    (.local_get valueLocal::.store .i32 none {align:=2,offset:=0}::code) addressLocal (.i32 address) post ha
    (hc.mono (by omega)) (by simpa only[paid,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega] using getValue)
  simpa only[show cfg.regularOpCost+(2*cfg.regularOpCost+rest)=3*cfg.regularOpCost+rest by omega,Nat.add_assoc,Nat.reduceAdd] using getAddress
end WNear.Proofs.DeallocateInsert
