import Binary.AllocateGrowthHelpers
import NearVM.MeteredBitRules
import NearVM.MeteredControlRules
import NearVM.MeteredScalarRules
import NearVM.MeteredWasmCall
import Proofs.StorePairCallerState

/-! Actual f573 accepted page-to-byte conversion, without panic execution premises. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def pageBytes (pages : UInt32) := pages <<< (16 : UInt32)
def after573 (s : Store NearState) (op : Nat) := paid (chargedStore (chargedStore s op) (9*op)) op 9

theorem mask573 (pages : UInt32) (h : pages.toNat<65536) : pages &&& 65535=pages := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_and,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n:=16) h

theorem pageBytes_toNat (pages : UInt32) (h : pages.toNat<65536) : (pageBytes pages).toNat=pages.toNat*65536 := by
  simp only [pageBytes,UInt32.toNat_shiftLeft,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod,Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  omega

theorem wp_body573 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (pages : UInt32) (post : Post) (hl : frame.locals[0]?=some (.i32 pages))
    (hpages : pages.toNat<65536) (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits (stack.push (.i32 (pageBytes pages))) frame callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateGrowth.body573++code)))
      (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size (.local_get 0::.i32_const 16::.i32_binop .shl::code)
  have last := wp_i32_binop_ok cfg fuel rest (paid s op 8) limits stack frame callers code .shl pages 16 (pageBytes pages) post rfl
    (paid_credits s op 8 _ (hc.mono (by dsimp [op];omega))) (by simpa only [paid,op] using hnext)
  have constant := wp_i32_const cfg (fuel+1) (op+rest) (paid s op 7) limits (stack.push (.i32 pages)) frame callers (.i32_binop .shl::code) 16 post
    (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) last
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 6) limits stack frame callers (.i32_const 16::.i32_binop .shl::code) 0 (.i32 pages) post hl
    (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) constant
  have branch := wp_br_if_block_nonzero cfg (fuel+3) (op+(op+(op+rest))) (paid s op 5) limits stack frame callers
    (.local_get 0::.i32_const 16::.i32_binop .shl::code) WNear.Binary.AllocateGrowth.panic573 1 post (by decide)
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) get
  have rel := wp_i32_relop cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 4) limits stack bf callers
    (.br_if 0::WNear.Binary.AllocateGrowth.panic573) .eq (pages&&&65535) pages post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [Numeric.irelop32,mask573 pages hpages,BEq.rfl,Numeric.bool,ite_true,bf,paid,op] using branch)
  have get2 := wp_local_get cfg (fuel+5) _ (paid s op 3) limits (stack.push (.i32 (pages&&&65535))) bf callers
    (.i32_relop .eq::.br_if 0::WNear.Binary.AllocateGrowth.panic573) 0 (.i32 pages) post hl
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) rel
  have and := wp_i32_and cfg (fuel+6) _ (paid s op 2) limits stack bf callers
    (.local_get 0::.i32_relop .eq::.br_if 0::WNear.Binary.AllocateGrowth.panic573) pages 65535 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) get2
  have mask := wp_i32_const cfg (fuel+7) _ (paid s op 1) limits (stack.push (.i32 pages)) bf callers
    (.i32_binop .and::.local_get 0::.i32_relop .eq::.br_if 0::WNear.Binary.AllocateGrowth.panic573) 65535 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) and
  have first := wp_local_get cfg (fuel+8) _ s limits stack bf callers
    (.i32_const 65535::.i32_binop .and::.local_get 0::.i32_relop .eq::.br_if 0::WNear.Binary.AllocateGrowth.panic573) 0 (.i32 pages) post hl
    (hc.mono (by dsimp [op];omega)) mask
  have inner : WP cfg (fuel+9) (.next (atCode s limits stack bf callers (WNear.Binary.AllocateGrowth.check573++WNear.Binary.AllocateGrowth.panic573)))
      (9*op+rest) post := by
    simpa only [WNear.Binary.AllocateGrowth.check573,List.cons_append,List.nil_append,show cfg.regularOpCost=op from rfl,show op+(op+(op+(op+(op+(op+(op+(op+(op+(rest)))))))))=9*op+rest by omega] using first
  have whole := wp_block_empty cfg (fuel+9) (9*op+rest) s limits stack frame callers
    (WNear.Binary.AllocateGrowth.check573++WNear.Binary.AllocateGrowth.panic573) (.local_get 0::.i32_const 16::.i32_binop .shl::code) post hc inner
  simpa only [WNear.Binary.AllocateGrowth.body573,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,op] using whole

/-- Real f573 call, accepted for every page count below 65536. -/
theorem wp_call573 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (pages : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.funcAddrs[573]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateGrowth.signature573 frame.inst WNear.Binary.AllocateGrowth.function573))
    (hpages : pages.toNat<65536) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (19*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after573 s cfg.regularOpCost) limits (base++[Value.i32 (pageBytes pages)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits (base++[Value.i32 pages]).toArray frame callers (.call 573::code)))
      (19*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := chargedStore (chargedStore s op) (9*op)
  let leaf : CallFrame := {locals:=#[.i32 pages],inst:=frame.inst,arity:=1,height:=base.length,labels:=[],code:=[]}
  let saved := {frame with code}
  have c0 := StorePair.charged_credits s op (9*op+(9*op+rest)) (hc.mono (by dsimp [op];omega))
  have ca := StorePair.charged_credits (chargedStore s op) (9*op) (9*op+rest) c0
  have cf := paid_credits active op 9 rest ca
  have ln : WP cfg fuel (.next (atCode (after573 s op) limits (base++[Value.i32 (pageBytes pages)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have left := wp_leave_wasm cfg fuel rest (after573 s op) limits base [.i32 (pageBytes pages)] leaf saved callers post rfl rfl rfl cf ln
  have arr : (base++[Value.i32 (pageBytes pages)]).toArray=base.toArray.push (.i32 (pageBytes pages)) := by apply Array.toList_inj.mp;simp
  have bn : WP cfg (fuel+1) (.next (atCode (paid active op 9) limits (base.toArray.push (.i32 (pageBytes pages))) leaf (saved::callers) [])) rest post := by
    simpa only [after573,active,arr] using left
  have body := wp_body573 cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] pages post rfl hpages ca bn
  have cr := wp_call_wasm cfg ((fuel+1)+10) (9*op+rest) s limits base [.i32 pages] frame callers code 573 address mi
    WNear.Binary.AllocateGrowth.signature573 frame.inst WNear.Binary.AllocateGrowth.function573 post hm hi hf rfl hd
  have activation : activationGas op (wasmLocals WNear.Binary.AllocateGrowth.function573 [.i32 pages])=9*op := by
    simp [activationGas,wasmLocals,WNear.Binary.AllocateGrowth.function573]
  rw [activation] at cr
  have next : WP cfg ((fuel+1)+10) (.next (wasmCallee active limits base frame callers code WNear.Binary.AllocateGrowth.signature573 frame.inst
      WNear.Binary.AllocateGrowth.function573 [.i32 pages])) (9*op+rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.AllocateGrowth.function573,WNear.Binary.AllocateGrowth.signature573,
      WNear.Binary.AllocateGrowth.signature569,leaf,saved,atCode,List.map_cons,List.map_nil,List.append_nil,List.length_cons,List.length_nil,ValType.default,Array.append_empty] using body
  have result := cr (hc.mono (by dsimp [op];omega)) next
  have cost : cfg.regularOpCost+(9*op+(9*op+rest))=19*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocateGrowth
