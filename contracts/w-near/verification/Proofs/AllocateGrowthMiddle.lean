import Binary.AllocateGrowth
import Proofs.AllocateGrowthBytes
import Proofs.AllocateUnitsMinimum
import NearVM.MeteredLoopRules

/-! Actual post-growth page-width guard and checked byte-count conversion. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def bytesFrame (frame : CallFrame) (pages : UInt32) := {frame with locals:=frame.locals.set! 4 (.i32 (pageBytes pages))}
def bytesAfter (s : Store NearState) (op : Nat) := AllocateUnits.minimumAfter (paid (after573 (paid s op 1) op) op 1) op

theorem wp_old_pages_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (old : UInt32) (post : Post) (h2 : frame.locals[2]?=some (.i32 old))
    (hold : old.toNat<65536) (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateGrowth.oldPagesGuard++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have branch := wp_br_if_zero cfg fuel rest (paid s op 5) limits stack frame callers code 4 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) (by simpa only [paid,op] using hnext)
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 4) limits stack frame callers (.br_if 4::code)
    .ne (old&&&65535) old post (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [mask573 old hold,Numeric.irelop32,Numeric.bool,bne_self_eq_false,Bool.false_eq_true,ite_false,paid,op] using branch)
  have second := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 (old&&&65535))) frame callers
    (.i32_relop .ne::.br_if 4::code) 2 (.i32 old) post h2 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) rel
  have and := wp_i32_and cfg (fuel+3) _ (paid s op 2) limits stack frame callers (.local_get 2::.i32_relop .ne::.br_if 4::code)
    old 65535 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) second
  have constant := wp_i32_const cfg (fuel+4) _ (paid s op 1) limits (stack.push (.i32 old)) frame callers
    (.i32_binop .and::.local_get 2::.i32_relop .ne::.br_if 4::code) 65535 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) and
  have first := wp_local_get cfg (fuel+5) _ s limits stack frame callers
    (.i32_const 65535::.i32_binop .and::.local_get 2::.i32_relop .ne::.br_if 4::code) 2 (.i32 old) post h2
    (hc.mono (by dsimp [op];omega)) constant
  have cost : cfg.regularOpCost+(cfg.regularOpCost+(cfg.regularOpCost+(cfg.regularOpCost+(op+(op+rest)))))=6*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateGrowth.oldPagesGuard,List.cons_append,List.nil_append,cost,Nat.add_assoc,Nat.reduceAdd] using first

theorem wp_bytes_minimum (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (pages : UInt32) (mi : ModuleInst) (address573 address574 : Nat) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 pages))
    (hm : s.modules[frame.inst]?=some mi) (hi573 : mi.funcAddrs[573]?=some address573)
    (hf573 : s.funcs[address573]?=some (.wasm WNear.Binary.AllocateGrowth.signature573 frame.inst WNear.Binary.AllocateGrowth.function573))
    (hi574 : mi.funcAddrs[574]?=some address574)
    (hf574 : s.funcs[address574]?=some (.wasm WNear.Binary.AllocateUnits.minimumSignature frame.inst WNear.Binary.AllocateUnits.minimumFunction))
    (hpages : pages.toNat<65536) (hpositive : 0<pages.toNat)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (38*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (bytesAfter s cfg.regularOpCost) limits base.toArray (bytesFrame frame pages) callers code)) rest post) :
    WP cfg (fuel+23) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateGrowth.bytesAndMinimum++code)))
      (38*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let converted := after573 (paid s op 1) op
  let bf := bytesFrame frame pages
  have c1 := paid_credits s op 1 (19*op+(op+(17*op+rest))) (hc.mono (by dsimp [op];omega))
  have ce : converted.host.gas.Credits (op+(17*op+rest)) := by
    have a := StorePair.charged_credits (paid s op 1) op (9*op+(9*op+(op+(17*op+rest)))) (c1.mono (by omega))
    have b := StorePair.charged_credits (chargedStore (paid s op 1) op) (9*op) (9*op+(op+(17*op+rest))) a
    exact paid_credits _ op 9 _ b
  have hmT : (paid converted op 1).modules[bf.inst]?=some mi := by simpa only [converted,after573,paid,chargedStore,bf,bytesFrame] using hm
  have hfT : (paid converted op 1).funcs[address574]?=some (.wasm WNear.Binary.AllocateUnits.minimumSignature bf.inst WNear.Binary.AllocateUnits.minimumFunction) := by
    simpa only [converted,after573,paid,chargedStore,bf,bytesFrame] using hf574
  have minNext : WP cfg fuel (.next (atCode (AllocateUnits.minimumAfter (paid converted op 1) cfg.regularOpCost) limits base.toArray bf callers code)) rest post := by
    simpa only [bytesAfter,converted,bf,op] using hnext
  have bound : 8≤(pageBytes pages).toNat := by rw [pageBytes_toNat pages hpages];omega
  have minimum := AllocateUnits.wp_minimum_call cfg fuel rest (paid converted op 1) limits base bf callers code (pageBytes pages) mi address574 post
    hmT hi574 hfT bound hd (paid_credits converted op 1 _ (by simpa only [Nat.one_mul,op] using ce)) minNext
  have arr : (base++[Value.i32 (pageBytes pages)]).toArray=base.toArray.push (.i32 (pageBytes pages)) := by apply Array.toList_inj.mp;simp
  have teeNext : WP cfg (fuel+9) (.next (atCode (chargedStore converted cfg.regularOpCost) limits (base.toArray.push (.i32 (pageBytes pages))) bf callers (.call 574::code)))
      (17*op+rest) post := by simpa only [paid,op,arr] using minimum
  have tee := wp_local_tee cfg (fuel+9) (17*op+rest) converted limits base.toArray frame callers (.call 574::code) 4 (.i32 (pageBytes pages)) post ce
    (by simpa only [bf,bytesFrame] using teeNext)
  have hm1 : (paid s op 1).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have hf1 : (paid s op 1).funcs[address573]?=some (.wasm WNear.Binary.AllocateGrowth.signature573 frame.inst WNear.Binary.AllocateGrowth.function573) := by simpa only [paid,chargedStore] using hf573
  have call := wp_call573 cfg (fuel+10) (op+(17*op+rest)) (paid s op 1) limits base frame callers (.local_tee 4::.call 574::code)
    pages mi address573 post hm1 hi573 hf1 hpages hd c1 (by simpa only [converted,op,arr] using tee)
  have arrIn : (base++[Value.i32 pages]).toArray=base.toArray.push (.i32 pages) := by apply Array.toList_inj.mp;simp
  have first := wp_local_get cfg (fuel+22) (19*op+(op+(17*op+rest))) s limits base.toArray frame callers (.call 573::.local_tee 4::.call 574::code)
    3 (.i32 pages) post h3 (hc.mono (by dsimp [op];omega)) (by simpa only [arrIn,paid,op,Nat.add_assoc,Nat.reduceAdd] using call)
  have cost : cfg.regularOpCost+(19*op+(op+(17*op+rest)))=38*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateGrowth.bytesAndMinimum,List.cons_append,List.nil_append,cost,Nat.add_assoc,Nat.reduceAdd] using first
end WNear.Proofs.AllocateGrowth
