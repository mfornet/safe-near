import Proofs.DeallocatePrevious
import NearVM.MeteredSelectionRules

/-! The deployed next-neighbor guard when header bit2 disables coalescing.
Both branch conditions follow from the loaded original word. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

def rawNextFrame(frame:CallFrame)(word:UInt32):={frame with locals:=frame.locals.set! 5 (.i32 word)}
def maskedNextFrame(frame:CallFrame)(word:UInt32):=
  {rawNextFrame frame word with locals:=(rawNextFrame frame word).locals.set! 6 (.i32 (word&&&4294967292))}
def disabledNextFrame(frame:CallFrame)(word:UInt32):=
  {maskedNextFrame frame word with locals:=(maskedNextFrame frame word).locals.set! 5 (.i32 0)}

private theorem paid_plus(s:Store NearState)(op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with
  |zero=>rfl
  |succ b ih=>change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op;rw[ih]

theorem wp_next_disabled(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code inner discarded:Expr)
    (header:UInt32)(mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (hh:frame.locals[2]?=some (.i32 header))(hs:7≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:header.toNat+4≤memory.byteSize)
    (hnz:readI32 memory header.toNat&&&4294967292≠0)(hbit:readI32 memory header.toNat&&&2≠0)
    (hc:s.host.gas.Credits (17*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 17) limits stack
      (disabledNextFrame frame (readI32 memory header.toNat)) callers code)) rest post):
    WP cfg (fuel+17) (.next (atCode s limits stack
      (emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size inner) callers
      ((WNear.Binary.Deallocate.nextGuard.take 17)++discarded))) (17*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let word:=readI32 memory header.toNat
  let masked:=word&&&4294967292
  let f0:=emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size inner
  let f1:=rawNextFrame f0 word
  let f2:=maskedNextFrame f0 word
  let f3:=disabledNextFrame f0 word
  have hz:Numeric.bool (masked==0)=0:=by simp[Numeric.bool,masked,word,hnz]
  have hm1:(paid s op 1).modules[f0.inst]?=some mi:=by simpa only[paid,chargedStore,f0,emptyBlockFrame] using hm
  have he1:(paid s op 1).mems[index]?=some memory:=by simpa only[paid,chargedStore] using he
  have five:f2.locals[5]?=some (.i32 word):=by
    simp[f2,maskedNextFrame,rawNextFrame,f0,emptyBlockFrame,Array.set!,show 5<frame.locals.size by omega]
  have six:f2.locals[6]?=some (.i32 masked):=by
    simp[f2,maskedNextFrame,rawNextFrame,f0,emptyBlockFrame,Array.set!,masked,show 6<frame.locals.size by omega]
  change WP cfg (fuel+17) (.next (atCode s limits stack f0 callers
    ([.local_get 2,.load .i32 none {align:=2,offset:=0},.local_tee 5,.i32_const 4294967292,.i32_binop .and,.local_tee 6,.i32_eqz,.br_if 1,
      .i32_const 0,.local_get 6,.local_get 5,.i32_const 2,.i32_binop .and,.select none,.local_tee 5,.i32_eqz,.br_if 1]++discarded))) (17*op+rest) post
  rw[show 17*op+rest=op+(16*op+rest) by omega]
  apply wp_local_get cfg (fuel+16) _ s limits stack f0 callers _ 2 (.i32 header) post hh (hc.mono (by dsimp[op];omega))
  rw[show 16*op+rest=op+(15*op+rest) by omega]
  apply wp_i32_load cfg (fuel+15) _ (paid s op 1) limits stack f0 callers _ {align:=2,offset:=0} header mi index memory post hm1 hi he1 (by simpa only[Nat.add_zero] using hb)
  · exact paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))
  simp only[Nat.add_zero]
  rw[show 15*op+rest=op+(14*op+rest) by omega]
  apply wp_local_tee cfg (fuel+14) _ (paid s op 2) limits stack f0 callers _ 5 (.i32 word) post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))
  rw[show 14*op+rest=op+(13*op+rest) by omega]
  apply wp_i32_const cfg (fuel+13) _ (paid s op 3) limits _ f1 callers _ 4294967292 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))
  rw[show 13*op+rest=op+(12*op+rest) by omega]
  apply wp_i32_and cfg (fuel+12) _ (paid s op 4) limits stack f1 callers _ word 4294967292 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))
  rw[show 12*op+rest=op+(11*op+rest) by omega]
  apply wp_local_tee cfg (fuel+11) _ (paid s op 5) limits stack f1 callers _ 6 (.i32 masked) post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  rw[show 11*op+rest=op+(10*op+rest) by omega]
  apply wp_i32_eqz cfg (fuel+10) _ (paid s op 6) limits stack f2 callers _ masked post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))
  rw[hz]
  rw[show 10*op+rest=op+(9*op+rest) by omega]
  apply wp_br_if_zero cfg (fuel+9) _ (paid s op 7) limits stack f2 callers _ 1 post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))
  rw[show 9*op+rest=op+(8*op+rest) by omega]
  apply wp_i32_const cfg (fuel+8) _ (paid s op 8) limits stack f2 callers _ 0 post
  · exact paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))
  rw[show 8*op+rest=op+(7*op+rest) by omega]
  apply wp_local_get cfg (fuel+7) _ (paid s op 9) limits _ f2 callers _ 6 (.i32 masked) post six
  · exact paid_credits s op 9 _ (hc.mono (by dsimp[op];omega))
  rw[show 7*op+rest=op+(6*op+rest) by omega]
  apply wp_local_get cfg (fuel+6) _ (paid s op 10) limits _ f2 callers _ 5 (.i32 word) post five
  · exact paid_credits s op 10 _ (hc.mono (by dsimp[op];omega))
  rw[show 6*op+rest=op+(5*op+rest) by omega]
  apply wp_i32_const cfg (fuel+5) _ (paid s op 11) limits _ f2 callers _ 2 post
  · exact paid_credits s op 11 _ (hc.mono (by dsimp[op];omega))
  rw[show 5*op+rest=op+(4*op+rest) by omega]
  apply wp_i32_and cfg (fuel+4) _ (paid s op 12) limits _ f2 callers _ word 2 post
  · exact paid_credits s op 12 _ (hc.mono (by dsimp[op];omega))
  rw[show 4*op+rest=op+(3*op+rest) by omega]
  apply wp_select cfg (fuel+3) _ (paid s op 13) limits stack f2 callers _ (.i32 0) (.i32 masked) (word&&&2) post
  · exact paid_credits s op 13 _ (hc.mono (by dsimp[op];omega))
  have choice:(if word&&&2≠0 then Value.i32 0 else .i32 masked)=.i32 0:=by split <;> simp_all only [word]
  rw[choice]
  rw[show 3*op+rest=op+(2*op+rest) by omega]
  apply wp_local_tee cfg (fuel+2) _ (paid s op 14) limits stack f2 callers _ 5 (.i32 0) post
  · exact paid_credits s op 14 _ (hc.mono (by dsimp[op];omega))
  rw[show 2*op+rest=op+(op+rest) by omega]
  apply wp_i32_eqz cfg (fuel+1) _ (paid s op 15) limits stack f3 callers _ 0 post
  · exact paid_credits s op 15 _ (hc.mono (by dsimp[op];omega))
  have branch:=wp_br_if_two_blocks_nonzero cfg fuel rest (paid s op 16) limits stack (disabledNextFrame frame word) callers code inner discarded 1 post (by decide)
    (paid_credits s op 16 _ (hc.mono (by dsimp[op];omega))) hnext
  simpa only[f3,f0,disabledNextFrame,maskedNextFrame,rawNextFrame,emptyBlockFrame,Numeric.bool,beq_self_eq_true,ite_true,paid,op,List.append_eq,List.cons_append,List.nil_append] using branch
end WNear.Proofs.DeallocateInsert
