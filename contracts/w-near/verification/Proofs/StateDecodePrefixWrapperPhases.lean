import Proofs.StateDecodePrefixWrapperResources
import Proofs.StateDecodePrefixWrapperTailFrame

/-! Full315 accepted result snapshots. Both copied values are read from the
actual316 final memory before either caller output write. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic

def tailLayout(p:Layout)(q:StateDecodeVectorCopy.Layout):Tail.Layout:=
  {memory:=StateDecodePrefix.finalMemory p.toPrefix q,index:=p.memoryIndex,globalIndex:=p.globalIndex,out:=p.wrapperOut,pointer:=scratch p}
def after(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  Tail.after (decoded cfg s p q) cfg.regularOpCost (tailLayout p q)
def finalMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=Tail.finalMemory (tailLayout p q)
def finalFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=Tail.finalFrame (reservedFrame frame p) (tailLayout p q)
def bodyCost(p:Layout):=18*(StateDecodePrefix.count p.toPrefix).toNat+960
def bodySteps(p:Layout):=17*(StateDecodePrefix.count p.toPrefix).toNat+769

theorem after_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (rest:Nat)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest)):
    (after cfg s p q).host.gas.Credits rest:=by
  let op:=cfg.regularOpCost
  apply Tail.after_credits (decoded cfg s p q) op rest (tailLayout p q)
  exact decoded_credits cfg s p q (33*op+rest) hn hd (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega))
end WNear.Proofs.StateDecodePrefixWrapper
