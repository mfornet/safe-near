import Proofs.StateDecodeScalarBody
import NearVM.MeteredWasmCall

/-! Actual typed deployed f372/f371 calls. The selected bodies return explicitly,
so there is no extra free callee-leave transition. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after

def entered (wide : Bool) (s : Store NearState) (op : Nat) :=
  chargedStore (chargedStore s op) (activationUnits wide*op)
def callAfter (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  after wide cfg (entered wide s cfg.regularOpCost) p
def leafFrame (wide : Bool) (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.out,.i32 p.slice,.i32 0,.i32 0,.i64 0,.i64 0]++(if wide then #[.i64 0] else #[]),
   inst,arity:=0,height,labels:=[],code:=[]}

theorem entered_credits (wide : Bool) (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits ((activationUnits wide+1)*op+rest)) :
    (entered wide s op).host.gas.Credits rest := by
  have c0:=StorePair.charged_credits s op (activationUnits wide*op+rest) (hc.mono (by simp only[Nat.add_mul];omega))
  exact StorePair.charged_credits (chargedStore s op) (activationUnits wide*op) rest c0

theorem callAfter_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost wide+activationUnits wide+1)*cfg.regularOpCost+rest)) :
    (callAfter wide cfg s p).host.gas.Credits rest :=
  after_credits wide cfg (entered wide s cfg.regularOpCost) p rest
    (entered_credits wide s cfg.regularOpCost _ (hc.mono (by simp only[Nat.add_mul];omega)))

/-- The complete accepted u128/u64 reader, from original memory bounds and
installed deployed descriptors. Source, result and slice aliases remain allowed. -/
theorem wp_call (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native wide p) (hcode : Code wide s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global)
    (hv : p.global.value=.i32 p.sp)
    (hi : p.mi.funcAddrs[if wide then 372 else 371]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeScalar.signature frame.inst (WNear.Binary.StateDecodeScalar.function wide)))
    (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((bodyCost wide+activationUnits wide+1)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter wide cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+bodySteps wide+1) (.next (atCode s limits (base++[Value.i32 p.out,.i32 p.slice]).toArray frame callers
      (.call (if wide then 372 else 371)::code)))
      ((bodyCost wide+activationUnits wide+1)*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=entered wide s op
  let leaf:=leafFrame wide frame.inst base.length p
  let saved:={frame with code}
  have ca:=entered_credits wide s op (bodyCost wide*op+rest) (hc.mono (by simp only[Nat.add_mul,op];omega))
  have ac : Code wide active leaf.inst p := by
    have cc : Code wide active frame.inst p:=hcode.transport rfl rfl
    simpa only [leaf,leafFrame] using cc
  have bn : WP cfg fuel (.next (atCode (after wide cfg active p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only[callAfter,active,op,saved,atCode] using hnext
  have body:=wp_body wide cfg fuel rest active limits base leaf saved callers [] p post hn ac hm hg hv
    (by cases wide <;> rfl) (by cases wide <;> rfl)
    (by cases wide <;> simp[leaf,leafFrame]) rfl rfl hd ca bn
  have ae : activationGas op (wasmLocals (WNear.Binary.StateDecodeScalar.function wide) [.i32 p.out,.i32 p.slice])=activationUnits wide*op := by
    cases wide <;> simp[wasmLocals,WNear.Binary.StateDecodeScalar.function,ValType.default,activationGas,activationUnits]
  have cr:=wp_call_wasm cfg (fuel+bodySteps wide) (bodyCost wide*op+rest) s limits base [.i32 p.out,.i32 p.slice]
    frame callers code (if wide then 372 else 371) address p.mi WNear.Binary.StateDecodeScalar.signature frame.inst
    (WNear.Binary.StateDecodeScalar.function wide) post hcode.module hi hf rfl (by omega)
  rw [ae] at cr
  have actual : WP cfg (fuel+bodySteps wide) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateDecodeScalar.signature frame.inst (WNear.Binary.StateDecodeScalar.function wide) [.i32 p.out,.i32 p.slice]))
      (bodyCost wide*op+rest) post := by
    cases wide <;> simpa [WNear.Binary.StateDecodeScalar.function,WNear.Binary.StateDecodeScalar.signature,
      leaf,leafFrame,wasmCallee,wasmLocals,ValType.default,saved,atCode,op] using body
  have proof:=cr (hc.mono (by simp only[Nat.add_mul,op];omega)) actual
  have ce : cfg.regularOpCost+(activationUnits wide*op+(bodyCost wide*op+rest))=
      (bodyCost wide+activationUnits wide+1)*cfg.regularOpCost+rest := by simp only[Nat.add_mul,op];omega
  simpa only[ce] using proof
end WNear.Proofs.StateDecodeScalar
