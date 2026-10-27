import Proofs.StateReadResult
import NearVM.MeteredWasmCall

/-! Typed normal call of deployed f498 on a present result. -/
namespace WNear.Proofs.StateReadResult
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11 * op)
def callAfter (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  after (entered s op) op index memory out source

theorem callAfter_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (27 * op + rest)) :
    (callAfter s op index memory out source).host.gas.Credits rest := by
  have h0 := (GasCounter.burn_credits s.host.gas op (11 * op + (15 * op + rest)) (hc.mono (by omega))).2.2.2
  have h1 := (GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (15 * op + rest) h0).2.2.2
  exact after_credits (entered s op) op index rest memory out source h1

/-- All actual call/activation/body/normal-leave steps. The caller's arbitrary
operand prefix and frame are restored, with the precise sequential memory. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source message length location : UInt32)
    (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[498]? = some address)
    (hfn : s.funcs[address]? = some (.wasm WNear.Binary.StateRead.resultSignature frame.inst WNear.Binary.StateRead.resultFunction))
    (hwf : memory.wf) (hob : out.toNat + 8 ≤ memory.byteSize) (hsb : source.toNat + 8 ≤ memory.byteSize)
    (hoh : (out + 8).toNat + 4 ≤ memory.byteSize) (hsh : (source + 8).toNat + 4 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 0) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index memory out source) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 18) (.next (atCode s limits
      (base ++ [Value.i32 out,.i32 source,.i32 message,.i32 length,.i32 location]).toArray frame callers (.call 498 :: code)))
      (27 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {
    locals := #[.i32 out,.i32 source,.i32 message,.i32 length,.i32 location],
    inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have h0 := (GasCounter.burn_credits s.host.gas op (11 * op + (15 * op + rest)) (hc.mono (by dsimp [op]; omega))).2.2.2
  have h1 := (GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (15 * op + rest) h0).2.2.2
  have cf := callAfter_credits s op index rest memory out source hc
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op index memory out source) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op,List.append_nil] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter s op index memory out source) limits base [] leaf saved callers post rfl rfl rfl cf leaveNext
  have bn : WP cfg (fuel + 1) (.next (atCode (after active op index memory out source) limits base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using left
  have hma : active.modules[leaf.inst]? = some mi := by simpa only [active,entered,chargedStore,leaf] using hm
  have hmea : active.mems[index]? = some memory := by simpa only [active,entered,chargedStore] using hmem
  have body := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] out source mi index memory post
    rfl rfl hma hi hmea hwf hob hsb hoh hsh htag h1 bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 16) (15 * op + rest) s limits base
    [.i32 out,.i32 source,.i32 message,.i32 length,.i32 location] frame callers code 498 address mi
    WNear.Binary.StateRead.resultSignature frame.inst WNear.Binary.StateRead.resultFunction post hm hfi hfn rfl hd
  have ac : activationGas op (wasmLocals WNear.Binary.StateRead.resultFunction
      [.i32 out,.i32 source,.i32 message,.i32 length,.i32 location]) = 11 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateRead.resultFunction]
  rw [ac] at cr
  have next : WP cfg ((fuel + 1) + 16) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateRead.resultSignature frame.inst WNear.Binary.StateRead.resultFunction
      [.i32 out,.i32 source,.i32 message,.i32 length,.i32 location])) (15 * op + rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.StateRead.resultFunction,WNear.Binary.StateRead.resultSignature,
      op,leaf,saved,atCode,List.length_nil,List.map_cons,List.map_nil,List.append_nil,Array.append_empty] using body
  have result := cr (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (11 * op + (15 * op + rest)) = 27 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.StateReadResult
