import Proofs.UnwrapState

/-! Actual accepted f155 call: the call opcode, activation, complete copy loop,
and caller return. The nonzero tag is an explicit memory representation fact. -/
namespace WNear.Proofs.UnwrapStateCallees
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

def entered (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (9 * op)

def callAfter (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) : Store NearState :=
  UnwrapState.finalStore (entered s op) op index out source memory

theorem unwrapState (cfg : WasmConfig) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (out source : UInt32) (address copyAddress : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[155]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.UnwrapState.signature frame.inst WNear.Binary.UnwrapState.function))
    (hcopyAddress : mi.funcAddrs[951]? = some copyAddress)
    (hcopy : s.funcs[copyAddress]? = some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + 40 ≤ memory.byteSize) (hwrite : out.toNat + 40 ≤ memory.byteSize)
    (htag : readI32 memory (source.toNat + 24) ≠ 0) (hdepth : 2 < limits.maxCallDepth) :
    CalleeContract cfg limits frame 155 [.i32 out, .i32 source] s
      (callAfter s cfg.regularOpCost index out source memory) (754 * cfg.regularOpCost) 702 := by
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.UnwrapState.function [.i32 out, .i32 source]) = 9 * cfg.regularOpCost :=
    WNear.Binary.UnwrapState.activation_cost _ _ _
  constructor
  · intro rest hc
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (744 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    exact UnwrapState.finalStore_credits (entered s cfg.regularOpCost) cfg.regularOpCost index out source memory rest h2
  · intro fuel rest code post hc hnext
    let active := entered s cfg.regularOpCost
    let leaf := StorePair.voidFrame #[.i32 out, .i32 source] frame.inst
    let saved := {frame with code := code}
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (744 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 : active.host.gas.Credits (744 * cfg.regularOpCost + rest) :=
      WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    have hfinal := UnwrapState.finalStore_credits active cfg.regularOpCost index out source memory rest h2
    have leaveRule := wp_leave_wasm cfg fuel rest (callAfter s cfg.regularOpCost index out source memory)
      limits [] [] leaf saved [] post
    have leaveShape := leaveRule rfl rfl rfl
    have hleave := leaveShape hfinal hnext
    have hm : active.modules[frame.inst]? = some mi := by simpa only [active, entered, chargedStore] using hmodule
    have hf : active.funcs[copyAddress]? = some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function) := by
      simpa only [active, entered, chargedStore] using hcopy
    have hmem : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmemory
    have bodyRule := UnwrapState.wp_body cfg (fuel + 1) rest active limits [] leaf [saved] [] out source copyAddress mi index memory post
    have bodyLocals := bodyRule rfl rfl
    have bodyEnv := bodyLocals hm hcopyAddress hf hindex hmem hwf
    have bodyBounds := bodyEnv hwidth hread hwrite htag hdepth
    have bodyPaid := bodyBounds h2
    have hbody := bodyPaid hleave
    have callRule := wp_call_wasm cfg ((fuel + 1) + 700) (744 * cfg.regularOpCost + rest) s limits []
      [.i32 out, .i32 source] frame [] code 155 address mi WNear.Binary.UnwrapState.signature frame.inst WNear.Binary.UnwrapState.function post
    have callEnv := callRule hmodule haddress hfunction
    have callTyped := callEnv rfl (by simp only [List.length_nil]; omega)
    rw [activation] at callTyped
    have callPaid := callTyped h0
    have nextBody : WP cfg ((fuel + 1) + 700)
        (.next (wasmCallee active limits [] frame [] code WNear.Binary.UnwrapState.signature frame.inst
          WNear.Binary.UnwrapState.function [.i32 out, .i32 source])) (744 * cfg.regularOpCost + rest) post := by
      simpa only [wasmCallee, wasmLocals, WNear.Binary.UnwrapState.function,
        WNear.Binary.UnwrapState.signature, StorePair.voidFrame, leaf, saved, atCode,
        List.map_nil, List.append_nil, List.length_nil, Array.append_empty] using hbody
    have result := callPaid nextBody
    have budget : cfg.regularOpCost + (9 * cfg.regularOpCost + (744 * cfg.regularOpCost + rest)) = 754 * cfg.regularOpCost + rest := by omega
    rw [budget] at result
    simpa only [List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

/-- Loader-derived actual155 and951 code tables; only memory representation,
native bounds and call-depth resources remain explicit. -/
theorem unwrapState_installed (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (frame : CallFrame) (s : Store NearState) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi) (hinst : frame.inst = 0)
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + 40 ≤ memory.byteSize) (hwrite : out.toNat + 40 ≤ memory.byteSize)
    (htag : readI32 memory (source.toNat + 24) ≠ 0) (hdepth : 2 < limits.maxCallDepth) :
    CalleeContract cfg.wasm limits frame 155 [.i32 out, .i32 source] s
      (callAfter s cfg.wasm.regularOpCost index out source memory) (754 * cfg.wasm.regularOpCost) 702 := by
  have info := LoadedCallees.functions cfg host s mi hload 107
    WNear.Binary.UnwrapState.function WNear.Binary.UnwrapState.signature
    WNear.Binary.UnwrapState.module_function WNear.Binary.UnwrapState.module_signature
  have helper := LoadedCallees.functions cfg host s mi hload 903
    WNear.Binary.UnwrapState.Copy.function WNear.Binary.UnwrapState.Copy.signature
    WNear.Binary.UnwrapState.Copy.module_function WNear.Binary.UnwrapState.Copy.module_signature
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact info.2.2
  have hf : s.funcs[155]? = some (.wasm WNear.Binary.UnwrapState.signature frame.inst WNear.Binary.UnwrapState.function) := by
    rw [hinst]; exact info.2.1
  have hh : s.funcs[951]? = some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function) := by
    rw [hinst]; exact helper.2.1
  exact unwrapState cfg.wasm limits frame s out source 155 951 mi index memory
    hm info.1 hf helper.1 hh hindex hmemory hwf hwidth hread hwrite htag hdepth

end WNear.Proofs.UnwrapStateCallees
