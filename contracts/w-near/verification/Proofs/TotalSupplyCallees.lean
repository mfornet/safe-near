import Proofs.TotalSupply
import Proofs.LoadedCallees
import Proofs.PackWords
import Proofs.ExpectResult
import Proofs.StorePairCaller
import NearVM.MeteredWasmCall

/-! Actual direct-call adapters for the named ft_total_supply callees. These
contracts execute the call opcode, activation, body and free caller return. -/
namespace WNear.Proofs.TotalSupplyCallees
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- The actual call opcode and callee activation are distinct charges. -/
def entered (s : Store NearState) (op activation : Nat) : Store NearState :=
  chargedStore (chargedStore s op) activation

def packedAfter (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) : Store NearState :=
  PackWords.packedStore (entered s op (9 * op)) op index out.toNat source.toNat memory

/-- f779 is an actual18unit/10step local call:1opcode,9activation,8body
instructions and one free leave. Its two sequential stores retain aliasing. -/
theorem packWords (cfg : WasmConfig) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (out source : UInt32) (address : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[779]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.PackWords.signature frame.inst WNear.Binary.PackWords.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) :
    CalleeContract cfg limits frame 779 [.i32 out, .i32 source] s
      (packedAfter s cfg.regularOpCost index out source memory) (18 * cfg.regularOpCost) 10 := by
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.PackWords.function [.i32 out, .i32 source]) = 9 * cfg.regularOpCost :=
    WNear.Binary.PackWords.activation_cost _ _ _
  constructor
  · intro rest hc
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    exact PackWords.packedStore_credits (entered s cfg.regularOpCost (9 * cfg.regularOpCost))
      cfg.regularOpCost index out.toNat source.toNat rest memory h2
  · intro fuel rest code post hc hnext
    let active := entered s cfg.regularOpCost (9 * cfg.regularOpCost)
    let leaf := StorePair.voidFrame #[.i32 out, .i32 source] frame.inst
    let saved := {frame with code := code}
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 : active.host.gas.Credits (8 * cfg.regularOpCost + rest) :=
      WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    have hfinal := PackWords.packedStore_credits active cfg.regularOpCost index out.toNat source.toNat rest memory h2
    have leaveRule := wp_leave_wasm cfg fuel rest (packedAfter s cfg.regularOpCost index out source memory)
      limits [] [] leaf saved [] post
    have leaveShape := leaveRule rfl rfl rfl
    have hleave := leaveShape hfinal hnext
    have hm : active.modules[frame.inst]? = some mi := by simpa only [active, entered, chargedStore] using hmodule
    have hmem : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmemory
    have bodyRule := PackWords.wp_body cfg (fuel + 1) rest active limits #[] leaf [saved] [] out source mi index memory post
    have bodyLocals := bodyRule rfl rfl
    have bodyEnv := bodyLocals hm hindex hmem hwf
    have bodyBounds := bodyEnv hread hwrite
    have bodyPaid := bodyBounds h2
    have hbody := bodyPaid hleave
    have callRule := wp_call_wasm cfg ((fuel + 1) + 8) (8 * cfg.regularOpCost + rest) s limits []
      [.i32 out, .i32 source] frame [] code 779 address mi WNear.Binary.PackWords.signature frame.inst WNear.Binary.PackWords.function post
    have callEnv := callRule hmodule haddress hfunction
    have callTyped := callEnv rfl hdepth
    rw [activation] at callTyped
    have callPaid := callTyped h0
    have nextBody : WP cfg ((fuel + 1) + 8)
        (.next (wasmCallee active limits [] frame [] code WNear.Binary.PackWords.signature frame.inst
          WNear.Binary.PackWords.function [.i32 out, .i32 source])) (8 * cfg.regularOpCost + rest) post := by
      simpa only [wasmCallee, wasmLocals, WNear.Binary.PackWords.function,
        WNear.Binary.PackWords.signature, StorePair.voidFrame, leaf, saved, atCode,
        List.map_nil, List.append_nil, List.length_nil, Array.append_empty, PackWords.body] using hbody
    have result := callPaid nextBody
    have budget : cfg.regularOpCost + (9 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest)) = 18 * cfg.regularOpCost + rest := by omega
    rw [budget] at result
    simpa only [List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

/-- Concrete accepted Result::expect effect after its call opcode and activation. -/
def expectAfter (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  ExpectResultState.finalStore (entered s op (10 * op)) op globalIndex memoryIndex sp out source memory

/-- The accepted f158 local call includes the branch's actual block entry and
free exit, then returns to the original caller. Discriminant one is excluded. -/
theorem expectResult (cfg : WasmConfig) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (sp out source location : UInt32) (address : Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[158]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ExpectResult.signature frame.inst WNear.Binary.ExpectResult.function))
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hsp : global.value = .i32 sp) (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hout : out.toNat + 12 ≤ memory.byteSize) (hsource : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1) (hdepth : 1 < limits.maxCallDepth) :
    CalleeContract cfg limits frame 158 [.i32 out, .i32 source, .i32 location] s
      (expectAfter s cfg.regularOpCost globalIndex memoryIndex sp out source memory) (37 * cfg.regularOpCost) 29 := by
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.ExpectResult.function [.i32 out, .i32 source, .i32 location]) = 10 * cfg.regularOpCost :=
    WNear.Binary.ExpectResult.activation_cost _ _ _ _
  constructor
  · intro rest hc
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (10 * cfg.regularOpCost + (26 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    exact (ExpectResultState.finalStore_gas (entered s cfg.regularOpCost (10 * cfg.regularOpCost))
      cfg.regularOpCost globalIndex memoryIndex rest sp out source memory h2).2.2
  · intro fuel rest code post hc hnext
    let active := entered s cfg.regularOpCost (10 * cfg.regularOpCost)
    let leaf := StorePair.voidFrame #[.i32 out, .i32 source, .i32 location, .i32 0] frame.inst
    let saved := {frame with code := code}
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (10 * cfg.regularOpCost + (26 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 : active.host.gas.Credits (26 * cfg.regularOpCost + rest) :=
      WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    have hfinal := (ExpectResultState.finalStore_gas active cfg.regularOpCost globalIndex memoryIndex rest sp out source memory h2).2.2
    have leaveRule := wp_leave_wasm cfg fuel rest (expectAfter s cfg.regularOpCost globalIndex memoryIndex sp out source memory)
      limits [] [] (ExpectResult.afterFrame leaf sp) saved [] post
    have leaveShape := leaveRule rfl rfl rfl
    have hleave := leaveShape hfinal hnext
    have hm : active.modules[frame.inst]? = some mi := by simpa only [active, entered, chargedStore] using hmodule
    have hg : active.globals[globalIndex]? = some global := by simpa only [active, entered, chargedStore] using hglobal
    have hmem : active.mems[memoryIndex]? = some memory := by simpa only [active, entered, chargedStore] using hmemory
    have bodyRule := ExpectResult.wp_body cfg (fuel + 1) rest active limits #[] leaf [saved] [] sp out source
      mi globalIndex memoryIndex global memory post
    have bodyLocals := bodyRule rfl rfl (by simp [leaf, StorePair.voidFrame])
    have bodyEnv := bodyLocals hm hglobalIndex hg hsp hmemoryIndex hmem hwf
    have bodyBounds := bodyEnv hwidth hout hsource htag
    have hbody := bodyBounds h2 hleave
    have callRule := wp_call_wasm cfg ((fuel + 1) + 27) (26 * cfg.regularOpCost + rest) s limits []
      [.i32 out, .i32 source, .i32 location] frame [] code 158 address mi WNear.Binary.ExpectResult.signature
      frame.inst WNear.Binary.ExpectResult.function post
    have callEnv := callRule hmodule haddress hfunction
    have callTyped := callEnv rfl hdepth
    rw [activation] at callTyped
    have callPaid := callTyped h0
    have locals_eq : #[Value.i32 out, .i32 source, .i32 location] ++ #[Value.i32 0] =
        #[Value.i32 out, .i32 source, .i32 location, .i32 0] := rfl
    have nextBody : WP cfg ((fuel + 1) + 27)
        (.next (wasmCallee active limits [] frame [] code WNear.Binary.ExpectResult.signature frame.inst
          WNear.Binary.ExpectResult.function [.i32 out, .i32 source, .i32 location])) (26 * cfg.regularOpCost + rest) post := by
      simpa only [wasmCallee, wasmLocals, WNear.Binary.ExpectResult.function,
        WNear.Binary.ExpectResult.signature, StorePair.voidFrame, leaf, saved, atCode,
        ValType.default, List.map_cons, List.map_nil, List.append_nil, List.length_nil, Array.append_empty, locals_eq] using hbody
    have result := callPaid nextBody
    have budget : cfg.regularOpCost + (10 * cfg.regularOpCost + (26 * cfg.regularOpCost + rest)) = 37 * cfg.regularOpCost + rest := by omega
    rw [budget] at result
    simpa only [List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

/-- Concrete f414 effect, including its nested f566 call. -/
def supplyAfter (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  StorePairCaller.finalStore (entered s op (11 * op)) op globalIndex memoryIndex sp out memory
    (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))

/-- The actual f414 local call pays58units and takes38steps including both
callee leaves. Two available call-depth slots account for its nested f566. -/
theorem readSupply (cfg : WasmConfig) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (sp out source : UInt32) (address helperAddress : Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[414]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.StorePairCaller.signature frame.inst WNear.Binary.StorePairCaller.function))
    (hhelperAddress : mi.funcAddrs[566]? = some helperAddress)
    (hhelper : s.funcs[helperAddress]? = some (.wasm WNear.Binary.StorePair.signature frame.inst WNear.Binary.StorePair.function))
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hspValue : global.value = .i32 sp) (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (hout : out.toNat + 16 ≤ memory.byteSize) (hsource : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 2 < limits.maxCallDepth) :
    CalleeContract cfg limits frame 414 [.i32 out, .i32 source] s
      (supplyAfter s cfg.regularOpCost globalIndex memoryIndex sp out source memory) (58 * cfg.regularOpCost) 38 := by
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.StorePairCaller.function [.i32 out, .i32 source]) = 11 * cfg.regularOpCost :=
    WNear.Binary.StorePairCaller.activation_cost _ _ _
  constructor
  · intro rest hc
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (11 * cfg.regularOpCost + (46 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    exact (StorePairCaller.finalStore_gas (entered s cfg.regularOpCost (11 * cfg.regularOpCost))
      cfg.regularOpCost globalIndex memoryIndex rest sp out memory (readI64 memory source.toNat)
      (readI64 memory (source.toNat + 8)) h2).2.2
  · intro fuel rest code post hc hnext
    let active := entered s cfg.regularOpCost (11 * cfg.regularOpCost)
    let leaf := StorePair.voidFrame #[.i32 out, .i32 source, .i32 0, .i64 0] frame.inst
    let finished := {leaf with locals := (leaf.locals.set! 2 (.i32 (sp - 16))).set! 3 (.i64 (readI64 memory source.toNat))}
    let saved := {frame with code := code}
    have h0 : s.host.gas.Credits (cfg.regularOpCost + (11 * cfg.regularOpCost + (46 * cfg.regularOpCost + rest))) := hc.mono (by omega)
    have h1 := WNear.Proofs.StorePair.charged_credits s _ _ h0
    have h2 : active.host.gas.Credits (46 * cfg.regularOpCost + rest) :=
      WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
    have hfinal := (StorePairCaller.finalStore_gas active cfg.regularOpCost globalIndex memoryIndex rest sp out memory
      (readI64 memory source.toNat) (readI64 memory (source.toNat + 8)) h2).2.2
    have leaveRule := wp_leave_wasm cfg fuel rest (supplyAfter s cfg.regularOpCost globalIndex memoryIndex sp out source memory)
      limits [] [] finished saved [] post
    have leaveShape := leaveRule rfl rfl rfl
    have hleave := leaveShape hfinal hnext
    have hm : active.modules[frame.inst]? = some mi := by simpa only [active, entered, chargedStore] using hmodule
    have hg : active.globals[globalIndex]? = some global := by simpa only [active, entered, chargedStore] using hglobal
    have hf : active.funcs[helperAddress]? = some (.wasm WNear.Binary.StorePair.signature frame.inst WNear.Binary.StorePair.function) := by
      simpa only [active, entered, chargedStore] using hhelper
    have hmem : active.mems[memoryIndex]? = some memory := by simpa only [active, entered, chargedStore] using hmemory
    have nestedDepth : [saved].length + 1 < limits.maxCallDepth := by simpa using hdepth
    have bodyRule := StorePairCaller.wp_body cfg (fuel + 1) rest active limits [] leaf [saved] []
      mi globalIndex memoryIndex helperAddress global memory sp out source post
    have bodyLocals := bodyRule rfl rfl (by simp [leaf, StorePair.voidFrame])
    have bodyEnv := bodyLocals hm hglobalIndex hg hspValue hhelperAddress hf hmemoryIndex hmem hwf
    have bodyBounds := bodyEnv hwidth hsp hstack hout hsource nestedDepth
    have hbody := bodyBounds h2 hleave
    have callRule := wp_call_wasm cfg ((fuel + 1) + 36) (46 * cfg.regularOpCost + rest) s limits []
      [.i32 out, .i32 source] frame [] code 414 address mi WNear.Binary.StorePairCaller.signature
      frame.inst WNear.Binary.StorePairCaller.function post
    have callEnv := callRule hmodule haddress hfunction
    have firstDepth : ([] : List CallFrame).length + 1 < limits.maxCallDepth := by simpa using Nat.lt_trans (by decide : 1 < 2) hdepth
    have callTyped := callEnv rfl firstDepth
    rw [activation] at callTyped
    have callPaid := callTyped h0
    have locals_eq : #[Value.i32 out, .i32 source] ++ #[Value.i32 0, .i64 0] =
        #[Value.i32 out, .i32 source, .i32 0, .i64 0] := rfl
    have nextBody : WP cfg ((fuel + 1) + 36)
        (.next (wasmCallee active limits [] frame [] code WNear.Binary.StorePairCaller.signature frame.inst
          WNear.Binary.StorePairCaller.function [.i32 out, .i32 source])) (46 * cfg.regularOpCost + rest) post := by
      simpa only [wasmCallee, wasmLocals, WNear.Binary.StorePairCaller.function,
        WNear.Binary.StorePairCaller.signature, StorePair.voidFrame, leaf, saved, atCode,
        ValType.default, List.map_cons, List.map_nil, List.append_nil, List.length_nil, Array.append_empty, StorePairCaller.body, locals_eq] using hbody
    have result := callPaid nextBody
    have budget : cfg.regularOpCost + (11 * cfg.regularOpCost + (46 * cfg.regularOpCost + rest)) = 58 * cfg.regularOpCost + rest := by omega
    rw [budget] at result
    simpa only [List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

/-- Actual deployed installation supplies both the function address and code. -/
theorem packWords_installed (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi) (hinst : frame.inst = 0)
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) :
    CalleeContract cfg.wasm limits frame 779 [.i32 out, .i32 source] s
      (packedAfter s cfg.wasm.regularOpCost index out source memory) (18 * cfg.wasm.regularOpCost) 10 := by
  have info := LoadedCallees.functions cfg host s mi hload 731
    WNear.Binary.PackWords.function WNear.Binary.PackWords.signature
    WNear.Binary.PackWords.module_function WNear.Binary.PackWords.module_signature
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact info.2.2
  have hf : s.funcs[779]? = some (.wasm WNear.Binary.PackWords.signature frame.inst WNear.Binary.PackWords.function) := by
    rw [hinst]; exact info.2.1
  exact packWords cfg.wasm limits frame s out source 779 mi index memory hm info.1 hf
    hindex hmemory hwf hread hwrite hdepth

theorem expectResult_installed (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (sp out source location : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi) (hinst : frame.inst = 0)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hsp : global.value = .i32 sp) (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hout : out.toNat + 12 ≤ memory.byteSize) (hsource : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1) (hdepth : 1 < limits.maxCallDepth) :
    CalleeContract cfg.wasm limits frame 158 [.i32 out, .i32 source, .i32 location] s
      (expectAfter s cfg.wasm.regularOpCost globalIndex memoryIndex sp out source memory) (37 * cfg.wasm.regularOpCost) 29 := by
  have info := LoadedCallees.functions cfg host s mi hload 110
    WNear.Binary.ExpectResult.function WNear.Binary.ExpectResult.signature
    WNear.Binary.ExpectResult.module_function WNear.Binary.ExpectResult.module_signature
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact info.2.2
  have hf : s.funcs[158]? = some (.wasm WNear.Binary.ExpectResult.signature frame.inst WNear.Binary.ExpectResult.function) := by
    rw [hinst]; exact info.2.1
  exact expectResult cfg.wasm limits frame s sp out source location 158 mi globalIndex memoryIndex global memory
    hm info.1 hf hglobalIndex hglobal hsp hmemoryIndex hmemory hwf hwidth hout hsource htag hdepth

theorem readSupply_installed (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits) (frame : CallFrame)
    (s : Store NearState) (sp out source : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi) (hinst : frame.inst = 0)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hspValue : global.value = .i32 sp) (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (hout : out.toNat + 16 ≤ memory.byteSize) (hsource : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 2 < limits.maxCallDepth) :
    CalleeContract cfg.wasm limits frame 414 [.i32 out, .i32 source] s
      (supplyAfter s cfg.wasm.regularOpCost globalIndex memoryIndex sp out source memory) (58 * cfg.wasm.regularOpCost) 38 := by
  have info := LoadedCallees.functions cfg host s mi hload 366
    WNear.Binary.StorePairCaller.function WNear.Binary.StorePairCaller.signature
    WNear.Binary.StorePairCaller.module_function WNear.Binary.StorePairCaller.module_signature
  have helper := LoadedCallees.functions cfg host s mi hload 518
    WNear.Binary.StorePair.function WNear.Binary.StorePair.signature
    WNear.Binary.StorePair.module_function WNear.Binary.StorePair.module_signature
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact info.2.2
  have hf : s.funcs[414]? = some (.wasm WNear.Binary.StorePairCaller.signature frame.inst WNear.Binary.StorePairCaller.function) := by
    rw [hinst]; exact info.2.1
  have hh : s.funcs[566]? = some (.wasm WNear.Binary.StorePair.signature frame.inst WNear.Binary.StorePair.function) := by
    rw [hinst]; exact helper.2.1
  exact readSupply cfg.wasm limits frame s sp out source 414 566 mi globalIndex memoryIndex global memory
    hm info.1 hf helper.1 hh hglobalIndex hglobal hspValue hmemoryIndex hmemory hwf hwidth hsp hstack hout hsource hdepth

end WNear.Proofs.TotalSupplyCallees
