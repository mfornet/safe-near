import Binary.InstalledCallees
import Proofs.StorePairEntry
import Proofs.StorePairCallerEntry
import Proofs.PackWordsEntry
import Proofs.ExpectResultEntry
import Proofs.TotalSupplyEntry

/-! Entry contracts connected to actual host allocation and deployed linking. -/
namespace WNear.Proofs.LoadedCallees
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- Successful validation and linking of the actual prepared deployed module.
No guest execution equation or function-table lookup is included. -/
def Loaded (cfg : RuntimeConfig) (host : NearState) (s : Store NearState)
    (inst : ModuleInst) : Prop :=
  ∃ vm, (prepareMemory cfg WNear.Binary.wNearModule).validate (Features.nearcore true) = .ok vm ∧
    Link.instantiateModule ((WNear.Binary.ImportLayout.hosts cfg).allocate (Store.empty host)).1 vm
      ((WNear.Binary.ImportLayout.hosts cfg).allocate (Store.empty host)).2 = .ok (s, inst)

/-- Executing code may change host, memories and globals. The installed code
is retained from one actual successful load. -/
def Installed (cfg : RuntimeConfig) (host : NearState) (s : Store NearState)
    (inst : ModuleInst) : Prop :=
  ∃ loaded, Loaded cfg host loaded inst ∧ s.funcs = loaded.funcs ∧ s.modules = loaded.modules

theorem loaded_installed (cfg : RuntimeConfig) (host : NearState) (s : Store NearState)
    (inst : ModuleInst) (h : Loaded cfg host s inst) : Installed cfg host s inst :=
  ⟨s, h, rfl, rfl⟩

/-- The code invariant survives any update retaining functions and modules. -/
theorem installed_frame (cfg : RuntimeConfig) (host : NearState) (s t : Store NearState)
    (inst : ModuleInst) (h : Installed cfg host s inst)
    (hf : t.funcs = s.funcs) (hm : t.modules = s.modules) : Installed cfg host t inst := by
  rcases h with ⟨loaded, hl, hfs, hms⟩
  exact ⟨loaded, hl, hf.trans hfs, hm.trans hms⟩

/-- The runtime's empty initial store fixes installed addresses and module slot. -/
theorem functions (cfg : RuntimeConfig) (host : NearState) (s : Store NearState)
    (inst : ModuleInst) (hload : Installed cfg host s inst)
    (n : Nat) (function : Func) (signature : FuncType)
    (hf : WNear.Binary.wNearModule.funcs[n]? = some function)
    (ht : WNear.Binary.wNearModule.types[function.type]? = some signature) :
    inst.funcAddrs[48 + n]? = some (48 + n) ∧
    s.funcs[48 + n]? = some (.wasm signature 0 function) ∧
    s.modules[0]? = some inst := by
  rcases hload with ⟨loaded, ⟨vm, hv, hl⟩, hfs, hms⟩
  have h := WNear.Binary.InstalledCallees.from_empty cfg host vm loaded inst hv hl n function signature hf ht
  simpa only [hfs, hms] using h

theorem storePair (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (address : UInt32) (lo hi : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hload : Installed cfg host s mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hbound : address.toNat + 16 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (17 * cfg.wasm.regularOpCost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[566]! [.i32 address, .i64 lo, .i64 hi]).map
      (fun c => runInitialized cfg.wasm 7 (.next c)) =
      some (.done [] (StorePairEntry.finalStore s cfg.wasm.regularOpCost index address.toNat memory lo hi), none) := by
  have hinfo := functions cfg host s mi hload 518
    WNear.Binary.StorePair.function WNear.Binary.StorePair.signature
    WNear.Binary.StorePair.module_function WNear.Binary.StorePair.module_signature
  have ha : mi.funcAddrs[566]! = 566 := by
    simp [getElem!_def, hinfo.1]
  rw [ha]
  exact StorePairEntry.invoke cfg.wasm rest s limits 566 0 address lo hi mi index memory
    hinfo.2.1 hinfo.2.2 hindex hmemory hwf hbound hgas

theorem packWords (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hload : Installed cfg host s mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (17 * cfg.wasm.regularOpCost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[779]! [.i32 out, .i32 source]).map
      (fun c => runInitialized cfg.wasm 9 (.next c)) =
      some (.done [] (PackWordsEntry.finalStore s cfg.wasm.regularOpCost index out.toNat source.toNat memory), none) := by
  have hinfo := functions cfg host s mi hload 731
    WNear.Binary.PackWords.function WNear.Binary.PackWords.signature
    WNear.Binary.PackWords.module_function WNear.Binary.PackWords.module_signature
  have ha : mi.funcAddrs[779]! = 779 := by
    simp [getElem!_def, hinfo.1]
  rw [ha]
  exact PackWordsEntry.invoke cfg.wasm rest s limits 779 0 out source mi index memory
    hinfo.2.1 hinfo.2.2 hindex hmemory hwf hread hwrite hgas

theorem expectResult (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (sp out source location : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hload : Installed cfg host s mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (36 * cfg.wasm.regularOpCost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[158]! [.i32 out, .i32 source, .i32 location]).map
      (fun c => runInitialized cfg.wasm 28 (.next c)) =
      some (.done [] (ExpectResultEntry.finalStore s cfg.wasm.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  have hinfo := functions cfg host s mi hload 110
    WNear.Binary.ExpectResult.function WNear.Binary.ExpectResult.signature
    WNear.Binary.ExpectResult.module_function WNear.Binary.ExpectResult.module_signature
  have ha : mi.funcAddrs[158]! = 158 := by
    simp [getElem!_def, hinfo.1]
  rw [ha]
  exact ExpectResultEntry.invoke cfg.wasm rest s limits 158 0 sp out source location mi globalIndex memoryIndex global memory
    hinfo.2.1 hinfo.2.2 hglobalIndex hglobal hsp hmemoryIndex hmemory hwf hwidth houtBound hsourceBound htag hc

theorem storePairCaller (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (out source : UInt32) (mi : ModuleInst)
    (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory) (sp : UInt32)
    (hload : Installed cfg host s mi) (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hspValue : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (houtBound : out.toNat + 16 ≤ memory.byteSize) (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) (hgas : s.host.gas.Credits (57 * cfg.wasm.regularOpCost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[414]! [.i32 out, .i32 source]).map
      (fun c => runInitialized cfg.wasm 37 (.next c)) =
      some (.done [] (StorePairCallerEntry.finalStore s cfg.wasm.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  have hinfo := functions cfg host s mi hload 366
    WNear.Binary.StorePairCaller.function WNear.Binary.StorePairCaller.signature
    WNear.Binary.StorePairCaller.module_function WNear.Binary.StorePairCaller.module_signature
  have ha : mi.funcAddrs[414]! = 414 := by
    simp [getElem!_def, hinfo.1]
  rw [ha]
  have hhelper := functions cfg host s mi hload 518
    WNear.Binary.StorePair.function WNear.Binary.StorePair.signature
    WNear.Binary.StorePair.module_function WNear.Binary.StorePair.module_signature
  exact StorePairCallerEntry.invoke cfg.wasm rest s limits 414 0 out source mi globalIndex memoryIndex 566 global memory sp
    hinfo.2.1 hinfo.2.2 hglobalIndex hglobal hspValue hhelper.1 hhelper.2.1 hmemoryIndex hmemory hwf hwidth hsp hstack houtBound hsourceBound hdepth hgas

open TotalSupply

theorem totalSupply (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hload : Installed cfg host s mi)
    (hcalls : CallObligations cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0)
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[296]! []).map
      (fun c => runInitialized cfg.wasm (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  have hinfo := functions cfg host s mi hload 248
    WNear.Binary.TotalSupply.function WNear.Binary.TotalSupply.signature
    WNear.Binary.TotalSupply.module_function WNear.Binary.TotalSupply.module_signature
  have ha : mi.funcAddrs[296]! = 296 := by
    simp [getElem!_def, hinfo.1]
  rw [ha]
  exact TotalSupplyEntry.invoke cfg.wasm rest s final limits 296 0 before after cost steps mi
    globalIndex memoryIndex sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory
    hinfo.2.1 hcalls hboundaries hinv hgas

end WNear.Proofs.LoadedCallees
