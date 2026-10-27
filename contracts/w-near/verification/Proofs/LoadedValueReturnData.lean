import Proofs.LoadedCallees
import Binary.ValueReturnLookupLayout
import NearVM.MeteredI32MemoryRules
import Wasm.LinkDataLookup

/-! Static vtable words in the actual initialized deployed memory. Source
bytes remain symbolic through the linker proof; later guest writes need their
own explicit byte-preservation facts. -/
namespace WNear.Proofs.LoadedValueReturnData
open Wasm Wasm.Near MeteredLogic

private noncomputable def segment : Data :=
  {init := WNear.Binary.dataInit, mode := .active 0 [.i32_const 1048576]}

private theorem data_singleton : WNear.Binary.wNearModule.datas = #[segment] := rfl

private theorem data_size : WNear.Binary.dataInit.size = 26319 := by
  simp only [WNear.Binary.dataInit, ByteArray.size, Array.size_ofFn]

private theorem byte_get (bytes : ByteArray) (i : Nat) (h : i < bytes.size) :
    bytes[i]! = bytes.data[i]! := by
  rw [getElem!_pos bytes i h, getElem!_pos bytes.data i h]
  cases bytes
  rfl

/-- Actual initialized memory, with exact byte provenance throughout the one
active deployed data segment. No initialized-memory lookup is assumed. -/
theorem loaded_bytes (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (hload : LoadedCallees.Loaded cfg original s inst) :
    ∃ index memory, inst.memAddrs[0]? = some index ∧ s.mems[index]? = some memory ∧
      memory.wf ∧ ∀ i < 26319,
        memory.read8 (1048576 + i) = WNear.Binary.dataInit.data[i]! := by
  rcases hload with ⟨vm, hv, hl⟩
  have hm := WNear.Binary.ImportLayout.validated_module cfg (Features.nearcore true) vm hv
  have hd : vm.module.datas = #[segment] := by rw [hm]; exact data_singleton
  have hstart : Link.MemoriesWF
      ((WNear.Binary.ImportLayout.hosts cfg).allocate (Store.empty original)).1 := by
    intro memory hmem
    have hs := congrArg (fun t : Store NearState => t.mems)
      (HostEnv.allocate_layout (Store.empty original) (WNear.Binary.ImportLayout.hosts cfg)).1
    rw [hs] at hmem
    change memory ∈ (#[] : Array Memory) at hmem
    simp at hmem
  have hread := Link.instantiateModule_single_active_data_read _ vm _ s inst hl segment hd
    1048576 rfl hstart
  rcases hread with ⟨index, memory, hi, hm, hwf, hr⟩
  refine ⟨index, memory, hi, hm, hwf, fun i hb => ?_⟩
  have hb' : i < segment.init.size := by change i < WNear.Binary.dataInit.size; rw [data_size]; exact hb
  have hval := hr i hb'
  have hoff : (1048576 : UInt32).toNat = 1048576 := rfl
  have hp : segment.init = WNear.Binary.dataInit := rfl
  rw [hoff, hp] at hval
  have hbdata : i < WNear.Binary.dataInit.size := by rw [data_size]; exact hb
  rw [byte_get WNear.Binary.dataInit i hbdata] at hval
  exact hval

private def decode32 (bytes : List UInt8) : UInt32 :=
  UInt32.ofNat (bytes.foldr (fun b acc => acc * 256 + b.toNat) 0)

private theorem readI32_decode (memory : Memory) (address : Nat) :
    readI32 memory address = decode32 ((List.range 4).map (fun i => memory.read8 (address + i))) := by
  rfl

/-- The actual deployed data segment installs the two four-byte words used by
return dispatch and its interface lookup. -/
theorem loaded_words (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (hload : LoadedCallees.Loaded cfg original s inst) :
    ∃ index memory, inst.memAddrs[0]? = some index ∧ s.mems[index]? = some memory ∧
      memory.wf ∧ readI32 memory 1050280 = 58 ∧ readI32 memory 1055020 = 116 := by
  rcases loaded_bytes cfg original s inst hload with ⟨index, memory, hi, hm, hwf, hr⟩
  have h58 : (List.range 4).map (fun i => memory.read8 (1050280 + i)) = [58, 0, 0, 0] := by
    rw [← WNear.Binary.ValueReturnLayout.data_word]
    apply List.map_congr_left
    intro i hb
    have hlt := List.mem_range.mp hb
    have hread := hr (1704 + i) (by omega)
    simpa only [← Nat.add_assoc] using hread
  have h116 : (List.range 4).map (fun i => memory.read8 (1055020 + i)) = [116, 0, 0, 0] := by
    rw [← WNear.Binary.ValueReturnLookupLayout.data_word]
    apply List.map_congr_left
    intro i hb
    have hlt := List.mem_range.mp hb
    have hread := hr (6444 + i) (by omega)
    simpa only [← Nat.add_assoc] using hread
  refine ⟨index, memory, hi, hm, hwf, ?_, ?_⟩
  · rw [readI32_decode, h58]; rfl
  · rw [readI32_decode, h116]; rfl

/-- Later writes may change the memory elsewhere. Retaining just these four
bytes retains the actual i32 value at a selected vtable slot. -/
theorem readI32_frame (before after : Memory) (address : Nat)
    (hbytes : ∀ i < 4, after.read8 (address + i) = before.read8 (address + i)) :
    readI32 after address = readI32 before address := by
  rw [readI32_decode, readI32_decode]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hbytes i (List.mem_range.mp hi)

end WNear.Proofs.LoadedValueReturnData
