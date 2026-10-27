import Binary.PackWords
import NearVM.MeteredI32MemoryRules
import Proofs.StorePair

/-! Actual f779 packs two words with sequential loads. The source and output
may overlap: the second source word is read after the first destination store.
All contracts start inside an active frame; entry activation is separate. -/
namespace WNear.Proofs.PackWords
open Wasm Wasm.Near Wasm.Near.MeteredLogic

attribute [local irreducible] readI32 writeI32

abbrev body := WNear.Binary.PackWords.body

def charge4 (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore (chargedStore (chargedStore s op) op) op) op

def copyWord (s : Store NearState) (op index destination source : Nat)
    (memory : Memory) : Store NearState :=
  storeI32 (charge4 s op) index destination memory (readI32 memory source)

def firstMemory (memory : Memory) (out source : Nat) : Memory :=
  writeI32 memory (out + 4) (readI32 memory (source + 8))

def packedMemory (memory : Memory) (out source : Nat) : Memory :=
  writeI32 (firstMemory memory out source) out (readI32 (firstMemory memory out source) source)

def packedStore (s : Store NearState) (op index out source : Nat)
    (memory : Memory) : Store NearState :=
  copyWord (copyWord s op index (out + 4) (source + 8) memory) op index out source
    (firstMemory memory out source)

private theorem charged_credits (s : Store NearState) (op rest : Nat)
    (h : s.host.gas.Credits (op + rest)) :
    (chargedStore s op).host.gas.Credits rest :=
  (GasCounter.burn_credits s.host.gas op rest h).2.2.2

theorem copyWord_credits (s : Store NearState) (op index destination source rest : Nat)
    (memory : Memory) (hgas : s.host.gas.Credits (4 * op + rest)) :
    (copyWord s op index destination source memory).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (op + (op + (op + (op + rest)))) := by
    convert hgas using 1; omega
  exact charged_credits _ _ _ (charged_credits _ _ _
    (charged_credits _ _ _ (charged_credits _ _ _ h0)))

/-- Execute the actual local_get/local_get/load/store block. -/
theorem wp_copyWord (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (loadArg storeArg : MemArg)
    (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out))
    (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hread : source.toNat + loadArg.offset + 4 ≤ memory.byteSize)
    (hwrite : out.toNat + storeArg.offset + 4 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (copyWord s cfg.regularOpCost index (out.toNat + storeArg.offset)
        (source.toNat + loadArg.offset) memory) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (.local_get 0 :: .local_get 1 :: .load .i32 none loadArg :: .store .i32 none storeArg :: code)))
      (4 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (cfg.regularOpCost +
      (cfg.regularOpCost + (cfg.regularOpCost + rest)))) := by
    convert hgas using 1; omega
  have h1 := charged_credits s _ _ h0
  have h2 := charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
  have h3 := charged_credits (chargedStore (chargedStore s cfg.regularOpCost) cfg.regularOpCost) _ _ h2
  convert wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ 0 (.i32 out)
    post hout h0 ?_ using 1 <;> try omega
  apply wp_local_get cfg (fuel + 2) _ _ limits _ frame callers _ 1 (.i32 source) post hsource h1
  apply wp_i32_load cfg (fuel + 1) _
    (chargedStore (chargedStore s cfg.regularOpCost) cfg.regularOpCost) limits _ frame callers _ loadArg source mi index memory
    post hmodule hindex hmemory hread h2
  apply wp_i32_store cfg fuel rest
    (chargedStore (chargedStore (chargedStore s cfg.regularOpCost) cfg.regularOpCost) cfg.regularOpCost)
    limits stack frame callers code storeArg out
    (readI32 memory (source.toNat + loadArg.offset)) mi index memory post
    hmodule hindex hmemory hwrite h3
  exact hnext

/-- Eight actual instructions, without an alias restriction on the two pointers.
The continuation sees the exact sequentially updated memory and gas state. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out))
    (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : source.toNat + 12 ≤ memory.byteSize)
    (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (packedStore s cfg.regularOpCost index out.toNat source.toNat memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers (body ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
  have hr0 : source.toNat + 8 + 4 ≤ memory.byteSize := by omega
  have hw0 : out.toNat + 4 + 4 ≤ memory.byteSize := by omega
  have hspec := writeI32_spec memory (out.toNat + 4) (readI32 memory (source.toNat + 8)) hwf hw0
  have hg0 : s.host.gas.Credits (4 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) := by
    convert hgas using 1; omega
  have hg1 := copyWord_credits s cfg.regularOpCost index (out.toNat + 4)
    (source.toNat + 8) (4 * cfg.regularOpCost + rest) memory hg0
  have hm0 : (charge4 s cfg.regularOpCost).mems[index]? = some memory := by
    simp only [charge4, chargedStore_mems]
    exact hmemory
  have hm1 := storeI32_memory (charge4 s cfg.regularOpCost) index (out.toNat + 4)
    memory (readI32 memory (source.toNat + 8)) hm0
  have hr1 : source.toNat + 0 + 4 ≤ (firstMemory memory out.toNat source.toNat).byteSize := by
    rw [show (firstMemory memory out.toNat source.toNat).byteSize = memory.byteSize from hspec.2.1]
    omega
  have hw1 : out.toNat + 0 + 4 ≤ (firstMemory memory out.toNat source.toNat).byteSize := by
    rw [show (firstMemory memory out.toNat source.toNat).byteSize = memory.byteSize from hspec.2.1]
    omega
  have hmodule1 : (copyWord s cfg.regularOpCost index (out.toNat + 4) (source.toNat + 8) memory).modules[frame.inst]? = some mi := by
    simpa only [copyWord, storeI32_modules, charge4, chargedStore] using hmodule
  have hmemory1 : (copyWord s cfg.regularOpCost index (out.toNat + 4) (source.toNat + 8) memory).mems[index]? =
      some (firstMemory memory out.toNat source.toNat) := hm1
  have hn := wp_copyWord cfg fuel rest
    (copyWord s cfg.regularOpCost index (out.toNat + 4) (source.toNat + 8) memory)
    limits stack frame callers code {align := 2, offset := 0} {align := 2, offset := 0}
    out source mi index (firstMemory memory out.toNat source.toNat) post hout hsource
    hmodule1 hindex hmemory1 hr1 hw1 hg1 hnext
  have hall := wp_copyWord cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame
    callers (.local_get 0 :: .local_get 1 :: .load .i32 none {align := 2, offset := 0} ::
      .store .i32 none {align := 2, offset := 0} :: code)
    {align := 2, offset := 8} {align := 2, offset := 4}
    out source mi index memory post hout hsource hmodule hindex hmemory hr0 hw0 hg0
  have hall' := hall hn
  convert hall' using 1 <;> first | omega | simp only [body, WNear.Binary.PackWords.body,
    List.cons_append, List.nil_append]

theorem packedStore_credits (s : Store NearState) (op index out source rest : Nat)
    (memory : Memory) (hgas : s.host.gas.Credits (8 * op + rest)) :
    (packedStore s op index out source memory).host.gas.Credits rest := by
  have hg0 : s.host.gas.Credits (4 * op + (4 * op + rest)) := by
    convert hgas using 1; omega
  have hg1 := copyWord_credits s op index (out + 4) (source + 8) (4 * op + rest) memory hg0
  exact copyWord_credits (copyWord s op index (out + 4) (source + 8) memory)
    op index out source rest (firstMemory memory out source) hg1

theorem wp_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (8 * cfg.regularOpCost + rest)) :
    WP cfg 9 (.next (atCode s limits #[]
      (StorePair.voidFrame #[.i32 out, .i32 source] inst) [] body))
      (8 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (packedStore s cfg.regularOpCost index out.toNat source.toNat memory) ∧
        error = none) := by
  have hg := packedStore_credits s cfg.regularOpCost index out.toNat source.toNat rest memory hgas
  let post : Post := fun remaining final error => remaining = rest ∧
    final = .done [] (packedStore s cfg.regularOpCost index out.toNat source.toNat memory) ∧ error = none
  have hfinish := StorePair.wp_finish_void cfg 0 rest
    (packedStore s cfg.regularOpCost index out.toNat source.toNat memory) limits
    #[.i32 out, .i32 source] inst post hg ⟨rfl, rfl, rfl⟩
  exact wp_body cfg 1 rest s limits #[] (StorePair.voidFrame #[.i32 out, .i32 source] inst)
    [] [] out source mi index memory _ rfl rfl hmodule hindex hmemory hwf hread hwrite hgas hfinish

theorem run_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (8 * cfg.regularOpCost + rest)) :
    runMetered cfg 9 (.next (atCode s limits #[]
      (StorePair.voidFrame #[.i32 out, .i32 source] inst) [] body)) =
      (.done [] (packedStore s cfg.regularOpCost index out.toNat source.toNat memory), none) := by
  obtain ⟨_, hp, _⟩ := (wp_return cfg rest s limits inst out source mi index memory
    hmodule hindex hmemory hwf hread hwrite hgas).result
  exact Prod.ext hp.2.1 hp.2.2

/-- The low output word depends on the updated source. This is intentional even
when the first output store overlaps the second source load. -/
theorem packedMemory_spec (memory : Memory) (out source : Nat)
    (hwf : memory.wf) (hwrite : out + 8 ≤ memory.byteSize) :
    (packedMemory memory out source).wf ∧
    (packedMemory memory out source).byteSize = memory.byteSize ∧
    (packedMemory memory out source).max = memory.max ∧
    ∀ j, (packedMemory memory out source).read8 j =
      if out ≤ j ∧ j < out + 4 then
        UInt8.ofNat ((readI32 (firstMemory memory out source) source).toNat >>> (8 * (j - out)))
      else if out + 4 ≤ j ∧ j < out + 8 then
        UInt8.ofNat ((readI32 memory (source + 8)).toNat >>> (8 * (j - (out + 4))))
      else memory.read8 j := by
  have hb0 : out + 4 + 4 ≤ memory.byteSize := by omega
  have h0 := writeI32_spec memory (out + 4) (readI32 memory (source + 8)) hwf hb0
  have hb1 : out + 4 ≤ (firstMemory memory out source).byteSize := by
    rw [show (firstMemory memory out source).byteSize = memory.byteSize from h0.2.1]
    omega
  have h1 := writeI32_spec (firstMemory memory out source) out
    (readI32 (firstMemory memory out source) source) h0.1 hb1
  refine ⟨h1.1, h1.2.1.trans h0.2.1, h1.2.2.1.trans h0.2.2.1, ?_⟩
  intro j
  rw [show (packedMemory memory out source).read8 j = _ from h1.2.2.2 j]
  rw [show (firstMemory memory out source).read8 j = _ from h0.2.2.2 j]

theorem packedStore_memory (s : Store NearState) (op index out source : Nat)
    (memory : Memory) (hmemory : s.mems[index]? = some memory) :
    (packedStore s op index out source memory).mems[index]? = some (packedMemory memory out source) := by
  have hm0 : (charge4 s op).mems[index]? = some memory := by
    simpa only [charge4, chargedStore_mems] using hmemory
  have hm1 := storeI32_memory (charge4 s op) index (out + 4) memory (readI32 memory (source + 8)) hm0
  have hm2 : (charge4 (copyWord s op index (out + 4) (source + 8) memory) op).mems[index]? =
      some (firstMemory memory out source) := by
    simpa only [charge4, chargedStore_mems, copyWord, firstMemory] using hm1
  exact storeI32_memory (charge4 (copyWord s op index (out + 4) (source + 8) memory) op)
    index out (firstMemory memory out source) (readI32 (firstMemory memory out source) source) hm2

theorem packedStore_other_memory (s : Store NearState) (op index out source other : Nat)
    (memory : Memory) (hne : other ≠ index) :
    (packedStore s op index out source memory).mems[other]? = s.mems[other]? := by
  simp only [packedStore, copyWord, storeI32_other_memory _ _ _ _ _ _ hne, charge4, chargedStore_mems]

theorem packedStore_frame (s : Store NearState) (op index out source : Nat) (memory : Memory) :
    (packedStore s op index out source memory).modules = s.modules ∧
    (packedStore s op index out source memory).funcs = s.funcs ∧
    (packedStore s op index out source memory).globals = s.globals ∧
    (packedStore s op index out source memory).tables = s.tables ∧
    { (packedStore s op index out source memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [packedStore, copyWord, storeI32, charge4, chargedStore, chargeHost]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem copyWord_gas (s : Store NearState) (op index out source rest : Nat)
    (memory : Memory) (hgas : s.host.gas.Credits (4 * op + rest)) :
    (copyWord s op index out source memory).host.gas.burnt = s.host.gas.burnt + 4 * op ∧
    (copyWord s op index out source memory).host.gas.promises = s.host.gas.promises := by
  have hg : s.host.gas.Credits (op + (op + (op + (op + rest)))) := by
    convert hgas using 1; omega
  have b0 := GasCounter.burn_credits s.host.gas op (op + (op + (op + rest))) hg
  have hb0 : (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op := b0.2.1
  have hp0 : (chargedStore s op).host.gas.promises = s.host.gas.promises := b0.2.2.1
  have b1 := GasCounter.burn_credits (chargedStore s op).host.gas op (op + (op + rest)) b0.2.2.2
  have hb1 : (chargedStore (chargedStore s op) op).host.gas.burnt = (chargedStore s op).host.gas.burnt + op := b1.2.1
  have hp1 : (chargedStore (chargedStore s op) op).host.gas.promises = (chargedStore s op).host.gas.promises := b1.2.2.1
  have b2 := GasCounter.burn_credits (chargedStore (chargedStore s op) op).host.gas op (op + rest) b1.2.2.2
  have hb2 : (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.burnt = (chargedStore (chargedStore s op) op).host.gas.burnt + op := b2.2.1
  have hp2 : (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.promises = (chargedStore (chargedStore s op) op).host.gas.promises := b2.2.2.1
  have b3 := GasCounter.burn_credits (chargedStore (chargedStore (chargedStore s op) op) op).host.gas op rest b2.2.2.2
  have hb3 : (chargedStore (chargedStore (chargedStore (chargedStore s op) op) op) op).host.gas.burnt = (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.burnt + op := b3.2.1
  have hp3 : (chargedStore (chargedStore (chargedStore (chargedStore s op) op) op) op).host.gas.promises = (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.promises := b3.2.2.1
  change (charge4 s op).host.gas.burnt = _ ∧ (charge4 s op).host.gas.promises = _
  dsimp only [charge4]
  constructor <;> omega

theorem packedStore_gas (s : Store NearState) (op index out source rest : Nat)
    (memory : Memory) (hgas : s.host.gas.Credits (8 * op + rest)) :
    (packedStore s op index out source memory).host.gas.burnt = s.host.gas.burnt + 8 * op ∧
    (packedStore s op index out source memory).host.gas.promises = s.host.gas.promises := by
  have hg0 : s.host.gas.Credits (4 * op + (4 * op + rest)) := by
    convert hgas using 1; omega
  have hg1 := copyWord_credits s op index (out + 4) (source + 8) (4 * op + rest) memory hg0
  have h0 := copyWord_gas s op index (out + 4) (source + 8) (4 * op + rest) memory hg0
  have h1 := copyWord_gas (copyWord s op index (out + 4) (source + 8) memory)
    op index out source rest (firstMemory memory out source) hg1
  dsimp only [packedStore]
  constructor <;> omega

end WNear.Proofs.PackWords
