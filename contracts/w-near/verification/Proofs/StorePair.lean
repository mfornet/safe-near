import NearVM.MeteredMemoryRules
import Binary.StorePair

/-! Metered semantics of the deployed two-word store leaf, from an active frame.
Entry activation is paid by the caller. -/
namespace WNear.Proofs.StorePair
open Wasm Wasm.Near Wasm.Near.MeteredLogic

def charge3 (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore (chargedStore s op) op) op

def storeWord (s : Store NearState) (op index address : Nat) (memory : Memory)
    (value : UInt64) : Store NearState := storeI64 (charge3 s op) index address memory value

theorem charged_credits (s : Store NearState) (op rest : Nat)
    (h : s.host.gas.Credits (op + rest)) :
    (chargedStore s op).host.gas.Credits rest :=
  (GasCounter.burn_credits s.host.gas op rest h).2.2.2

theorem wp_storeWord (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (slot : Nat) (arg : MemArg)
    (address : UInt32) (value : UInt64) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (haddress : frame.locals[0]? = some (.i32 address))
    (hvalue : frame.locals[slot]? = some (.i64 value))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeWord s cfg.regularOpCost index (address.toNat + arg.offset) memory value)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      (.local_get 0 :: .local_get slot :: .store .i64 none arg :: code)))
      (3 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (cfg.regularOpCost +
      (cfg.regularOpCost + rest))) := by convert hgas using 1; omega
  have h1 := charged_credits s _ _ h0
  have h2 := charged_credits (chargedStore s cfg.regularOpCost) _ _ h1
  convert wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 address)
    post haddress h0 ?_ using 1 <;> try omega
  apply wp_local_get cfg (fuel + 1) _ _ limits _ frame callers _ slot (.i64 value)
    post hvalue h1
  apply wp_i64_store cfg fuel rest _ limits stack frame callers code arg address value
    mi index memory post
  · exact hmodule
  · exact hindex
  · exact hmemory
  · exact hbound
  · exact h2
  · exact hnext

/-- The body identified in the actual decoded module by
`WNear.Binary.StorePair.module_function`. -/
abbrev body : List Instr := WNear.Binary.StorePair.body

def pairMemory (memory : Memory) (address : Nat) (lo hi : UInt64) : Memory :=
  writeI64 (writeI64 memory (address + 8) hi) address lo

def pairStore (s : Store NearState) (op index address : Nat) (memory : Memory)
    (lo hi : UInt64) : Store NearState :=
  storeWord (storeWord s op index (address + 8) memory hi) op index address
    (writeI64 memory (address + 8) hi) lo

theorem storeWord_credits (s : Store NearState) (op index address rest : Nat)
    (memory : Memory) (value : UInt64)
    (hgas : s.host.gas.Credits (3 * op + rest)) :
    (storeWord s op index address memory value).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (op + (op + (op + rest))) := by
    convert hgas using 1; omega
  exact charged_credits _ _ _ (charged_credits _ _ _ (charged_credits _ _ _ h0))

/-- The actual six-instruction shape, retaining arbitrary labels, caller frames,
operand prefix and following code. The only semantic continuation is after all
six actual instructions have completed. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (address : UInt32) (lo hi : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (haddress : frame.locals[0]? = some (.i32 address))
    (hlo : frame.locals[1]? = some (.i64 lo)) (hhi : frame.locals[2]? = some (.i64 hi))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hbound : address.toNat + 16 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (pairStore s cfg.regularOpCost index address.toNat memory lo hi)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers (body ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  have hfirst : address.toNat + 8 + 8 ≤ memory.byteSize := by omega
  have hspec := writeI64_spec memory (address.toNat + 8) hi hwf hfirst
  have hg0 : s.host.gas.Credits (3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest)) := by
    convert hgas using 1; omega
  have hg1 := storeWord_credits s cfg.regularOpCost index (address.toNat + 8)
    (3 * cfg.regularOpCost + rest) memory hi hg0
  have hm1 : (storeWord s cfg.regularOpCost index (address.toNat + 8) memory hi).mems[index]? =
      some (writeI64 memory (address.toNat + 8) hi) := by
    apply storeI64_memory
    exact hmemory
  have hb1 : address.toNat + 0 + 8 ≤ (writeI64 memory (address.toNat + 8) hi).byteSize := by
    rw [hspec.2.1]; omega
  have hn := wp_storeWord cfg fuel rest
    (storeWord s cfg.regularOpCost index (address.toNat + 8) memory hi)
    limits stack frame callers code 1 {align := 3, offset := 0} address lo mi index
    (writeI64 memory (address.toNat + 8) hi) post haddress hlo hmodule hindex hm1 hb1 hg1 hnext
  have hall := wp_storeWord cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame
    callers (.local_get 0 :: .local_get 1 :: .store .i64 none {align := 3, offset := 0} :: code)
    2 {align := 3, offset := 8} address hi mi index memory post haddress hhi
    hmodule hindex hmemory hfirst hg0 hn
  convert hall using 1 <;> first | omega | simp only [body, WNear.Binary.StorePair.body, List.cons_append, List.nil_append]

def voidFrame (locals : Array Value) (inst : Nat) : CallFrame :=
  { locals, inst, arity := 0, height := 0, labels := [], code := [] }

theorem wp_finish_void (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (post : Post)
    (hgas : s.host.gas.Credits rest) (hpost : post rest (.done [] s) none) :
    WP cfg (fuel + 1) (.next (atCode s limits #[] (voidFrame locals inst) [] [])) rest post := by
  let c := atCode s limits #[] (voidFrame locals inst) [] []
  have hz := chargeWasm_zero (.next c) (hgas.mono (Nat.zero_le rest))
  have hc : chargeConfig c 0 = (c, none) := by
    cases he : chargeConfig c 0 with
    | mk c' error =>
      simp only [chargeWasm, he] at hz
      cases hz
      rfl
  have hstep : Exec.step c = .done [] s := rfl
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  have hcost : nextInstructionGas cfg c = 0 := rfl
  rw [hcost, hc, hstep] at h
  simp only [Nat.zero_add] at h
  apply h hgas
  · rfl
  · rfl
  · exact wp_done cfg fuel [] s rest post hgas hpost

/-- Complete active body: six charged instructions and one free frame leave.
The caller must account separately for entering this frame. -/
theorem wp_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (address : UInt32) (lo hi : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hbound : address.toNat + 16 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (6 * cfg.regularOpCost + rest)) :
    WP cfg 7 (.next (atCode s limits #[]
      (voidFrame #[.i32 address, .i64 lo, .i64 hi] inst) [] body))
      (6 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (pairStore s cfg.regularOpCost index address.toNat memory lo hi) ∧
        error = none) := by
  have hg0 : s.host.gas.Credits (3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest)) := by
    convert hgas using 1; omega
  have hg1 := storeWord_credits s cfg.regularOpCost index (address.toNat + 8)
    (3 * cfg.regularOpCost + rest) memory hi hg0
  have hg2 := storeWord_credits
    (storeWord s cfg.regularOpCost index (address.toNat + 8) memory hi)
    cfg.regularOpCost index address.toNat rest (writeI64 memory (address.toNat + 8) hi) lo hg1
  let post : Post := fun remaining final error => remaining = rest ∧
    final = .done [] (pairStore s cfg.regularOpCost index address.toNat memory lo hi) ∧ error = none
  have hfinish := wp_finish_void cfg 0 rest
    (pairStore s cfg.regularOpCost index address.toNat memory lo hi) limits
    #[.i32 address, .i64 lo, .i64 hi] inst post hg2 ⟨rfl, rfl, rfl⟩
  exact wp_body cfg 1 rest s limits #[] (voidFrame #[.i32 address, .i64 lo, .i64 hi] inst)
    [] [] address lo hi mi index memory _ rfl rfl rfl hmodule hindex hmemory hwf hbound hgas hfinish

/-- Exact output bytes and frame, including the first write's disjointness from
the low word written second. -/
theorem pairMemory_spec (memory : Memory) (address : Nat) (lo hi : UInt64)
    (hwf : memory.wf) (hbound : address + 16 ≤ memory.byteSize) :
    (pairMemory memory address lo hi).wf ∧
    (pairMemory memory address lo hi).byteSize = memory.byteSize ∧
    (pairMemory memory address lo hi).max = memory.max ∧
    ∀ j, (pairMemory memory address lo hi).read8 j =
      if address ≤ j ∧ j < address + 8 then
        UInt8.ofNat (lo.toNat >>> (8 * (j - address)))
      else if address + 8 ≤ j ∧ j < address + 16 then
        UInt8.ofNat (hi.toNat >>> (8 * (j - (address + 8))))
      else memory.read8 j := by
  have hbhi : address + 8 + 8 ≤ memory.byteSize := by omega
  have hhi := writeI64_spec memory (address + 8) hi hwf hbhi
  have hblo : address + 8 ≤ (writeI64 memory (address + 8) hi).byteSize := by
    rw [hhi.2.1]; omega
  have hlo := writeI64_spec (writeI64 memory (address + 8) hi) address lo hhi.1 hblo
  refine ⟨hlo.1, hlo.2.1.trans hhi.2.1, hlo.2.2.1.trans hhi.2.2.1, ?_⟩
  intro j
  rw [show (pairMemory memory address lo hi).read8 j = _ from hlo.2.2.2 j]
  rw [hhi.2.2.2 j]

theorem pairStore_memory (s : Store NearState) (op index address : Nat)
    (memory : Memory) (lo hi : UInt64) (hmemory : s.mems[index]? = some memory) :
    (pairStore s op index address memory lo hi).mems[index]? =
      some (pairMemory memory address lo hi) := by
  have hm0 : (charge3 s op).mems[index]? = some memory := hmemory
  have hm1 := storeI64_memory (charge3 s op) index (address + 8) memory hi hm0
  have hm2 : (charge3 (storeWord s op index (address + 8) memory hi) op).mems[index]? =
      some (writeI64 memory (address + 8) hi) := hm1
  exact storeI64_memory (charge3 (storeWord s op index (address + 8) memory hi) op)
    index address (writeI64 memory (address + 8) hi) lo hm2

theorem pairStore_other_memory (s : Store NearState) (op index address other : Nat)
    (memory : Memory) (lo hi : UInt64) (hne : other ≠ index) :
    (pairStore s op index address memory lo hi).mems[other]? = s.mems[other]? := by
  simp only [pairStore, storeWord, storeI64_other_memory _ _ _ _ _ _ hne, charge3,
    chargedStore_mems]

theorem storeWord_gas (s : Store NearState) (op index address rest : Nat)
    (memory : Memory) (value : UInt64) (hgas : s.host.gas.Credits (3 * op + rest)) :
    (storeWord s op index address memory value).host.gas.burnt = s.host.gas.burnt + 3 * op ∧
    (storeWord s op index address memory value).host.gas.promises = s.host.gas.promises := by
  have h0 : s.host.gas.Credits (op + (op + (op + rest))) := by
    convert hgas using 1; omega
  have b0 := GasCounter.burn_credits s.host.gas op _ h0
  have b1 := GasCounter.burn_credits (chargedStore s op).host.gas op _ b0.2.2.2
  have b2 := GasCounter.burn_credits (chargedStore (chargedStore s op) op).host.gas op rest b1.2.2.2
  change ((chargedStore (chargedStore (chargedStore s op) op) op).host.gas.burnt = _ ∧
    (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.promises = _)
  have hb0 : (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op := b0.2.1
  have hb1 : (chargedStore (chargedStore s op) op).host.gas.burnt =
      (chargedStore s op).host.gas.burnt + op := b1.2.1
  have hb2 : (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.burnt =
      (chargedStore (chargedStore s op) op).host.gas.burnt + op := b2.2.1
  have hp0 : (chargedStore s op).host.gas.promises = s.host.gas.promises := b0.2.2.1
  have hp1 : (chargedStore (chargedStore s op) op).host.gas.promises =
      (chargedStore s op).host.gas.promises := b1.2.2.1
  have hp2 : (chargedStore (chargedStore (chargedStore s op) op) op).host.gas.promises =
      (chargedStore (chargedStore s op) op).host.gas.promises := b2.2.2.1
  constructor <;> omega

theorem pairStore_gas (s : Store NearState) (op index address rest : Nat)
    (memory : Memory) (lo hi : UInt64) (hgas : s.host.gas.Credits (6 * op + rest)) :
    (pairStore s op index address memory lo hi).host.gas.burnt = s.host.gas.burnt + 6 * op ∧
    (pairStore s op index address memory lo hi).host.gas.promises = s.host.gas.promises := by
  have hg0 : s.host.gas.Credits (3 * op + (3 * op + rest)) := by
    convert hgas using 1; omega
  have hg1 := storeWord_credits s op index (address + 8) (3 * op + rest) memory hi hg0
  have h0 := storeWord_gas s op index (address + 8) (3 * op + rest) memory hi hg0
  have h1 := storeWord_gas (storeWord s op index (address + 8) memory hi)
    op index address rest (writeI64 memory (address + 8) hi) lo hg1
  change _ = _ ∧ _ = _
  constructor <;> dsimp only [pairStore] <;> omega

theorem pairStore_frame (s : Store NearState) (op index address : Nat)
    (memory : Memory) (lo hi : UInt64) :
    (pairStore s op index address memory lo hi).modules = s.modules ∧
    (pairStore s op index address memory lo hi).funcs = s.funcs ∧
    (pairStore s op index address memory lo hi).globals = s.globals ∧
    (pairStore s op index address memory lo hi).tables = s.tables ∧
    { (pairStore s op index address memory lo hi).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [pairStore, storeWord, storeI64, charge3, chargedStore, chargeHost]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Interpreter adequacy, with an explicit successful result rather than a
continuation premise. -/
theorem run_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (address : UInt32) (lo hi : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hbound : address.toNat + 16 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (6 * cfg.regularOpCost + rest)) :
    runMetered cfg 7 (.next (atCode s limits #[]
      (voidFrame #[.i32 address, .i64 lo, .i64 hi] inst) [] body)) =
      (.done [] (pairStore s cfg.regularOpCost index address.toNat memory lo hi), none) := by
  obtain ⟨remaining, hpost, _⟩ :=
    (wp_return cfg rest s limits inst address lo hi mi index memory
      hmodule hindex hmemory hwf hbound hgas).result
  exact Prod.ext hpost.2.1 hpost.2.2

end WNear.Proofs.StorePair
