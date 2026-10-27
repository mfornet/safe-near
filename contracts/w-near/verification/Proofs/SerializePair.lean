import Binary.SerializeHelpers
import Proofs.InterfaceSetBody
import NearVM.MeteredWasmCall

/-! Actual f472 formatter-pair construction, with sequential byte writes. -/
namespace WNear.Proofs.SerializePair
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP

def pairMemory (memory : Memory) (out : UInt32) (pointer element : UInt32) :=
  writeI32 (writeI32 memory (out.toNat + 4) element) out.toNat pointer
def after (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer element : UInt32) :=
  InterfaceSetBody.twoWordsStore s op index 4 0 out element pointer memory

theorem after_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out pointer element : UInt32)
    (hc : s.host.gas.Credits (6 * op + rest)) : (after s op index memory out pointer element).host.gas.Credits rest :=
  InterfaceSetBody.twoWordsStore_credits s op index 4 0 rest out element pointer memory hc

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out pointer element : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hp : frame.locals[1]? = some (.i32 pointer)) (he : frame.locals[2]? = some (.i32 element))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hwf : memory.wf) (hb : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory out pointer element) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers (WNear.Binary.SerializeHelpers.pairBody ++ code))) (6 * cfg.regularOpCost + rest) post := by
  have hs := writeI32_spec memory (out.toNat + 4) element hwf (by omega)
  have hb2 : out.toNat + 0 + 4 ≤ (writeI32 memory (out.toNat + 4) element).byteSize := by rw [hs.2.1]; omega
  exact InterfaceSetBody.wp_two_words cfg fuel rest s limits stack frame callers code 0 2 1 4 0 out element pointer mi index memory post ho he hp hm hi hmem (by omega) hb2 hc hnext

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def callAfter (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer element : UInt32) :=
  after (entered s op) op index memory out pointer element

theorem callAfter_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out pointer element : UInt32)
    (hc : s.host.gas.Credits (17 * op + rest)) : (callAfter s op index memory out pointer element).host.gas.Credits rest := by
  have co := StorePair.charged_credits s op (10 * op + (6 * op + rest)) (hc.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore s op) (10 * op) (6 * op + rest) co
  exact after_credits (entered s op) op index rest memory out pointer element ca

/-- Actual typed f472 activation and normal return, preserving arbitrary caller
operands and frames. The formatter table index is an ordinary stored word. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out pointer element : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[472]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.SerializeHelpers.pairSignature frame.inst WNear.Binary.SerializeHelpers.pairFunction))
    (hwf : memory.wf) (hb : out.toNat + 8 ≤ memory.byteSize) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index memory out pointer element) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits (base ++ [Value.i32 out, .i32 pointer, .i32 element]).toArray frame callers (.call 472 :: code)))
      (17 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[Value.i32 out, .i32 pointer, .i32 element], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have co := StorePair.charged_credits s op (10 * op + (6 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca := StorePair.charged_credits (chargedStore s op) (10 * op) (6 * op + rest) co
  have cf := callAfter_credits s op index rest memory out pointer element hc
  have leave := wp_leave_wasm cfg fuel rest (callAfter s op index memory out pointer element) limits base [] leaf saved callers post rfl rfl rfl cf
  have resume : WP cfg fuel (.next (atCode (callAfter s op index memory out pointer element) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, List.append_nil] using hnext
  have left := leave resume
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered, chargedStore, leaf] using hm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after active op index memory out pointer element) limits base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [callAfter, active, List.append_nil] using left
  have body := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] out pointer element mi index memory post rfl rfl rfl hm' hi hmem' hwf hb ca bodyNext
  have rule := wp_call_wasm cfg ((fuel + 1) + 6) (6 * op + rest) s limits base [.i32 out, .i32 pointer, .i32 element] frame callers code 472 address mi
    WNear.Binary.SerializeHelpers.pairSignature frame.inst WNear.Binary.SerializeHelpers.pairFunction post hm hfi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.SerializeHelpers.pairFunction [.i32 out, .i32 pointer, .i32 element]) = 10 * op := by simp [activationGas, wasmLocals, WNear.Binary.SerializeHelpers.pairFunction]
  rw [ha] at rule
  have next : WP cfg ((fuel + 1) + 6) (.next (wasmCallee active limits base frame callers code WNear.Binary.SerializeHelpers.pairSignature frame.inst WNear.Binary.SerializeHelpers.pairFunction [.i32 out, .i32 pointer, .i32 element])) (6 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.SerializeHelpers.pairFunction, WNear.Binary.SerializeHelpers.pairSignature, leaf, saved, atCode,
      List.map_nil, Array.append_empty, List.append_nil, List.length_nil] using body
  have result := rule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd, show cfg.regularOpCost + (10 * op + (6 * op + rest)) = 17 * cfg.regularOpCost + rest by dsimp [op]; omega] using result


theorem after_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer element : UInt32)
    (hm : s.mems[index]? = some memory) :
    (after s op index memory out pointer element).mems[index]? = some (pairMemory memory out pointer element) := by
  let first := InterfaceSetBody.storeWord s op index 4 out element memory
  have h1 : first.mems[index]? = some (writeI32 memory (out.toNat + 4) element) :=
    storeI32_memory (paid s op 3) index (out.toNat + 4) memory element hm
  have h1' : (paid first op 3).mems[index]? = some (writeI32 memory (out.toNat + 4) element) := by
    simpa only [paid, chargedStore] using h1
  have h2 := storeI32_memory (paid first op 3) index out.toNat (writeI32 memory (out.toNat + 4) element) pointer h1'
  simpa only [after, pairMemory, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord, first, Nat.add_zero] using h2

theorem after_resources (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer element : UInt32) :
    {after s op index memory out pointer element with host := s.host, mems := s.mems} = s := by
  simp only [after, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord, storeI32, paid, chargedStore]

theorem callAfter_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer element : UInt32)
    (hm : s.mems[index]? = some memory) :
    (callAfter s op index memory out pointer element).mems[index]? = some (pairMemory memory out pointer element) :=
  after_memory (entered s op) op index memory out pointer element hm
end WNear.Proofs.SerializePair
