import Proofs.StateReadStorage
import NearVM.MeteredStorageReadFrames
import NearVM.MeteredWasmCall

/-! Actual typed f284 storage-read-hit forwarding call. -/
namespace WNear.Proofs.StateReadStorage
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (12 * op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :=
  after cfg (entered s cfg.regularOpCost) mi initial keyLen keyPtr register key value

theorem ready_entered (s : Store NearState) (op : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value) :
    StorageReadCalls.Ready ⟨memory,(entered s op).host⟩ ctx raw storage keyLen keyPtr register key value :=
  (hr.charge _ op ctx raw storage keyLen keyPtr register key value).charge _ (12 * op) ctx raw storage keyLen keyPtr register key value

theorem cost_entered (s : Store NearState) (op : Nat) (memory : Memory) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    StorageReadCalls.cost ⟨memory,(entered s op).host⟩ initial keyLen keyPtr register key value =
      StorageReadCalls.cost ⟨memory,s.host⟩ initial keyLen keyPtr register key value :=
  (StorageReadCalls.cost_charge ⟨memory,(chargedStore s op).host⟩ (12 * op) initial keyLen keyPtr register key value).trans
    (StorageReadCalls.cost_charge ⟨memory,s.host⟩ op initial keyLen keyPtr register key value)

 theorem after_credits (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest)) :
    (after cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.Credits rest := by
  have cp := paid_credits s cfg.regularOpCost 3 (cfg.regularOpCost + (StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest)) (hc.mono (by omega))
  have hp : (paid s cfg.regularOpCost 3).mems[index]? = some memory := hm
  have ch : (paid s cfg.regularOpCost 3).host.gas.Credits (cfg.regularOpCost + (StorageReadCalls.cost ⟨memory,(paid s cfg.regularOpCost 3).host⟩ ctx.trie keyLen keyPtr register key value + rest)) := by
    rw [cost_paid]; exact cp
  exact StorageReadCalls.callStore_credits cfg (paid s cfg.regularOpCost 3) mi index memory ctx raw storage keyLen keyPtr register key value rest hi hp
    (ready_paid s cfg.regularOpCost 3 memory ctx raw storage keyLen keyPtr register key value hr) ch

/-- Typed local f284, including its actual twelve-unit activation. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (hostAddress leafAddress index : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (receiver : UInt32) (keyLen keyPtr register : UInt64) (key value : List UInt8) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[43]? = some hostAddress)
    (hf : s.funcs[hostAddress]? = some (.host (metered extra "storage_read" storageReadFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hli : mi.funcAddrs[284]? = some leafAddress)
    (hlf : s.funcs[leafAddress]? = some (.wasm WNear.Binary.StateRead.storageForwardSignature frame.inst WNear.Binary.StateRead.storageForwardFunction))
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s mi ctx.trie keyLen keyPtr register key value)
      limits (base ++ [Value.i64 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits (base ++ [Value.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register]).toArray frame callers (.call 284 :: code)))
      (17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest) post := by
  let op := cfg.regularOpCost
  let fee := StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value
  let active := entered s op
  let leaf : CallFrame := {
    locals := #[.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register],inst := frame.inst,arity := 1,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have c0 := (GasCounter.burn_credits s.host.gas op (12 * op + (4 * op + fee + rest)) (hc.mono (by dsimp [op,fee]; omega))).2.2.2
  have c1 : active.host.gas.Credits (4 * op + fee + rest) :=
    (GasCounter.burn_credits (chargedStore s op).host.gas (12 * op) _ c0).2.2.2
  have ractive := ready_entered s op memory ctx raw storage keyLen keyPtr register key value hr
  have cbody : active.host.gas.Credits (4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,active.host⟩ ctx.trie keyLen keyPtr register key value + rest) := by
    rw [show StorageReadCalls.cost ⟨memory,active.host⟩ ctx.trie keyLen keyPtr register key value = fee from cost_entered s op memory ctx.trie keyLen keyPtr register key value]
    exact c1
  have cf := after_credits cfg active mi index memory ctx raw storage keyLen keyPtr register key value rest hmi hmem ractive cbody
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s mi ctx.trie keyLen keyPtr register key value) limits
      (base ++ [Value.i64 1]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s mi ctx.trie keyLen keyPtr register key value) limits base [.i64 1] leaf saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel + 1) (.next (atCode (after cfg active mi ctx.trie keyLen keyPtr register key value) limits
      (base ++ [Value.i64 1]).toArray leaf (saved :: callers) [])) rest post := left
  have body := wp_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] mi hostAddress index memory ctx raw storage keyLen keyPtr register key value post
    rfl rfl rfl hm hi hf hmi hmem ractive cbody bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 4) (4 * op + fee + rest) s limits base [.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register]
    frame callers code 284 leafAddress mi WNear.Binary.StateRead.storageForwardSignature frame.inst WNear.Binary.StateRead.storageForwardFunction post hm hli hlf rfl hd
  have ac : activationGas op (wasmLocals WNear.Binary.StateRead.storageForwardFunction [.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register]) = 12 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateRead.storageForwardFunction]
  rw [ac] at cr
  have next : WP cfg ((fuel + 1) + 4) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateRead.storageForwardSignature frame.inst
      WNear.Binary.StateRead.storageForwardFunction [.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register])) (4 * op + fee + rest) post := by
    have ce : StorageReadCalls.cost ⟨memory,active.host⟩ ctx.trie keyLen keyPtr register key value = fee := cost_entered s op memory ctx.trie keyLen keyPtr register key value
    simpa only [ce,op,Nat.zero_add,wasmCallee,wasmLocals,WNear.Binary.StateRead.storageForwardFunction,
      WNear.Binary.StateRead.storageForwardSignature,leaf,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,Array.append_empty] using body
  have result := cr (hc.mono (by dsimp [op,fee]; omega)) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,fee,
    show cfg.regularOpCost + (12 * op + (4 * op + (StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest))) =
      17 * cfg.regularOpCost + (StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest) by dsimp [op]; omega] using result

end WNear.Proofs.StateReadStorage
