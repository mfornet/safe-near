import Binary.StateRead
import Proofs.StorePairCallerState
import NearVM.MeteredStorageReadRules

/-! Actual SDK storage_read vtable forwarder f284, on a canonical hit. -/
namespace WNear.Proofs.StateReadStorage
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def after (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :=
  StorageReadCalls.callStore cfg (paid s cfg.regularOpCost 3) mi initial keyLen keyPtr register key value

theorem ready_paid (s : Store NearState) (op n : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value) :
    StorageReadCalls.Ready ⟨memory,(paid s op n).host⟩ ctx raw storage keyLen keyPtr register key value := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih.charge _ op ctx raw storage keyLen keyPtr register key value

theorem cost_paid (s : Store NearState) (op n : Nat) (memory : Memory) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    StorageReadCalls.cost ⟨memory,(paid s op n).host⟩ initial keyLen keyPtr register key value =
      StorageReadCalls.cost ⟨memory,s.host⟩ initial keyLen keyPtr register key value := by
  induction n with
  | zero => rfl
  | succ n ih => exact (StorageReadCalls.cost_charge ⟨memory,(paid s op n).host⟩ op initial keyLen keyPtr register key value).trans ih

/-- Four actual guest instructions; all trie/read/register execution is derived
from the original canonical host resources. -/
theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (address index : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (post : Post)
    (h1 : frame.locals[1]? = some (.i64 keyLen)) (h2 : frame.locals[2]? = some (.i64 keyPtr)) (h3 : frame.locals[3]? = some (.i64 register))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[43]? = some address)
    (hf : s.funcs[address]? = some (.host (metered extra "storage_read" storageReadFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s mi ctx.trie keyLen keyPtr register key value)
      limits (base ++ [Value.i64 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateRead.storageForwardBody ++ code)))
      (4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest) post := by
  let op := cfg.regularOpCost
  let fee := StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value
  have hm3 : (paid s op 3).modules[frame.inst]? = some mi := hm
  have hf3 : (paid s op 3).funcs[address]? = some (.host (metered extra "storage_read" storageReadFn).toHostFn) := hf
  have hmem3 : (paid s op 3).mems[index]? = some memory := hmem
  have hfee := cost_paid s op 3 memory ctx.trie keyLen keyPtr register key value
  have cp : (paid s op 3).host.gas.Credits (op + (fee + rest)) := paid_credits s op 3 _ (hc.mono (by dsimp [op,fee]; omega))
  have chost : (paid s op 3).host.gas.Credits (cfg.regularOpCost +
      (StorageReadCalls.cost ⟨memory,(paid s op 3).host⟩ ctx.trie keyLen keyPtr register key value + rest)) := by
    rw [hfee]; exact cp
  have tail := StorageReadCalls.wp_call cfg extra fuel rest (paid s op 3) limits base frame callers code 43 address index mi memory
    ctx raw storage keyLen keyPtr register key value post hm3 hi hf3 hmi hmem3 (ready_paid s op 3 memory ctx raw storage keyLen keyPtr register key value hr) chost hnext
  have stackEq : (base ++ StorageRead.args keyLen keyPtr register).toArray =
      ((base.toArray.push (.i64 keyLen)).push (.i64 keyPtr)).push (.i64 register) := by
    apply Array.toList_inj.mp; simp [StorageRead.args]
  have tail' : WP cfg (fuel + 1) (.next (atCode (paid s op 3) limits
      (((base.toArray.push (.i64 keyLen)).push (.i64 keyPtr)).push (.i64 register)) frame callers (.call 43 :: code))) (op + (fee + rest)) post := by
    simpa only [stackEq,hfee,op,fee] using tail
  have g3 := wp_local_get cfg (fuel + 1) (op + (fee + rest)) (paid s op 2) limits ((base.toArray.push (.i64 keyLen)).push (.i64 keyPtr))
    frame callers (.call 43 :: code) 3 (.i64 register) post h3 (paid_credits s op 2 _ (hc.mono (by dsimp [op,fee]; omega))) tail'
  have g2 := wp_local_get cfg (fuel + 2) (op + (op + (fee + rest))) (paid s op 1) limits (base.toArray.push (.i64 keyLen))
    frame callers (.local_get 3 :: .call 43 :: code) 2 (.i64 keyPtr) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp [op,fee]; omega))) g3
  have result := wp_local_get cfg (fuel + 3) (op + (op + (op + (fee + rest)))) s limits base.toArray frame callers
    (.local_get 2 :: .local_get 3 :: .call 43 :: code) 1 (.i64 keyLen) post h1 (hc.mono (by dsimp [op,fee]; omega)) g2
  simpa only [WNear.Binary.StateRead.storageForwardBody,List.cons_append,List.nil_append,Nat.add_assoc,fee,
    show cfg.regularOpCost + (op + (op + (op + (StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest)))) =
      4 * cfg.regularOpCost + (StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest) by dsimp [op]; omega] using result
end WNear.Proofs.StateReadStorage
