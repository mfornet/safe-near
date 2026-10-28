import Proofs.StateReadStorageOuterCredits
import Proofs.StateReadStorageOuterCode

/-! Actual548 typed activation definitions and credit transport. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] after fee

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.out548,.i32 p.keyPtr,.i32 p.keyLen,.i32 0,.i64 0],inst,arity:=0,height,labels:=[],code:=[]}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  after cfg (entered s cfg.regularOpCost) p ctx key

theorem fee_charge (cfg : WasmConfig) (s : Store NearState) (amount : Nat) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    fee cfg (chargedStore s amount) p ctx key=fee cfg s p ctx key := by
  have first : StateDispatchStorage.fee (chargedStore s amount) (storageLayout p) ctx key p.bytes=
      StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes :=
    StorageReadCalls.cost_charge ⟨StateDispatchStorage.lowMemory (storageLayout p),s.host⟩ amount ctx.trie _ _ _ key p.bytes
  unfold fee
  rw [first]
  simp only [StateReadRegisterOuter.fee,RegisterRead.readCost,chargedStore,chargeHost]


theorem entered_fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :
    fee cfg (entered s cfg.regularOpCost) p ctx key=fee cfg s p ctx key := by rw [entered,fee_charge,fee_charge]

theorem entered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (12*op+rest)) : (entered s op).host.gas.Credits rest := by
  have c0 := StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest c0

theorem callAfter_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg s p ctx key+rest)) :
    (callAfter cfg s p ctx key).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have ca := entered_credits s op (bodyCost p*op+fee cfg s p ctx key+rest)
    (hc.mono (by simp only [Nat.add_mul,op];omega))
  have ra : StorageReadCalls.Ready ⟨p.memory,(entered s op).host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes :=
    (hr.charge _ op ctx raw storage _ _ _ key p.bytes).charge _ (11*op) ctx raw storage _ _ _ key p.bytes
  unfold callAfter
  apply after_credits cfg (entered s op) p hn ctx raw storage key rest hi hm ra
  rw [entered_fee]
  exact ca
end WNear.Proofs.StateReadStorageOuter
