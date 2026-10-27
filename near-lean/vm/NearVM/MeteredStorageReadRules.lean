import NearVM.MeteredCall
import NearVM.MeteredHosts.StorageReadResult

/-! Canonical resources derive the actual installed metered storage-read call. -/
namespace Wasm.Near.MeteredLogic.StorageReadCalls
open MeteredHosts
open _root_.Near.TrieOverlay

/-- Pure pre-call resources; no host invocation or future store is assumed. -/
structure Ready (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8) : Prop where
  wf : ctx.WF raw
  raw_eq : storage.toFinset = raw
  represents : StorageOverlay.Represents before.host ctx storage
  nodes : ctx.trie.NonzeroNodes
  accounting : before.host.storageAccounting = some ctx.trie
  key_read : getMemOrReg before keyPtr keyLen = some key
  key_limit : withinLimit before.host.config.maxStorageKeyLen key.length = true
  value_read : before.host.storage key = some value
  register_limit : register = u64Max ∨ withinLimit before.host.config.maxRegisterLen value.length = true
  proof : recordedStorageError before.host
    (StorageRead.readPlan ctx.trie (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie).looked = none

def cost (before : HostStore NearState) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) : Nat :=
  burnSum before.host.extCosts (StorageRead.preCharges before keyLen keyPtr register) +
  (burnSum before.host.extCosts
    ((StorageRead.readPlan initial (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie).charges initial) +
  burnSum before.host.extCosts (writeReg value.length))

def after (before : HostStore NearState) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) : HostStore NearState :=
  StorageRead.result before keyLen keyPtr register initial
    (StorageRead.readPlan initial (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie) value

def beforeCall (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) : HostStore NearState :=
  ⟨(store.memOf mi).getD (Memory.new 0 none), (chargedStore store cfg.regularOpCost).host⟩

def callStore (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) : Store NearState :=
  let result := after (beforeCall cfg store mi) initial keyLen keyPtr register key value
  Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) result.host (some result.mem)

theorem Ready.charge (before : HostStore NearState) (amount : Nat)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (r : Ready before ctx raw storage keyLen keyPtr register key value) :
    Ready { before with host := (chargeHost before.host amount).1 }
      ctx raw storage keyLen keyPtr register key value := by
  exact ⟨r.wf, r.raw_eq, r.represents, r.nodes, r.accounting, r.key_read,
    r.key_limit, r.value_read, r.register_limit, r.proof⟩

theorem cost_charge (before : HostStore NearState) (amount : Nat) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    cost { before with host := (chargeHost before.host amount).1 }
      initial keyLen keyPtr register key value = cost before initial keyLen keyPtr register key value := rfl

/-- Original canonical resources and credits suffice for the concrete host opcode.
The caller's module resolves the actual installed host, not a supplied execution contract. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (functionIndex address memoryIndex : Nat) (mi : ModuleInst) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddress : mi.funcAddrs[functionIndex]? = some address)
    (hfunction : store.funcs[address]? = some (.host (metered extra "storage_read" storageReadFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : store.mems[memoryIndex]? = some memory)
    (ready : Ready ⟨memory,store.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : store.host.gas.Credits (cfg.regularOpCost +
      (cost ⟨memory,store.host⟩ ctx.trie keyLen keyPtr register key value + rest)))
    (hnext : WP cfg fuel (.next (atCode (callStore cfg store mi ctx.trie keyLen keyPtr register key value)
      limits (base ++ [Value.i64 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (base ++ StorageRead.args keyLen keyPtr register).toArray
      frame callers (.call functionIndex :: code)))
      (cfg.regularOpCost + (cost ⟨memory,store.host⟩ ctx.trie keyLen keyPtr register key value + rest)) post := by
  let original : HostStore NearState := ⟨memory,store.host⟩
  let fee := cost original ctx.trie keyLen keyPtr register key value
  have hmem : (beforeCall cfg store mi).mem = memory := by
    simp [beforeCall, Store.memOf, hmemoryIndex, hmemory]
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost (fee + rest) hc
  have hbefore : beforeCall cfg store mi = { original with host := (chargeHost store.host cfg.regularOpCost).1 } := by
    exact congrArg (fun memory => (⟨memory,(chargedStore store cfg.regularOpCost).host⟩ : HostStore NearState)) hmem
  have hr : Ready (beforeCall cfg store mi) ctx raw storage keyLen keyPtr register key value := by
    rw [hbefore]
    exact ready.charge original cfg.regularOpCost ctx raw storage keyLen keyPtr register key value
  have hcost : cost (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value = fee := by
    rw [hbefore, cost_charge]
  have hh : (beforeCall cfg store mi).host.gas.Credits
      (cost (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value + rest) := by
    rw [hcost]
    exact hb.2.2.2
  have hcredits : (beforeCall cfg store mi).host.gas.Credits
      (burnSum (beforeCall cfg store mi).host.extCosts (StorageRead.preCharges (beforeCall cfg store mi) keyLen keyPtr register) +
        (burnSum (beforeCall cfg store mi).host.extCosts
          ((StorageRead.readPlan ctx.trie (contractKey (beforeCall cfg store mi).host.context.currentAccountId key)
            (beforeCall cfg store mi).host.storageReadsFromTrie).charges ctx.trie) +
        (burnSum (beforeCall cfg store mi).host.extCosts (writeReg value.length) + rest))) := by
    simpa only [cost, Nat.add_assoc] using hh
  have hi := StorageRead.canonical_contract extra (beforeCall cfg store mi) ctx raw hr.wf storage hr.raw_eq
    hr.represents hr.nodes keyLen keyPtr register key value rest hr.accounting hr.key_read hr.key_limit
    hr.value_read hr.register_limit hr.proof hcredits
  have hburn : (after (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value).host.gas.burnt =
      (chargedStore store cfg.regularOpCost).host.gas.burnt + fee := by
    rw [← hcost]
    have hgas : (beforeCall cfg store mi).host.gas.burnt = (chargedStore store cfg.regularOpCost).host.gas.burnt := rfl
    simpa only [after, cost, Nat.add_assoc, hgas] using hi.2.1
  have hpromises : (after (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value).host.gas.promises =
      (chargedStore store cfg.regularOpCost).host.gas.promises := hi.2.2.1
  apply wp_call_host cfg fuel fee rest store limits base (StorageRead.args keyLen keyPtr register)
    [.i64 1] frame callers code functionIndex address mi (metered extra "storage_read" storageReadFn)
    (after (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value)
    hmodule haddress hfunction rfl hc hi.1
  · exact Nat.le_of_eq hburn
  · have hu : (after (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value).host.gas.used =
        (chargedStore store cfg.regularOpCost).host.gas.used + fee := by
      simp only [GasCounter.used, hburn, hpromises]
      omega
    exact Nat.le_of_eq hu
  · exact hi.2.2.2
  · exact hnext

end Wasm.Near.MeteredLogic.StorageReadCalls
