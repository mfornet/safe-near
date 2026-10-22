import Std

namespace SputnikDAO2

abbrev CodeBytes := List UInt8

structure FactoryInfo where
  factoryId : String
  autoUpdate : Bool
  deriving Repr, DecidableEq

-- `FACTORY` raw-key read: missing uses the account-parent fallback;
-- malformed bytes abort during Borsh decoding.
inductive FactoryRead where
  | missing | stored (info : FactoryInfo) | malformed
  deriving Repr, DecidableEq

def effectiveFactory : FactoryRead → Option String → Option FactoryInfo
  | .missing, fallback => fallback.map (fun id => ⟨id, true⟩)
  | .stored info, _ => some info
  | .malformed, _ => none

-- `get_default_factory_id` takes everything after the FIRST dot in the
-- current account ID. AccountId parsing of that suffix is an SDK obligation.
def factoryParentSuffix (current : String) : Option String :=
  match current.splitOn "." with
  | _ :: suffix => if suffix.isEmpty then none
                   else some (String.intercalate "." suffix)
  | [] => none

def factoryInfoForAccount (read : FactoryRead) (current : String) :
    Option FactoryInfo :=
  effectiveFactory read (factoryParentSuffix current)

structure UpdateContext where
  current : String
  predecessor : String
  factoryRead : FactoryRead
  fallbackFactory : Option String
  successfulPromiseResult : Option CodeBytes
  rawInput : Option CodeBytes
  deriving Repr, DecidableEq

def updateAuthorized (ctx : UpdateContext) (info : FactoryInfo) : Bool :=
  ctx.predecessor == ctx.current ||
    (ctx.predecessor == info.factoryId && info.autoUpdate)

inductive DefaultGasWeight where
  | default
  deriving Repr, DecidableEq

structure UpgradeReceipt where
  receiver : String
  globalCodeHash : String
  migrateMethod : String
  migrateArgs : CodeBytes
  attachedDeposit : Nat
  staticGas : Nat
  gasWeight : DefaultGasWeight
  returned : Bool
  deriving Repr, DecidableEq

def upgradeReceipt (current : String) (hash : String) : UpgradeReceipt :=
  ⟨current, hash, "migrate", [], 0, 0, .default, true⟩

-- Source-level projection of raw `update` after host reads. `hashCode` stands
-- for SHA-256; no cryptographic property or global-code availability is
-- assumed. A successful result means the receipt was scheduled, not that
-- deployment or `migrate` succeeded.
def runUpdate (hashCode : CodeBytes → String) (ctx : UpdateContext) :
    Option UpgradeReceipt := Id.run do
  let some info := effectiveFactory ctx.factoryRead ctx.fallbackFactory |
    return none
  if !updateAuthorized ctx info then return none
  let some code :=
    (if ctx.predecessor == ctx.current then ctx.successfulPromiseResult
      else ctx.rawInput) | return none
  return some (upgradeReceipt ctx.current (hashCode code))

end SputnikDAO2
