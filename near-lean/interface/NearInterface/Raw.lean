/-!
# Raw values at the function-call boundary

The byte-level values a function call consumes and produces, as nearcore
represents them: callback inputs, the receipts a call creates and its return
data. They carry the names they have in `NearVM`, which re-exports them, so
there is a single copy of each type.
-/

namespace Wasm

/-- Result of a promise dependency visible to a callback. NEAR returns
`0` for incomplete, `1` for successful, and `2` for failed results. -/
inductive PromiseResult where
  | notReady
  | successful (data : List UInt8)
  | failed
deriving Inhabited, BEq

/-- Function-call access-key allowance. `none` represents no allowance. -/
abbrev Allowance := Option Nat

/-- Access-key permission carried by promise batch add-key actions. -/
inductive AccessKeyPermission where
  | fullAccess
  | functionCall (allowance : Allowance) (receiverId methodNames : List UInt8)
deriving Inhabited, BEq

/-- `GlobalContractIdentifier`: a 32-byte code hash, or the account that
deployed the contract. -/
inductive GlobalContractId where
  | codeHash (hash : List UInt8)
  | accountId (accountId : List UInt8)
deriving Inhabited, BEq

/-- `GlobalContractIdentifier::len`, the byte count the per-byte fee charges. -/
def GlobalContractId.length : GlobalContractId → Nat
  | .codeHash _ => 32
  | .accountId id => id.length

/-- Receipt actions emitted by promise batch action host functions. -/
inductive PromiseAction where
  | createAccount
  | deployContract (code : List UInt8)
  | functionCall (methodName args : List UInt8) (amount : Nat) (gas : UInt64)
  | transfer (amount : Nat)
  | stake (amount : Nat) (publicKey : List UInt8)
  | addKey (publicKey : List UInt8) (nonce : UInt64) (permission : AccessKeyPermission)
  | deleteKey (publicKey : List UInt8)
  | deleteAccount (beneficiaryId : List UInt8)
  | useGlobalContract (contract : GlobalContractId)
deriving Inhabited, BEq

end Wasm

namespace Wasm.Near

abbrev Bytes := List UInt8

/-- `ReturnData`. -/
inductive ReturnData
  | value (bytes : List UInt8)
  /-- The call's result is the result of the receipt created at this index. -/
  | receiptIndex (idx : Nat)
  | none
  deriving Repr, BEq, Inhabited

/-- One receipt to create, in the order of `promise_batch_create` /
`promise_then` calls. `dependencies` are indices into the same list: the
receipt runs once each of them has produced its data. -/
structure ReceiptSpec where
  receiverId : List UInt8
  actions : List PromiseAction
  dependencies : List Nat := []
  deriving BEq, Inhabited

/-- Each dependency refers to a receipt created earlier in this call. Repeated
edges are allowed: they represent separate data dependencies. -/
def ReceiptSpec.ValidAt (index : Nat) (r : ReceiptSpec) : Prop :=
  ∀ dependency ∈ r.dependencies, dependency < index

def receiptsValidFrom (index : Nat) : List ReceiptSpec → Bool
  | [] => true
  | r :: rs => r.dependencies.all (· < index) && receiptsValidFrom (index + 1) rs

def ReceiptsWellFormedFrom (index : Nat) : List ReceiptSpec → Prop
  | [] => True
  | r :: rs => r.ValidAt index ∧ ReceiptsWellFormedFrom (index + 1) rs

/-- The executable graph check proves backward-only dependencies, rather than
assuming host-created handles were valid. -/
theorem receiptsValidFrom_iff (rs : List ReceiptSpec) (index : Nat) :
    receiptsValidFrom index rs = true ↔ ReceiptsWellFormedFrom index rs := by
  induction rs generalizing index with
  | nil => simp [receiptsValidFrom, ReceiptsWellFormedFrom]
  | cons r rs ih =>
    simp [receiptsValidFrom, ReceiptsWellFormedFrom, ReceiptSpec.ValidAt, List.all_eq_true, ih]

/-- Looking up a receipt in a valid suffix preserves its creation-order bound. -/
theorem dependency_before_index {rs : List ReceiptSpec} {start index dependency : Nat}
    {r : ReceiptSpec} (hwf : ReceiptsWellFormedFrom start rs)
    (hget : rs[index]? = some r) (hdep : dependency ∈ r.dependencies) :
    dependency < start + index := by
  induction rs generalizing start index with
  | nil => simp at hget
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst r
      exact hwf.1 _ hdep
    | succ index =>
      have htail : tail[index]? = some r := hget
      have hlt := ih hwf.2 htail
      omega

/-- Nonempty dependency paths in the exact emitted receipt list. -/
inductive ReceiptDependencyPath (rs : List ReceiptSpec) : Nat → Nat → Prop
  | edge {source target : Nat} {r : ReceiptSpec}
      (lookup : rs[source]? = some r) (member : target ∈ r.dependencies) :
      ReceiptDependencyPath rs source target
  | trans {source middle target : Nat}
      (first : ReceiptDependencyPath rs source middle)
      (rest : ReceiptDependencyPath rs middle target) : ReceiptDependencyPath rs source target

/-- Every dependency path strictly decreases creation indices, so callbacks
cannot indirectly depend on themselves. -/
theorem dependencyPath_decreases {rs : List ReceiptSpec}
    (hwf : ReceiptsWellFormedFrom 0 rs) {source target : Nat}
    (path : ReceiptDependencyPath rs source target) : target < source := by
  induction path with
  | edge lookup member =>
    simpa only [Nat.zero_add] using dependency_before_index hwf lookup member
  | trans _ _ ihFirst ihRest => exact Nat.lt_trans ihRest ihFirst

theorem no_receipt_dependency_cycle {rs : List ReceiptSpec}
    (hwf : ReceiptsWellFormedFrom 0 rs) (index : Nat) :
    ¬ReceiptDependencyPath rs index index := by
  intro path
  exact Nat.lt_irrefl index (dependencyPath_decreases hwf path)

end Wasm.Near
