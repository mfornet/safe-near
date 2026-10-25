import NearVM.Outcome

namespace Wasm.Near

/-- A joint handle remembers its exact ordered dependency vector, rather than
recursively traversing earlier promises again with an interpreter fuel bound. -/
inductive PromiseHandle
  | receipt (index : Nat)
  | joint (dependencies : List Nat)
  deriving BEq, Inhabited

def PromiseHandle.dependencies : PromiseHandle → List Nat
  | .receipt index => [index]
  | .joint dependencies => dependencies

structure PromiseGraph where
  handles : List PromiseHandle := []
  receipts : List ReceiptSpec := []
  deriving Inhabited

def PromiseGraph.addReceipt (g : PromiseGraph) (r : ReceiptSpec) : PromiseGraph :=
  { handles := g.handles ++ [.receipt g.receipts.length], receipts := g.receipts ++ [r] }

def PromiseGraph.addJoint (g : PromiseGraph) (dependencies : List Nat) : PromiseGraph :=
  { g with handles := g.handles ++ [.joint dependencies] }

def expandDependencies (handles : List PromiseHandle) : List Nat → Option (List Nat)
  | [] => some []
  | index :: rest => do
    let handle ← handles[index]?
    let tail ← expandDependencies handles rest
    pure (handle.dependencies ++ tail)

/-- Exact join semantics: concatenate the dependency vectors in input order,
including repeated handles and repeated dependencies. -/
inductive ExpandsDependencies (handles : List PromiseHandle) : List Nat → List Nat → Prop
  | nil : ExpandsDependencies handles [] []
  | cons {index : Nat} {rest dependencies : List Nat} {handle : PromiseHandle}
      (lookup : handles[index]? = some handle)
      (tail : ExpandsDependencies handles rest dependencies) :
      ExpandsDependencies handles (index :: rest) (handle.dependencies ++ dependencies)

theorem expandDependencies_iff (handles : List PromiseHandle) (indices dependencies : List Nat) :
    expandDependencies handles indices = some dependencies ↔
      ExpandsDependencies handles indices dependencies := by
  induction indices generalizing dependencies with
  | nil =>
    constructor
    · intro h
      simp only [expandDependencies, Option.some.injEq] at h
      subst dependencies
      exact .nil
    · intro h
      cases h
      rfl
  | cons index rest ih =>
    constructor
    · intro h
      obtain ⟨handle, lookup, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, htail, h⟩ := Option.bind_eq_some_iff.mp h
      have heq : handle.dependencies ++ tail = dependencies := Option.some.inj h
      subst dependencies
      exact .cons lookup (ih tail |>.mp htail)
    · intro h
      cases h with
      | cons lookup tail => simp [expandDependencies, lookup, (ih _).mpr tail]

def convertPromise (g : PromiseGraph) : NearPromise → Option PromiseGraph
  | .batch account actions => some (g.addReceipt { receiverId := account, actions })
  | .callback base account actions => do
    let handle ← g.handles[base]?
    pure (g.addReceipt { receiverId := account, actions, dependencies := handle.dependencies })
  | .and indices => do
    let dependencies ← expandDependencies g.handles indices
    pure (g.addJoint dependencies)
  | .yielded receiver actions dataId =>
    some (g.addReceipt { receiverId := receiver, actions, yieldDataId := some dataId })

inductive ConvertsPromise : PromiseGraph → NearPromise → PromiseGraph → Prop
  | batch (g : PromiseGraph) (account : List UInt8) (actions : List PromiseAction) :
      ConvertsPromise g (.batch account actions) (g.addReceipt { receiverId := account, actions })
  | callback (g : PromiseGraph) (base : Nat) (account : List UInt8) (actions : List PromiseAction)
      (handle : PromiseHandle) (lookup : g.handles[base]? = some handle) :
      ConvertsPromise g (.callback base account actions)
        (g.addReceipt { receiverId := account, actions, dependencies := handle.dependencies })
  | joint (g : PromiseGraph) (indices dependencies : List Nat)
      (expands : ExpandsDependencies g.handles indices dependencies) :
      ConvertsPromise g (.and indices) (g.addJoint dependencies)
  | yielded (g : PromiseGraph) (receiver : List UInt8) (actions : List PromiseAction)
      (dataId : List UInt8) :
      ConvertsPromise g (.yielded receiver actions dataId)
        (g.addReceipt { receiverId := receiver, actions, yieldDataId := some dataId })

theorem convertPromise_sound {g next : PromiseGraph} {p : NearPromise}
    (h : convertPromise g p = some next) : ConvertsPromise g p next := by
  cases p with
  | batch account actions =>
    simp only [convertPromise, Option.some.injEq] at h
    subst next
    exact .batch g account actions
  | callback base account actions =>
    obtain ⟨handle, lookup, h⟩ := Option.bind_eq_some_iff.mp h
    have heq := Option.some.inj h
    subst next
    exact .callback g base account actions handle lookup
  | and indices =>
    obtain ⟨dependencies, he, h⟩ := Option.bind_eq_some_iff.mp h
    have heq := Option.some.inj h
    subst next
    exact .joint g indices dependencies ((expandDependencies_iff _ _ _).mp he)
  | yielded receiver actions dataId =>
    simp only [convertPromise, Option.some.injEq] at h
    subst next
    exact .yielded g receiver actions dataId

theorem convertPromise_complete {g next : PromiseGraph} {p : NearPromise}
    (h : ConvertsPromise g p next) : convertPromise g p = some next := by
  cases h with
  | batch => rfl
  | callback _ _ _ _ lookup => simp [convertPromise, lookup]
  | joint _ _ expands => simp [convertPromise, (expandDependencies_iff _ _ _).mpr expands]
  | yielded => rfl

def convertPromisesFrom (g : PromiseGraph) : List NearPromise → Option PromiseGraph
  | [] => some g
  | p :: ps => do
    let next ← convertPromise g p
    convertPromisesFrom next ps

def convertPromises (ps : List NearPromise) : Option PromiseGraph := convertPromisesFrom {} ps

inductive ConvertsPromises : PromiseGraph → List NearPromise → PromiseGraph → Prop
  | nil (g : PromiseGraph) : ConvertsPromises g [] g
  | cons {g next result : PromiseGraph} {p : NearPromise} {ps : List NearPromise}
      (head : ConvertsPromise g p next) (tail : ConvertsPromises next ps result) :
      ConvertsPromises g (p :: ps) result

theorem convertPromisesFrom_sound {g result : PromiseGraph} {ps : List NearPromise}
    (h : convertPromisesFrom g ps = some result) : ConvertsPromises g ps result := by
  induction ps generalizing g with
  | nil =>
    simp only [convertPromisesFrom, Option.some.injEq] at h
    subst result
    exact .nil g
  | cons p ps ih =>
    obtain ⟨next, hn, h⟩ := Option.bind_eq_some_iff.mp h
    exact .cons (convertPromise_sound hn) (ih h)

theorem convertPromisesFrom_complete {g result : PromiseGraph} {ps : List NearPromise}
    (h : ConvertsPromises g ps result) : convertPromisesFrom g ps = some result := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [convertPromisesFrom, convertPromise_complete head, ih]

/-- The executable conversion and the exact ordered transition relation coincide. -/
theorem convertPromises_iff (ps : List NearPromise) (result : PromiseGraph) :
    convertPromises ps = some result ↔ ConvertsPromises {} ps result :=
  ⟨convertPromisesFrom_sound, convertPromisesFrom_complete⟩

/-- Existing handles reference only existing receipts; emitted receipt edges
point strictly backwards. This invariant does not depend on a final validator. -/
def PromiseGraph.Valid (g : PromiseGraph) : Prop :=
  ReceiptsWellFormedFrom 0 g.receipts ∧
    ∀ handle ∈ g.handles, ∀ dependency ∈ handle.dependencies, dependency < g.receipts.length

private theorem receiptsWellFormed_snoc (rs : List ReceiptSpec) (start : Nat) (r : ReceiptSpec)
    (hwf : ReceiptsWellFormedFrom start rs) (hr : r.ValidAt (start + rs.length)) :
    ReceiptsWellFormedFrom start (rs ++ [r]) := by
  induction rs generalizing start with
  | nil => exact ⟨hr, trivial⟩
  | cons head tail ih =>
    refine ⟨hwf.1, ih (start + 1) hwf.2 ?_⟩
    intro dependency member
    have hlt := hr dependency member
    simp only [List.length_cons] at hlt
    omega

theorem PromiseGraph.valid_empty : Valid ({} : PromiseGraph) := by
  exact ⟨trivial, by simp⟩

theorem PromiseGraph.Valid.addReceipt {g : PromiseGraph} (hwf : g.Valid)
    (r : ReceiptSpec) (hr : r.ValidAt g.receipts.length) : (g.addReceipt r).Valid := by
  constructor
  · apply receiptsWellFormed_snoc _ _ _ hwf.1
    simpa only [Nat.zero_add] using hr
  · intro handle hm dependency hd
    rcases List.mem_append.mp hm with hm | hm
    · have hlt := hwf.2 handle hm dependency hd
      change dependency < (g.receipts ++ [r]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · simp only [List.mem_singleton] at hm
      subst handle
      simp only [PromiseHandle.dependencies, List.mem_singleton] at hd
      subst dependency
      change g.receipts.length < (g.receipts ++ [r]).length
      simp

theorem PromiseGraph.Valid.addJoint {g : PromiseGraph} (hwf : g.Valid)
    (dependencies : List Nat) (hd : ∀ d ∈ dependencies, d < g.receipts.length) :
    (g.addJoint dependencies).Valid := by
  refine ⟨hwf.1, ?_⟩
  intro handle hm dependency member
  rcases List.mem_append.mp hm with hm | hm
  · exact hwf.2 handle hm dependency member
  · simp only [List.mem_singleton] at hm
    subst handle
    exact hd dependency member

theorem ExpandsDependencies.bounded {g : PromiseGraph} (hwf : g.Valid)
    {indices dependencies : List Nat} (h : ExpandsDependencies g.handles indices dependencies) :
    ∀ dependency ∈ dependencies, dependency < g.receipts.length := by
  induction h with
  | nil => simp
  | cons lookup _ ih =>
    intro dependency member
    rcases List.mem_append.mp member with head | tail
    · exact hwf.2 _ (List.mem_of_getElem? lookup) dependency head
    · exact ih dependency tail

theorem ConvertsPromise.preserves {g next : PromiseGraph} {p : NearPromise}
    (h : ConvertsPromise g p next) (hwf : g.Valid) : next.Valid := by
  cases h with
  | batch => exact hwf.addReceipt _ (by simp [ReceiptSpec.ValidAt])
  | callback _ _ _ _ lookup =>
    exact hwf.addReceipt _ (hwf.2 _ (List.mem_of_getElem? lookup))
  | joint _ _ expands => exact hwf.addJoint _ (expands.bounded hwf)
  | yielded => exact hwf.addReceipt _ (by simp [ReceiptSpec.ValidAt])

theorem ConvertsPromises.preserves {g result : PromiseGraph} {ps : List NearPromise}
    (h : ConvertsPromises g ps result) (hwf : g.Valid) : result.Valid := by
  induction h with
  | nil => exact hwf
  | cons head _ ih => exact ih (head.preserves hwf)

/-- Successful executable conversion itself establishes a valid graph. -/
theorem convertPromises_valid {ps : List NearPromise} {g : PromiseGraph}
    (h : convertPromises ps = some g) : g.Valid :=
  ((convertPromises_iff ps g).mp h).preserves PromiseGraph.valid_empty

theorem expandDependencies_total (handles : List PromiseHandle) (indices : List Nat)
    (hbound : ∀ index ∈ indices, index < handles.length) :
    ∃ dependencies, ExpandsDependencies handles indices dependencies := by
  induction indices with
  | nil => exact ⟨[], .nil⟩
  | cons index rest ih =>
    have hi : index < handles.length := hbound index (by simp)
    obtain ⟨dependencies, htail⟩ := ih (fun i member => hbound i (by simp [member]))
    have lookup : handles[index]? = some (handles[index]'hi) :=
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
    exact ⟨_, .cons lookup htail⟩

theorem ConvertsPromise.handles_length {g next : PromiseGraph} {p : NearPromise}
    (h : ConvertsPromise g p next) : next.handles.length = g.handles.length + 1 := by
  cases h <;> simp [PromiseGraph.addReceipt, PromiseGraph.addJoint]

theorem convertPromise_total (g : PromiseGraph) (p : NearPromise)
    (hwf : PromiseWellFormedAt g.handles.length p) : ∃ next, ConvertsPromise g p next := by
  cases p with
  | batch account actions => exact ⟨_, .batch g account actions⟩
  | callback base account actions =>
    have hi : base < g.handles.length := hwf
    have lookup : g.handles[base]? = some (g.handles[base]'hi) :=
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
    exact ⟨_, .callback g base account actions _ lookup⟩
  | and indices =>
    obtain ⟨dependencies, expands⟩ := expandDependencies_total g.handles indices hwf
    exact ⟨_, .joint g indices dependencies expands⟩
  | yielded receiver actions dataId => exact ⟨_, .yielded g receiver actions dataId⟩

theorem convertPromisesFrom_total (g : PromiseGraph) (ps : List NearPromise)
    (hwf : PromisesWellFormedFrom g.handles.length ps) :
    ∃ result, ConvertsPromises g ps result := by
  induction ps generalizing g with
  | nil => exact ⟨g, .nil g⟩
  | cons p ps ih =>
    obtain ⟨next, head⟩ := convertPromise_total g p hwf.1
    have htail : PromisesWellFormedFrom next.handles.length ps := by
      rw [head.handles_length]
      exact hwf.2
    obtain ⟨result, tail⟩ := ih next htail
    exact ⟨result, .cons head tail⟩

/-- Every valid raw handle graph converts. The final receipt validator is not
used as an assumption or as an escape hatch for valid joins. -/
theorem convertPromises_total (ps : List NearPromise) (hwf : PromisesWellFormedFrom 0 ps) :
    ∃ result, convertPromises ps = some result := by
  obtain ⟨result, converts⟩ := convertPromisesFrom_total {} ps hwf
  exact ⟨result, (convertPromises_iff ps result).mpr converts⟩

theorem ExpandsDependencies.indices_bounded {handles : List PromiseHandle}
    {indices dependencies : List Nat} (h : ExpandsDependencies handles indices dependencies) :
    ∀ index ∈ indices, index < handles.length := by
  induction h with
  | nil => simp
  | cons lookup _ ih =>
    intro index member
    rcases List.mem_cons.mp member with rfl | tail
    · exact (List.getElem?_eq_some_iff.mp lookup).1
    · exact ih index tail

theorem ConvertsPromise.rawWellFormed {g next : PromiseGraph} {p : NearPromise}
    (h : ConvertsPromise g p next) : PromiseWellFormedAt g.handles.length p := by
  cases h with
  | batch => trivial
  | callback _ _ _ _ lookup => exact (List.getElem?_eq_some_iff.mp lookup).1
  | joint _ _ expands => exact expands.indices_bounded
  | yielded => trivial

theorem ConvertsPromises.rawWellFormed {g result : PromiseGraph} {ps : List NearPromise}
    (h : ConvertsPromises g ps result) : PromisesWellFormedFrom g.handles.length ps := by
  induction h with
  | nil => trivial
  | cons head _ ih =>
    refine ⟨head.rawWellFormed, ?_⟩
    rw [head.handles_length] at ih
    exact ih

/-- Conversion succeeds exactly on the supported, backward-only handle graphs. -/
theorem convertPromises_accepts_iff (ps : List NearPromise) :
    (convertPromises ps).isSome = true ↔ promisesValidFrom 0 ps = true := by
  constructor
  · intro h
    cases hc : convertPromises ps with
    | none => simp [hc] at h
    | some graph =>
      exact (promisesValidFrom_iff ps 0).mpr (((convertPromises_iff ps graph).mp hc).rawWellFormed)
  · intro h
    obtain ⟨graph, hc⟩ := convertPromises_total ps ((promisesValidFrom_iff ps 0).mp h)
    simp [hc]

theorem ConvertsPromises.deterministic {g first second : PromiseGraph} {ps : List NearPromise}
    (hfirst : ConvertsPromises g ps first) (hsecond : ConvertsPromises g ps second) : first = second :=
  Option.some.inj ((convertPromisesFrom_complete hfirst).symm.trans (convertPromisesFrom_complete hsecond))

theorem ConvertsPromises.handles_length {g result : PromiseGraph} {ps : List NearPromise}
    (h : ConvertsPromises g ps result) : result.handles.length = g.handles.length + ps.length := by
  induction h with
  | nil => simp
  | cons head _ ih =>
    rw [head.handles_length] at ih
    simp only [List.length_cons]
    omega

theorem convertPromises_receipts_valid {ps : List NearPromise} {g : PromiseGraph}
    (h : convertPromises ps = some g) : receiptsValidFrom 0 g.receipts = true :=
  (receiptsValidFrom_iff g.receipts 0).mpr (convertPromises_valid h).1

/-- Only receipt handles can be returned, even if a joint has one dependency. -/
def PromiseGraph.returnedReceipt? (g : PromiseGraph) (index : Nat) : Option Nat :=
  match g.handles[index]? with
  | some (.receipt receipt) => some receipt
  | _ => none

/-- Resolve the selected raw handle or the exact selected return bytes. -/
def PromiseGraph.returnData? (g : PromiseGraph) (ns : NearState) : Option ReturnData :=
  match ns.returnedPromise with
  | some index => (g.returnedReceipt? index).map ReturnData.receiptIndex
  | none => some (match ns.returnData with | some bytes => .value bytes | none => .none)

theorem PromiseGraph.returnedReceipt_lt {g : PromiseGraph} (hwf : g.Valid)
    {index receipt : Nat} (h : g.returnedReceipt? index = some receipt) : receipt < g.receipts.length := by
  unfold returnedReceipt? at h
  cases lookup : g.handles[index]? with
  | none => simp [lookup] at h
  | some handle =>
    cases handle with
    | receipt value =>
      simp only [lookup, Option.some.injEq] at h
      subst receipt
      exact hwf.2 _ (List.mem_of_getElem? lookup) value (by simp [PromiseHandle.dependencies])
    | joint dependencies => simp [lookup] at h

end Wasm.Near
