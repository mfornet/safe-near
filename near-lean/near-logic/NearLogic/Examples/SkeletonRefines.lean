import NearLogic.Examples.SkeletonRun
import NearRuntime.Boundary

/-!
# The walking skeleton against its model

The model of `get`: no state, every input to `get` is the call, it returns
`"ok"`, and it fails only when the account cannot pay for its storage. Its
gas bound is loading plus `getCost`. `get_enough` is the first clause of
`Refines` for the module: with at least the bound attached, the boundary's
observation matches the model and uses at most the bound.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near NearInterface

/-- The host `get` starts from, for a context. -/
def hostOf (ctx : Context) : NearState := (Near.Boundary.toVMContext ctx).toNearState ctx.protocol []

/-- The model of the skeleton, deployed with `size` bytes of code. -/
def skelModel (size : Nat) : ContractModel where
  State := Unit
  Call := Unit
  Ret := Unit
  Panic := Empty
  Promise := Empty
  encodeState _ := ∅
  Inv _ := True
  Parses m _ _ := m = "get"
  encodeRet _ := .value okBytes
  encodeReceipts _ _ := []
  panicFailure p := p.elim
  step ctx _ _ :=
    let d := stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached) ctx.locked
    if d > 0 then .error { failure := .lackBalanceForState d, logs := [] }
    else .ok { state := (), ret := (), logs := [], promises := [] }
  gas ctx _ _ := chargesUse (hostOf ctx) (loadingCharges size) + getCost ctx.protocol.wasm (hostOf ctx)
  proofBound _ _ _ := 0

/-- The skeleton as the boundary runs it. -/
def skelCode (size : Nat) (codeOf : Near.Bytes → Near.ContractCode) : Near.Boundary.Code :=
  { code := { module := skelModule, size, hash := "" }, codeOf }

/-- What the skeleton needs of the protocol config. -/
structure SkelProtocol (p : RuntimeConfig) : Prop where
  pos : 0 < minOpCost p.wasm
  limit : prepareLimitError p.wasm.limits skelModule = none
  pagesMin : p.wasm.limits.initialMemoryPages = 1024
  pagesMax : p.wasm.limits.maxMemoryPages = 2048
  ret : 4 ≤ p.wasm.limits.maxLengthReturnedData

theorem raw_empty {size : Nat} {raw : RawStorage} {st : Option Unit}
    (h : (skelModel size).Represents raw st) : raw = ∅ := by
  cases st with
  | none => exact h
  | some _ => exact h.2

/-- **Enough gas.** With at least the model's bound attached, the
boundary's observation of `get` matches the model and uses at most the bound. -/
theorem get_enough (size : Nat) (codeOf : Near.Bytes → Near.ContractCode) (raw : RawStorage)
    (st : Option Unit) (ctx : Context) (hp : SkelProtocol ctx.protocol)
    (hrep : (skelModel size).Represents raw st) (hwf : ctx.WF raw) (hm : ctx.method = "get")
    (hgas : (skelModel size).gas ctx st () ≤ ctx.gasLimit) :
    let r := Near.Boundary.execOn (skelCode size codeOf) raw.toList ctx
    Matches (skelModel size) ctx raw r ((skelModel size).step ctx st ()) ∧
      r.usedGas ≤ (skelModel size).gas ctx st () := by
  have hraw := raw_empty hrep
  subst hraw
  have hlist : (∅ : RawStorage).toList = [] := Finset.toList_empty
  simp only [hlist]
  set Cg := (skelModel size).gas ctx st ()
  have hh0 : (Near.Boundary.toVMContext ctx).toNearState ctx.protocol [] = hostOf ctx := rfl
  have hused0 : (hostOf ctx).gas.used = 0 := rfl
  have hmb : (hostOf ctx).gas.maxBurnt = ctx.protocol.wasm.limits.maxGasBurnt := rfl
  have hpp : (hostOf ctx).gas.prepaid = ctx.prepaidGas := rfl
  obtain ⟨ha, hrd, hrec, hu, hbu, hdist, hl, hb, hsu, hs⟩ := get_vmOutcome ctx.protocol size
    (Near.Boundary.toVMContext ctx) [] Cg hp.pos hp.limit hp.pagesMin hp.pagesMax
    (by simp [VMContext.toNearState, withinLimit, hp.ret])
    (by rw [hh0, hused0]; simp [Cg, skelModel])
    (by rw [hh0, hmb]; exact Nat.le_trans hgas (Nat.min_le_right _ _))
    (by rw [hh0, hpp]; exact Nat.le_trans hgas (Nat.min_le_left _ _))
  have hcheck : Near.checkVMReceipts ctx.protocol codeOf ctx.current ctx.signer ctx.signerPk [] = Except.ok () := rfl
  simp only [Near.Boundary.execOn, skelCode, hm, Near.Boundary.actionsIssue?, hrec, List.findSome?_nil,
    hcheck, Near.Boundary.observe, ha]
  have hsu' : (run ctx.protocol skelModule size "get" (Near.Boundary.toVMContext ctx) []).storageUsage =
      ctx.storageUsage := by
    rw [hsu]; exact Nat.mod_eq_of_lt (by have := hwf.usage_room; simp [Near.Boundary.toVMContext]; omega)
  have hb' : (run ctx.protocol skelModule size "get" (Near.Boundary.toVMContext ctx) []).balance =
      ctx.balance + ctx.attached := by rw [hb]; rfl
  have hs' : (run ctx.protocol skelModule size "get" (Near.Boundary.toVMContext ctx) []).storage = [] := by
    rw [hs]; simp [finalStorage, VMContext.toNearState, sortedKeys]
  rw [hsu', hb']
  have hstep : (skelModel size).step ctx st () =
      (if stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached) ctx.locked > 0 then
        .error ⟨.lackBalanceForState (stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached)
          ctx.locked), []⟩
      else .ok ⟨(), (), [], []⟩) := rfl
  rw [hstep]
  by_cases hd : stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached) ctx.locked > 0
  · simp only [hd, if_true]
    refine ⟨⟨rfl, rfl, rfl, rfl, hl, rfl⟩, Nat.le_trans hbu hu⟩
  · simp only [hd, if_false]
    refine ⟨⟨by simp only [hrd]; rfl, by rw [hs']; rfl, by simp [skelModel, receiptDeposits], by simp [skelModel, storageUsageOf],
      hl, rfl⟩, by simp only [hdist, Nat.sub_zero]; exact hu⟩

end NearLogic.Skeleton
