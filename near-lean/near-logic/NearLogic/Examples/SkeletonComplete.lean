import NearLogic.Examples.SkeletonRefines
import NearLogic.Examples.SkeletonBelow
import NearRuntime.BoundaryResolution

/-!
# The walking skeleton refines its model

`skel_refines`: every clause of `Refines` for the skeleton, deployed with
`size` bytes of code, under a protocol with the limits it needs
(`SkelProtocol`). With enough gas it is `get_enough`; below the bound
`get_vm_any` leaves an out-of-gas failure or the same success; any other
method is not exported.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near NearInterface

theorem exportFunc_skel {m : String} (hm : m ≠ "get") : skelModule.exportFunc? m = none := by
  simp [Module.exportFunc?, skelModule, Ne.symm hm]

/-- The model's step for a context. -/
theorem skel_step (size : Nat) (ctx : Context) (st : Option Unit) :
    (skelModel size).step ctx st () =
      (if stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached) ctx.locked > 0 then
        .error ⟨.lackBalanceForState (stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached)
          ctx.locked), []⟩
      else .ok ⟨(), (), [], []⟩) := rfl

/-- The VM outcome of `get` on a context, below or above the bound. -/
theorem get_boundary (size : Nat) (codeOf : Near.Bytes → Near.ContractCode) (raw : RawStorage)
    (st : Option Unit) (ctx : Context) (hp : SkelProtocol ctx.protocol)
    (hrep : (skelModel size).Represents raw st) (hwf : ctx.WF raw) (hm : ctx.method = "get") :
    let r := Near.Boundary.execOn (skelCode size codeOf) raw.toList ctx
    Matches (skelModel size) ctx raw r ((skelModel size).step ctx st ()) ∨
      (r.outcome = .error .outOfGas ∧ RolledBack ctx raw r ∧ r.logs = []) := by
  have hraw := raw_empty hrep
  subst hraw
  have hlist : (∅ : RawStorage).toList = [] := Finset.toList_empty
  simp only [hlist]
  have hcheck : Near.checkVMReceipts ctx.protocol codeOf ctx.current ctx.signer ctx.signerPk [] = Except.ok () := rfl
  rcases get_vm_any ctx.protocol size (Near.Boundary.toVMContext ctx) [] hp.pos hp.limit hp.pagesMin hp.pagesMax
    (by simp [VMContext.toNearState, withinLimit, hp.ret]) with
    ⟨e, hge, ha, -, hrec, hl⟩ | ⟨ha, hrd, hrec, hdist, hl, hb, hsu, hs⟩
  · right
    have hobs : (Near.Boundary.execOn (skelCode size codeOf) [] ctx).outcome = .error .outOfGas := by
      simp only [Near.Boundary.execOn, skelCode, hm, Near.Boundary.observe, ha]
      rcases hge with rfl | rfl <;> rfl
    refine ⟨hobs, ?_, ?_⟩
    · have := Near.Boundary.execOn_rolledBack (skelCode size codeOf) [] ctx hobs
      simpa using this
    · simp only [Near.Boundary.execOn, skelCode, hm, Near.Boundary.observe, ha]
      exact hl
  · left
    simp only [Near.Boundary.execOn, skelCode, hm, Near.Boundary.actionsIssue?, hrec, List.findSome?_nil,
      hcheck, Near.Boundary.observe, ha]
    have hsu' : (run ctx.protocol skelModule size "get" (Near.Boundary.toVMContext ctx) []).storageUsage =
        ctx.storageUsage := by
      rw [hsu]; exact Nat.mod_eq_of_lt (by have := hwf.usage_room; simp [Near.Boundary.toVMContext]; omega)
    have hb' : (run ctx.protocol skelModule size "get" (Near.Boundary.toVMContext ctx) []).balance =
        ctx.balance + ctx.attached := by rw [hb]; rfl
    have hs' : (run ctx.protocol skelModule size "get" (Near.Boundary.toVMContext ctx) []).storage = [] := by
      rw [hs]; simp [finalStorage, VMContext.toNearState, sortedKeys]
    rw [hsu', hb', skel_step]
    by_cases hd : stakeDeficit ctx.protocol ctx.storageUsage (ctx.balance + ctx.attached) ctx.locked > 0
    · simp only [hd, if_true]
      exact ⟨rfl, rfl, rfl, rfl, hl, rfl⟩
    · simp only [hd, if_false]
      exact ⟨by simp only [hrd]; rfl, by rw [hs']; rfl, by simp [skelModel, receiptDeposits],
        by simp [skelModel, storageUsageOf], hl, rfl⟩

/-- **The walking skeleton refines its model.** -/
theorem skel_refines (size : Nat) (codeOf : Near.Bytes → Near.ContractCode) (protocol : RuntimeConfig)
    (hp : SkelProtocol protocol) :
    Refines Near.Boundary.nearRuntime protocol (skelCode size codeOf) (skelModel size) := by
  intro raw st ctx hrep hwf hprot
  subst hprot
  by_cases hm : ctx.method = "get"
  · have hb := get_boundary size codeOf raw st ctx hp hrep hwf hm
    have hexec : Near.Boundary.nearRuntime.exec (skelCode size codeOf) raw ctx =
        Near.Boundary.execOn (skelCode size codeOf) raw.toList ctx := rfl
    rw [hexec]
    refine ⟨?_, ?_, ?_⟩
    · intro msg h
      rcases hb with hmt | ⟨ho, -, -⟩
      · rw [skel_step size ctx st] at hmt
        split at hmt
        · have := hmt.1; rw [h] at this; cases this
        · have := hmt.1; rw [h] at this; cases this
      · rw [h] at ho; cases ho
    · intro c _
      refine ⟨fun hgas _ => get_enough size codeOf raw st ctx hp hrep hwf hm hgas, ?_⟩
      rcases hb with hmt | ⟨ho, hrb, hl⟩
      · exact Or.inl hmt
      · exact Or.inr ⟨Or.inl ho, hrb, by rw [hl]; exact List.nil_prefix⟩
    · intro hn
      exact absurd ⟨(), hm⟩ hn
  · refine ⟨(Near.Boundary.nearRuntime_not_exported _ raw ctx rfl rfl (exportFunc_skel hm)).2,
      fun c hc => absurd hc hm, fun _ => (Near.Boundary.nearRuntime_not_exported _ raw ctx rfl rfl
        (exportFunc_skel hm)).1⟩

end NearLogic.Skeleton
