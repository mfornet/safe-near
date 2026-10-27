import Bridge.Functions.VecDeref
import NearLogic.Tactic.Step

/-!
# `<Vec<T> as Deref>::deref` (function 779), stepped with `mstep`

`VecDeref.lean` again, its body proved with the `mstep` tactic
(`NearLogic/Tactic/Step.lean`) instead of rule by rule: one `mstep` per
instruction, `mstep [H]` for the loads and stores on the points-to `H`. The
statements are those of `WNear.Binary.VecDeref`, whose byte-splitting lemmas,
`pre` and `post` are reused.
-/

namespace WNear.Binary.VecDerefAuto

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecDeref (storeBytes_load_i32 memBytes_split8 memBytes_split12 memBytes_join8
  memBytes_join12)

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {Φ : Post NearState GF} {Cg R : Nat}

/-- `VecDeref.body_spec`, by `mstep`. -/
theorem body_spec (f : Frame) (out vec : UInt32) (n : Nat) (ob vb : List UInt8)
    (hob : ob.length = 8) (hvb : vb.length = 12)
    (h0 : f.locals[0]? = some (.i32 out)) (h1 : f.locals[1]? = some (.i32 vec))
    (hn : f.mi.memAddrs[0]? = some n) :
    credits Cg (8 * cfg.regularOpCost + R) ∗ n ↦[wms][ out.toNat ] ob ∗
      n ↦[wms][ vec.toNat ] vb ∗
      (credits Cg R -∗ n ↦[wms][ out.toNat ] (vb.take 4 ++ vb.drop 8) -∗
        n ↦[wms][ vec.toNat ] vb -∗ Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] f779.body Φ := by
  iintro ⟨Hc, Ho, Hv, HΦ⟩
  icases memBytes_split8 n out.toNat ob hob $$ Ho with ⟨Ho1, Ho2⟩
  icases memBytes_split12 n vec.toNat vb hvb $$ Hv with ⟨Hv1, Hv2, Hv3⟩
  simp only [f779]
  mstep; mstep; mstep [Hv3]; mstep [Ho2]   -- out+4 := vec+8
  mstep; mstep; mstep [Hv1]; mstep [Ho1]   -- out   := vec
  rw [storeBytes_load_i32 _ (by simp; omega), storeBytes_load_i32 (vb.take 4) (by simp; omega)]
  iapply HΦ $$ Hc [Ho1 Ho2] [Hv1 Hv2 Hv3]
  · iapply memBytes_join8 n out.toNat _ _ (by simp; omega) $$ [Ho1 Ho2]
    isplitl [Ho1] <;> iassumption
  · iapply memBytes_join12 n vec.toNat vb hvb
    isplitl [Hv1]; iexact Hv1
    isplitl [Hv2] <;> iassumption

end Body

/-! ## The function -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecDeref (pre post)

/-- `<Vec<T> as Deref>::deref` (function 779 of `contract.wasm`), at any call
depth, for the memory `n` of its instance: 8 instructions. Same statement as
`VecDeref.f779_spec`. -/
theorem f779_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec : UInt32) (ob vb : List UInt8)
    (hob : ob.length = 8) (hvb : vb.length = 12) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f779 Cg (pre n out vec ob vb)
      (fun _ => 8 * cfg.regularOpCost) (post n out vec vb) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Ho, Hv⟩
  subst hargs
  iapply body_spec ⟨entryLocals f779 [.i32 out, .i32 vec], inst, mi⟩ out vec n ob vb hob hvb
    rfl rfl hn
  isplitl [Hc]; iexact Hc
  isplitl [Ho]; iexact Ho
  isplitl [Hv]; iexact Hv
  iintro Hc Ho Hv
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold post
  iframe Hc Ho Hv
  ipureintro; rfl

end Spec

end WNear.Binary.VecDerefAuto
