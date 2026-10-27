import NearLogic.Rules.CallWasm

/-!
# `call_indirect` to a function with a specification

`mwpi_call_indirect_spec` is `mwpi_call_spec` (`NearLogic/Rules/CallWasm.lean`)
for `call_indirect ty t`, built on `mwpi_call_indirect`: the caller holds the
table entry `ta ↦[wt][ idx ] Ref.func a` for the index on top of the stack,
the callee's `MFunSpec` and its precondition, and pays one
`regular_op_cost`, the activation of the callee's frame and its cost
`K args`, keeping `R`. The table entry is handed back with the results.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

section Rules

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

/-- A `call_indirect` through table `t` (address `ta`) at index `idx`, whose
entry names the Wasm function `a` of the expected type `f.mi.types[ty]!`, a
function with a specification: the caller pays the instruction, the
activation and the function's cost `K args`, and keeps `R` and the entry. -/
theorem mwpi_call_indirect_spec (ty t ta : Nat) (idx : UInt32) (a : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (code : Func) (vs₀ args : List Value) {Cg R : Nat}
    (P : List Value → IProp GF) (K : List Value → Nat) (Q : List Value → List Value → IProp GF)
    (hta : f.mi.tableAddrs[t]? = some ta) (hty : type = f.mi.types[ty]!)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        (K args + R)) ∗
      ta ↦[wt][ idx.toNat ] Ref.func a ∗ a ↪[wf] FuncInst.wasm type inst code ∗
      inst ↪[inst] mi ∗ MFunSpec cfg lim (d + 1) type inst mi code Cg P K Q ∗ P args ∗
      ▷ (∀ rs, ta ↦[wt][ idx.toNat ] Ref.func a -∗ credits Cg R -∗ Q args rs -∗
          Φ.normal (vs₀ ++ rs) f)
      ⊢ mwpi cfg lim d f (vs₀ ++ args ++ [.i32 idx]) [.call_indirect ty t] Φ := by
  iintro ⟨Hc, Ht, #Hf, #Hi, Hs, HP, HΦ⟩
  iapply mwpi_call_indirect ty t ta idx a type inst mi code vs₀ args hta hty hlen hd
  isplitl [Hc]
  · iexact Hc
  isplitl [Ht]
  · iexact Ht
  isplitr
  · iexact Hf
  isplitr
  · iexact Hi
  inext
  iintro Ht Hc
  iapply mwpInvoke_wand
  isplitl [HP Hc Hs]
  · iunfold MFunSpec at Hs
    icases Hs with #Hs
    iapply Hs $$ %args %R HP Hc
  isplit
  · iintro %rs ⟨Hc, HQ⟩
    iapply HΦ $$ %rs Ht Hc HQ
  · iintro HF
    iexfalso
    iexact HF

/-- `mwpi_call_indirect_spec` on a stack holding just the arguments and the
index. -/
theorem mwpi_call_indirect_spec_args (ty t ta : Nat) (idx : UInt32) (a : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (code : Func) (args : List Value) {Cg R : Nat}
    (P : List Value → IProp GF) (K : List Value → Nat) (Q : List Value → List Value → IProp GF)
    (hta : f.mi.tableAddrs[t]? = some ta) (hty : type = f.mi.types[ty]!)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        (K args + R)) ∗
      ta ↦[wt][ idx.toNat ] Ref.func a ∗ a ↪[wf] FuncInst.wasm type inst code ∗
      inst ↪[inst] mi ∗ MFunSpec cfg lim (d + 1) type inst mi code Cg P K Q ∗ P args ∗
      ▷ (∀ rs, ta ↦[wt][ idx.toNat ] Ref.func a -∗ credits Cg R -∗ Q args rs -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f (args ++ [.i32 idx]) [.call_indirect ty t] Φ :=
  mwpi_call_indirect_spec (vs₀ := []) ty t ta idx a type inst mi code args P K Q hta hty hlen hd

end Rules

end NearLogic
