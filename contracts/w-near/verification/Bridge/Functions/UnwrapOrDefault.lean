import Binary.Code.Part01
import Bridge.Functions.MemCpy
import Bridge.Functions.ResultExpect

/-!
# `Option<Contract>::unwrap_or_default` (function 155), the `Some` path

`unwrap_or_default(out, opt)` on the `Option<Contract>` at `opt`, whose niche
is the word at offset 24 (the `LookupMap` prefix's pointer):

```wat
block
  local.get 1  i32.load offset=24  br_if 0       ;; Some: skip the default
  local.get 1  call 156  unreachable             ;; None: Contract::default panics
end
local.get 0  local.get 1  i32.const 40  call 951  drop   ;; memcpy(out, opt, 40)
```

`f155_spec` is its `MFunSpec` when the word is nonzero, through
`MemCpy.f951_spec`: 744 `regular_op_cost`s (6 instructions, the call 1, the
activation of `memcpy` 10 and its 726, the `drop` 1); with the activation 9,
paid by the caller, the harness's 753 (`stateOrPanic`). The `None` path, a
trap through `Contract::default` (156), is `f155_spec_none`
(`UnwrapOrDefaultNone.lean`).
-/

namespace WNear.Binary.UnwrapOrDefault

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.U128From (memBytes_split memBytes_join)

theorem ofNat_ne_zero {bs : List UInt8} (h4 : bs.length = 4) (h : Memory.decodeLE bs ≠ 0) :
    UInt32.ofNat (Memory.decodeLE bs) ≠ 0 := by
  have hl := ResultExpect.decodeLE_lt bs
  rw [h4] at hl
  intro e
  apply h
  have := congrArg UInt32.toNat e
  simp at this hl
  omega

theorem activation_f951 (c : Nat) (a b e : UInt32) :
    activationGas c (entryLocals f951 [.i32 a, .i32 b, .i32 e]) = 10 * c := by
  simp [activationGas, entryLocals, f951, ValType.default]

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition: the arguments, the 40 bytes at `out` and the option at `opt`. -/
def pre (n : Nat) (out opt : UInt32) (ob sb : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 opt]⌝ ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ opt.toNat ] sb)

/-- The postcondition: no results, the option copied to `out`. -/
def post (n : Nat) (out opt : UInt32) (sb : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] sb ∗ n ↦[wms][ opt.toNat ] sb)

/-- `unwrap_or_default` (function 155 of `contract.wasm`) on a `Some` (the word at
offset 24 nonzero), calling `memcpy` (951, the function at `a951`). -/
theorem f155_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n a951 : Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[951]? = some a951) (ty951 : FuncType)
    (hty1 : ty951.params.length = 3) (hty2 : ty951.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (out opt : UInt32)
    (hout : out.toNat + 40 ≤ 2 ^ 32) (hopt : opt.toNat + 40 ≤ 2 ^ 32)
    (ob sb : List UInt8) (hob : ob.length = 40) (hsb : sb.length = 40)
    (hsome : Memory.decodeLE ((sb.drop 24).take 4) ≠ 0) :
    a951 ↪[wf] FuncInst.wasm ty951 inst f951 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f155 Cg (pre n out opt ob sb)
        (fun _ => 744 * cfg.regularOpCost) (post n out opt sb) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Ho, Hs⟩
  subst hargs
  have hne := ofNat_ne_zero (bs := (sb.drop 24).take 4) (by simp; omega) hsome
  icases memBytes_split n opt.toNat 24 sb (by omega) $$ Hs with ⟨Hs1, Hs2⟩
  icases memBytes_split n (opt.toNat + 24) 4 (sb.drop 24) (by simp; omega) $$ Hs2 with ⟨Hs2, Hs3⟩
  simp only [f155]
  mstep; mstep; mstep [Hs2]
  mstep_taken with exact hne
  mstep; mstep; mstep
  ihave Hs2 := memBytes_join n (opt.toNat + 24) 4 ((sb.drop 24).take 4)
    ((sb.drop 24).drop 4) (by simp; omega) $$ [Hs2 Hs3]
  · iframe Hs2 Hs3
  rw [List.take_append_drop]
  ihave Hs := memBytes_join n opt.toNat 24 (sb.take 24) (sb.drop 24)
    (by simp; omega) $$ [Hs1 Hs2]
  · iframe Hs1 Hs2
  rw [List.take_append_drop]
  mcall (MemCpy.f951_spec cfg lim (d + 1) ty951 hty2 inst mi n hn Cg out opt 40 ob sb
      (by simpa using hob) (by simpa using hsb) (by simp; omega) (by simp; omega))
    using [Ho Hs] with (simp [MemCpy.cost, activation_f951]; omega)
  · iunfold MemCpy.pre
    iframe Ho Hs
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho, Hs⟩
  subst hrs
  rw [show 738 * cfg.regularOpCost + R - (11 + MemCpy.cost 40) * cfg.regularOpCost =
    cfg.regularOpCost + R by simp [MemCpy.cost]; omega]
  mstep
  iframe Hc
  iunfold post
  iframe Ho Hs
  ipureintro; rfl

end Spec

end WNear.Binary.UnwrapOrDefault
