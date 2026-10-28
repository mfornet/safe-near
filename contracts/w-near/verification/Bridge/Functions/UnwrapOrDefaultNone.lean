import Bridge.Functions.UnwrapOrDefault
import Bridge.Functions.PanicStr

/-!
# `Option<Contract>::unwrap_or_default` (function 155), the `None` path

```wat
block
  local.get 1  i32.load offset=24  br_if 0       ;; the niche is 0: fall through
  local.get 1  call 156  unreachable             ;; Contract::default panics
end
```

`f155_spec_none`: when the word at offset 24 of the option is 0, `Contract::default` (156,
`PanicStr.f156_spec`) traps with the host panicked with `"The contract is not initialized"`.
-/

namespace WNear.Binary.UnwrapOrDefault

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.PanicStr (panicCode panicked notInit defaultPre)

section None

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The arguments, the zero niche at `opt + 24`, and what `Contract::default` needs
(`defaultPre`, `self = opt`). -/
def preNone (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp out opt c0 c4 w0 w4 w8 w12 : UInt32)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 opt]⌝ ∗ n ↦[i32][ opt.toNat + 24 ] 0 ∗
    defaultPre n g ta A gi sp opt c0 c4 w0 w4 w8 w12 h [.i32 opt])

/-- **`unwrap_or_default` on `None`** (function 155 of `contract.wasm`, the word at offset 24
zero): `Contract::default` (156) traps, the host panicked with `"The contract is not
initialized"`. -/
theorem f155_spec_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (out opt c0 c4 w0 w4 w8 w12 : UInt32) (h : NearState)
    (hfit : LogFits h 31) (hov : h.extCosts.cost "read_memory_byte" * 31 < 2 ^ 64) :
    A 156 ↪[wf] FuncInst.wasm types[0]! inst f156 ∗ A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗
      A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ ifaceCode e inst mi A n mx ∗ panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f155 Cg
        (preNone n g ta A gi sp out opt c0 c4 w0 w4 w8 w12 h)
        (fun _ => 221 * cfg.regularOpCost + panicUtf8Use h 31) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h notInit) := by
  iintro ⟨#F156, #F521, #F448, #Hcode, #Hpc⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at Hpc
    icases Hpc with ⟨-, -, #Hi⟩
    iexact Hi
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold preNone at HP
  icases HP with ⟨%hargs, H24, HD⟩
  subst hargs
  have hn := hm.mem
  simp only [f155]
  mstep; mstep; mstep [H24]
  mstep_not_taken
  mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 156) (a := A 156) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f156) [.i32 opt])
  isplitr
  · iapply (PanicStr.f156_spec cfg lim (d + 1) types[0]! inst mi e A n g ta mx hm (by omega) Cg gi sp hgi
      hsp hal opt c0 c4 w0 w4 w8 w12 h hfit hov)
    iframe F521 F448 Hcode Hpc
  isplitr
  · iexact F156
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, hm.funcs 156 (by decide), rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [HD]
  · iexact HD
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT

end None

end WNear.Binary.UnwrapOrDefault
