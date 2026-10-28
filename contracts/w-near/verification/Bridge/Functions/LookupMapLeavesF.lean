import Bridge.Functions.LookupMapLeaves
import Bridge.Functions.ReadRegisterF

/-!
# `env::read_register(EVICTED_REGISTER)` (550) on `heapInv … F`, any `F ≥ 1`

`LookupMapLeaves.f550_spec` with `ReadRegisterF.f523_specF` in place of `f523_spec`: in `new`,
`LookupMap::remove` reads the removed value after several frees, on a free list of `F ≥ 2` cells.
-/

namespace WNear.Binary.LookupMapLeavesF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.ReadRegister (rrCode RegOk)
open WNear.Binary.ReadRegisterF (rrCodeF pre523F post523F cost523F f523_specF)
open WNear.Binary.StorageWrite (evictedRegister)
open WNear.Binary.VecWithCap (okG)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 550 on any free list (persistent): `rrCodeF` and 523. -/
def rr550CodeF (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCodeF e inst mi A n maxP mx ∗ A 523 ↪[wf] FuncInst.wasm types[5]! inst f523)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (rr550CodeF (GF := GF) e inst mi A n maxP mx) := by
  unfold rr550CodeF; infer_instance

def pre550F (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ pre523F n g ta A gt s out evictedRegister idx maxP len live F ob h
    [.i32 out, .i64 evictedRegister])

set_option maxRecDepth 100000 in
/-- **`env::read_register(EVICTED_REGISTER)`** (550) on `heapInv … F`, `okG F`: `f523_specF` at
`u64::MAX - 1`, 13 `regular_op_cost`s more. -/
theorem f550_specF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (hok : RegOk maxP len (h.registers evictedRegister.toNat)) :
    rr550CodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f550 Cg
        (pre550F n g ta A gt s out idx maxP len live F ob h)
        (fun _ => 13 * cfg.regularOpCost + cost523F cfg F h evictedRegister)
        (post523F n g ta A gt s out evictedRegister idx maxP len live F h) := by
  iintro #Hk
  iunfold rr550CodeF at Hk
  icases Hk with ⟨#Hrr, #F523⟩
  ihave #S523 := f523_specF (GF := GF) cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt s
    out hs hal hout evictedRegister idx maxP len live F hF ob hob h hok $$ Hrr
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold rrCodeF, rrCode, ReadRegister.ifaceCodeR, Interface.ifaceCode at Hrr
    icases Hrr with ⟨⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩, -⟩, -⟩
    iexact Hi
  have ha523 := hm.funcs 523 (by decide)
  have t5 : types[5]!.params.length = 2 := by rfl
  generalize hK : cost523F cfg F h evictedRegister = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre550F at HP
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f550]
  mstep; mstep
  mcall S523 using [HP] with (rw [hK]; mstep_norm_full; omega)
  · rw [show (18446744073709551614 : UInt64) = evictedRegister from rfl]; iexact HP
  iunfold post523F at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post523F
  iframe HQ
  ipureintro; simp [htype]

end Spec

end WNear.Binary.LookupMapLeavesF
