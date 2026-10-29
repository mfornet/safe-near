import Bridge.Functions.PanicDisplay
import Bridge.Functions.FmtWriteP
import Binary.Code.Part18

/-!
# `<&Arguments as Display>::fmt` (887): the panic's message

`<PanicInfo as Display>` (885) with `message = Some(args)` writes `'{}', ` on the argument
`(sp + 12, 202)`, `sp + 12` holding the address `a0` of the message's `Arguments`; 202 is 887:

```wat
;; 887 (x, f)                   sp -= 32
a0 := [x]
copy the 24 bytes a0 .. a0 + 24 to sp + 8 .. sp + 32   ;; three i64 loads/stores, the word at
                                                     ;; a0 + 12 (fmt's length) among them
r := core::fmt::write([f + 24], [f + 28], sp + 8)      ;; 872 on the copy
sp += 32
```

`f887_spec`: on the `Arguments` header at `a0` (`argsT` and the word at `a0 + 12`), 887 is the inner
872's specification on the copy (a premise, `P` to `Q`), at `cost887 + K`.
-/

namespace WNear.Binary.PanicMsg

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.PanicHook (stk4_word stk_split')
open WNear.Binary.FmtWriteT (argsT)

/-- 887's cost, the inner 872 excluded. -/
noncomputable def cost887 (cfg : WasmConfig) : Nat :=
  70 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0])

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The header of the `Arguments` at `ar` with its word at `ar + 12`. -/
def argsH (n : Nat) (ar pp argp kp k : UInt32) : IProp GF :=
  iprop(argsT n ar pp argp kp k ∗ ∃ w : UInt32, n ↦[i32][ ar.toNat + 12 ] w)

/-- Eight bytes as two words. -/
theorem memBytes_two (n a : Nat) (x y : UInt32) :
    (n ↦[wms][ a ] (bytes32 x ++ bytes32 y) : IProp GF) ⊣⊢ n ↦[i32][ a ] x ∗ n ↦[i32][ a + 4 ] y := by
  constructor
  · iintro H
    icases (memBytes_append (GF := GF) (H := NearState) n a (bytes32 x) (bytes32 y)).1 $$ H with ⟨H0, H4⟩
    iframe H0
    iapply memBytes_addr _ $$ H4; simp [bytes32]
  · iintro ⟨H0, H4⟩
    iapply (memBytes_append (GF := GF) (H := NearState) n a (bytes32 x) (bytes32 y)).2
    iframe H0
    iapply memBytes_addr _ $$ H4; simp [bytes32]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<&Arguments as Display>::fmt(x, f)`** (887) on `*x = a0`: 872 on a copy of the `Arguments`
at `sp - 32 + 8`. -/
theorem f887_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp x f data vtab a0 pp argp kp k : UInt32) (hsp : 32 ≤ sp.toNat) (ha0 : a0.toNat + 24 ≤ 2 ^ 32)
    (hf : f.toNat + 32 ≤ 2 ^ 32) (P Q : IProp GF) (K : Nat) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      MFunSpec cfg lim (d + 1) types[15]! inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 (sp - 32 + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗
          argsT n (sp - 32 + 8) pp argp kp k ∗ P))
        (fun _ => K)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗
          argsT n (sp - 32 + 8) pp argp kp k ∗ Q))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f887 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 32) 32 ∗
          (n ↦[i32][ x.toNat ] a0 ∗ n ↦[i32][ f.toNat + 24 ] data ∗ n ↦[i32][ f.toNat + 28 ] vtab) ∗
          argsH n a0 pp argp kp k ∗ P))
        (fun _ => cost887 cfg + K)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 32) 32 ∗
          (n ↦[i32][ x.toNat ] a0 ∗ n ↦[i32][ f.toNat + 24 ] data ∗ n ↦[i32][ f.toNat + 28 ] vtab) ∗
          argsH n a0 pp argp kp k ∗ Q)) := by
  iintro ⟨#Hi, #H872, #S872⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have ha872 := hm.funcs 872 (by decide)
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 32 + 8).toNat = sp.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have t15 : types[15]!.params.length = 3 := by rfl
  simp only [cost887]
  generalize hAC : activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) = AC
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, ⟨X0, F24, F28⟩, HA, HP⟩
  subst hargs
  iunfold argsH, argsT at HA
  icases HA with ⟨⟨A0, A4, A8, A16, A20⟩, %w, A12⟩
  ihave HA0 := (memBytes_two n a0.toNat pp kp).2 $$ [A0 A4]
  · iframe A0 A4
  ihave HA8 := (memBytes_two n (a0.toNat + 8) 0 w).2 $$ [A8 A12]
  · iframe A8; iapply memBytes_addr _ $$ A12; omega
  ihave HA16 := (memBytes_two n (a0.toNat + 16) argp k).2 $$ [A16 A20]
  · iframe A16; iapply memBytes_addr _ $$ A20; omega
  ihave Hs := stk_addr (show sp.toNat - 32 = (sp - 32).toNat by omega) $$ Hs
  icases stk_split n _ 8 24 $$ Hs with ⟨L0, Hs⟩
  icases stk_split n _ 8 16 $$ Hs with ⟨C8, Hs⟩
  icases stk_split n _ 8 8 $$ Hs with ⟨C16, C24⟩
  iunfold stk at C8 C16 C24
  icases C8 with ⟨%c8, %hc8, C8⟩
  icases C16 with ⟨%c16, %hc16, C16⟩
  icases C24 with ⟨%c24, %hc24, C24⟩
  ihave HA16 := memBytes_addr (show a0.toNat + 16 = (a0 + 16).toNat by simp [UInt32.toNat_add]; omega) $$ HA16
  ihave HA8 := memBytes_addr (show a0.toNat + 8 = (a0 + 8).toNat by simp [UInt32.toNat_add]; omega) $$ HA8
  ihave C24 := memBytes_addr (show (sp - 32).toNat + 8 + 8 + 8 = (sp - 32 + 8 + 16).toNat by
    simp [UInt32.toNat_add, h32]; omega) $$ C24
  ihave C16 := memBytes_addr (show (sp - 32).toNat + 8 + 8 = (sp - 32 + 8 + 8).toNat by
    simp [UInt32.toNat_add, h32]; omega) $$ C16
  ihave C8 := memBytes_addr (show (sp - 32).toNat + 8 = (sp - 32).toNat + 8 by rfl) $$ C8
  simp only [f887]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [F28]
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [X0]
  repeat mstep
  mstep [HA16]
  repeat mstep
  mstep [C24]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  mstep [HA8]
  repeat mstep
  mstep [C16]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  mstep [HA0]
  repeat mstep
  mstep [C8]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  icases (memBytes_two n _ pp kp).1 $$ C8 with ⟨C0, C4⟩
  icases (memBytes_two n _ 0 w).1 $$ C16 with ⟨Q8, Q12⟩
  icases (memBytes_two n _ argp k).1 $$ C24 with ⟨Q16, Q20⟩
  mcall S872 using [Hg C0 C4 Q8 Q16 Q20 HP]
  · iframe Hg HP
    iunfold argsT
    rw [h8]
    isplitl [C0]; · iapply memBytes_addr _ $$ C0; omega
    isplitl [C4]; · iapply memBytes_addr _ $$ C4; omega
    isplitl [Q8]; · iapply memBytes_addr _ $$ Q8; simp [UInt32.toNat_add, h32]; omega
    isplitl [Q16]; · iapply memBytes_addr _ $$ Q16; simp [UInt32.toNat_add, h32]; omega
    iapply memBytes_addr _ $$ Q20; simp [UInt32.toNat_add, h32]; omega
  icases HQ with ⟨%hrs, Hg, HA, HQ⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg X0 F24 F28 HQ
  isplitr; · ipureintro; rw [htype]; rfl
  iunfold argsT at HA
  icases HA with ⟨C0, C4, Q8, Q16, Q20⟩
  isplitl [L0 C0 C4 Q8 Q12 Q16 Q20]
  · ihave C8 := (memBytes_two n ((sp - 32).toNat + 8) pp kp).2 $$ [C0 C4]
    · rw [h8] at *
      isplitl [C0]; · iapply memBytes_addr _ $$ C0; omega
      iapply memBytes_addr _ $$ C4; omega
    ihave C16 := (memBytes_two n ((sp - 32).toNat + 16) 0 w).2 $$ [Q8 Q12]
    · isplitl [Q8]; · iapply memBytes_addr _ $$ Q8; simp [UInt32.toNat_add, h32]; omega
      iapply memBytes_addr _ $$ Q12; simp [UInt32.toNat_add, h32]; omega
    ihave C24 := (memBytes_two n ((sp - 32).toNat + 24) argp k).2 $$ [Q16 Q20]
    · isplitl [Q16]; · iapply memBytes_addr _ $$ Q16; simp [UInt32.toNat_add, h32]; omega
      iapply memBytes_addr _ $$ Q20; simp [UInt32.toNat_add, h32]; omega
    ihave C8 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C8
    ihave C16 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C16
    ihave C24 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C24
    ihave H := stk_join n ((sp - 32).toNat + 16) 8 8 $$ [C16 C24]
    · iframe C16; iapply stk_addr _ $$ C24; omega
    ihave H := stk_join n ((sp - 32).toNat + 8) 8 16 $$ [C8 H]
    · iframe C8; iapply stk_addr _ $$ H; omega
    iapply stk_addr (show (sp - 32).toNat = sp.toNat - 32 by omega)
    iapply stk_join n (sp - 32).toNat 8 24
    iframe L0
    iapply stk_addr _ $$ H; omega
  iunfold argsH, argsT
  ihave HA0 := (memBytes_two n a0.toNat pp kp).1 $$ HA0
  ihave HA8 := (memBytes_two n (a0 + 8).toNat 0 w).1 $$ HA8
  ihave HA16 := (memBytes_two n (a0 + 16).toNat argp k).1 $$ HA16
  icases HA0 with ⟨A0, A4⟩
  icases HA8 with ⟨A8, A12⟩
  icases HA16 with ⟨A16, A20⟩
  iframe A0 A4
  isplitl [A8 A16 A20]
  · isplitl [A8]; · iapply memBytes_addr _ $$ A8; simp [UInt32.toNat_add]; omega
    isplitl [A16]; · iapply memBytes_addr _ $$ A16; simp [UInt32.toNat_add]; omega
    iapply memBytes_addr _ $$ A20; simp [UInt32.toNat_add]; omega
  iexists w
  iapply memBytes_addr _ $$ A12; simp [UInt32.toNat_add]; omega


/-! ## The message's `write!(f, "'{}', ", args)` -/

open WNear.Binary.PanicDisplay (SinkW sinkW_piece qp qcp partA pptrA plenA)
open WNear.Binary.FmtWriteN (fmtrP)
open WNear.Binary.FmtWriteT (Hyp872T)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.AllocFresh (MFunSpec_frame)

/-- **The message's `Arguments` formatted on a writer**: 872 on a copy of their header at `sp + 8`
(`kp` pieces at `pp`, `k` arguments at `argp`, `fmt: None`) appends `text` to `W w`, at any depth
`d ≤ D`, with 160 bytes of stack below `sp`; `Xm` is what it reads besides the header. -/
def MsgW (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (gt : GlobalType) (data vtab idx : UInt32) (a : Nat) (W : List UInt8 → IProp GF) (B : Nat)
    (pp argp kp k : UInt32) (Xm : IProp GF) (text : List UInt8) (Km Cg : Nat) : IProp GF :=
  iprop(□ ∀ d : Nat, ∀ sp : UInt32, ∀ w : List UInt8,
    ⌜d ≤ D ∧ 160 ≤ sp.toNat ∧ sp.toNat + 32 ≤ 2 ^ 32 ∧ w.length + text.length ≤ B⌝ -∗
    MFunSpec cfg lim d types[15]! inst mi f872 Cg
      (fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 (sp + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        argsT n (sp + 8) pp argp kp k ∗ (stk n (sp.toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
          ta ↦[wt][ idx.toNat ] Ref.func a ∗ W w ∗ Xm)))
      (fun _ => Km)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        argsT n (sp + 8) pp argp kp k ∗ (stk n (sp.toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
          ta ↦[wt][ idx.toNat ] Ref.func a ∗ W (w ++ text) ∗ Xm))))

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (gt : GlobalType) (data vtab idx : UInt32) (a : Nat) (W : List UInt8 → IProp GF) (B : Nat)
    (pp argp kp k : UInt32) (Xm : IProp GF) (text : List UInt8) (Km Cg : Nat) :
    Persistent (MsgW cfg lim D inst mi n g ta gt data vtab idx a W B pp argp kp k Xm text Km Cg) := by
  unfold MsgW; infer_instance

/-- What the message's writes read: the pieces' bytes; the address `a0` of the `Arguments` at `y`,
their header and `Xm`. -/
def XM (n : Nat) (y a0 pp argp kp k : UInt32) (Xm : IProp GF) : IProp GF :=
  iprop((n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗
    (n ↦[i32][ y.toNat ] a0 ∗ argsH n a0 pp argp kp k ∗ Xm))

/-- The state of the message's writes, below 872's frame `s - 48`: 192 bytes (887's frame and the
inner 872's 160). -/
def StM (n : Nat) (s : UInt32) (W : List UInt8 → IProp GF) (w1 : List UInt8) (y a0 pp argp kp k : UInt32)
    (Xm : IProp GF) (text : List UInt8) (i : Nat) : IProp GF :=
  iprop(stk n ((s - 48).toNat - 192) 192 ∗ W (w1 ++ partA text i) ∗ XM n y a0 pp argp kp k Xm)

/-- The message's arrays: the pieces at 1070688, the argument `(y, 202)` at `argp0`, the table entry. -/
def MM (n ta : Nat) (A : Nat → Nat) (argp0 y : UInt32) : IProp GF :=
  iprop((n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 ] pptrA 0 ∗
      n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 + 4 ] plenA 0) ∗
    (n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 ] pptrA 1 ∗
      n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 + 4 ] plenA 1) ∗
    (n ↦[i32][ argp0.toNat + 8 * 0 ] y ∗ n ↦[i32][ argp0.toNat + 8 * 0 + 4 ] 202 ∗
      ta ↦[wt][ (202 : UInt32).toNat ] Ref.func (A 887)))

/-- The code the message's writes run (persistent). -/
def CM (cfg : WasmConfig) (lim : ExecLimits) (D DM inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (gt : GlobalType) (data vtab idx : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat)
    (pp argp kp k : UInt32) (Xm : IProp GF) (text : List UInt8) (Km Cg : Nat) : IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 887 ↪[wf] FuncInst.wasm types[13]! inst f887 ∗
    A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
    SinkW cfg lim D inst mi n g gt data code W B Kw Cg ∗
    MsgW cfg lim DM inst mi n g ta gt data vtab idx a W B pp argp kp k Xm text Km Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D DM inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (gt : GlobalType) (data vtab idx : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat)
    (pp argp kp k : UInt32) (Xm : IProp GF) (text : List UInt8) (Km Cg : Nat) :
    Persistent (CM cfg lim D DM inst mi A n g ta gt data vtab idx a code W B Kw pp argp kp k Xm text Km Cg) := by
  unfold CM; infer_instance

/-- The cost of the message's argument (887). -/
noncomputable def KBM (cfg : WasmConfig) (Km : Nat) : Nat :=
  activationGas cfg.regularOpCost (entryLocals f887 [.i32 0, .i32 0]) + (cost887 cfg + Km)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp872T` for the panic's message**: `"'"`, the `Arguments` through 887, `"', "`. -/
theorem hypA_msg (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D DM : Nat) (hdD : d + 2 ≤ D) (hdM : d + 2 ≤ DM)
    (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s data vtab idx argp0 y a0 pp argp kp k : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (Xm : IProp GF) (text : List UInt8) (Km : Nat)
    (w1 : List UInt8) (hs : 240 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (ha0 : a0.toNat + 24 ≤ 2 ^ 32)
    (hwB : w1.length + 4 + text.length ≤ B) :
    Hyp872T (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1070688 argp0 1 pptrA plenA
      (fun _ => y) (fun _ => 202) (fun _ => A 887) (fun _ => f887) a code
      (CM cfg lim D DM inst mi A n g ta gt data vtab idx a code W B Kw pp argp kp k Xm text Km Cg)
      (MM n ta A argp0 y) (StM n s W w1 y a0 pp argp kp k Xm text) Kw (cost887 cfg + Km) (KBM cfg Km) := by
  have hlt := s.toNat_lt
  have hs48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, hs48]; omega
  have hs80 : (s - 48 - 32).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, hs48] <;> omega
  have hj2 : ∀ j, j < (1 : UInt32).toNat + 1 → j = 0 ∨ j = 1 := fun j hj => by
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  have hj1 : ∀ j, j < (1 : UInt32).toNat → j = 0 := fun j hj => by
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases hj2 j hj with rfl | rfl
    · iintro H
      iunfold MM at H
      icases H with ⟨⟨P0, P4⟩, Q, R⟩
      iframe P0 P4
      iintro ⟨P0, P4⟩
      iunfold MM
      iframe P0 P4 Q R
    · iintro H
      iunfold MM at H
      icases H with ⟨P, ⟨Q0, Q4⟩, R⟩
      iframe Q0 Q4
      iintro ⟨Q0, Q4⟩
      iunfold MM
      iframe P Q0 Q4 R
  · intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MM at H
    icases H with ⟨P, Q, ⟨R0, R4, Rt⟩⟩
    iframe R0 R4 Rt
    iintro ⟨R0, R4, Rt⟩
    iunfold MM
    iframe P Q R0 R4 Rt
  · iintro #C
    iunfold CM at C
    icases C with ⟨#Hi, -, -, #Ha, -⟩
    iframe Hi Ha
  · intro j hj
    rcases hj2 j hj with rfl | rfl
    · simp only [pptrA, plenA, StM, Nat.reduceMul, ↓reduceIte]
      iintro #C
      iunfold CM at C
      icases C with ⟨-, -, -, -, #Sw, -⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1070684 1 192
        (w1 ++ partA text 0) (w1 ++ partA text 1) qp (XM n y a0 pp argp kp k Xm) (by omega) (by omega)
        (by omega) rfl (by decide) (by simp [partA]; omega) (by simp [partA])
        (by
          iintro H
          iunfold XM at H
          icases H with ⟨⟨P0, P1⟩, Q⟩
          isplitl [P0]
          · iapply memBytes_addr _ $$ P0; rfl
          iintro P0
          iunfold XM
          iframe P1 Q
          iapply memBytes_addr _ $$ P0; rfl)
      iexact Sw
    · simp only [pptrA, plenA, StM, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CM at C
      icases C with ⟨-, -, -, -, #Sw, -⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1070685 3 192
        (w1 ++ partA text 2) (w1 ++ partA text 3) qcp (XM n y a0 pp argp kp k Xm) (by omega) (by omega)
        (by omega) rfl (by decide) (by simp [partA, qp]; omega) (by simp [partA])
        (by
          iintro H
          iunfold XM at H
          icases H with ⟨⟨P0, P1⟩, Q⟩
          isplitl [P1]
          · iapply memBytes_addr _ $$ P1; rfl
          iintro P1
          iunfold XM
          iframe P0 Q
          iapply memBytes_addr _ $$ P1; rfl)
      iexact Sw
  · intro j hj
    rcases hj1 j hj
    iintro #C
    iunfold CM at C
    icases C with ⟨-, #H887, -⟩
    iexact H887
  · -- the argument: the `Arguments` through 887
    intro j hj
    rcases hj1 j hj
    simp only [StM, Nat.reduceMul, Nat.reduceAdd]
    iintro #C
    iunfold CM at C
    icases C with ⟨#Hi, -, #H872, -, -, #Mw⟩
    iunfold MsgW at Mw
    ihave #S0 := Mw $$ %(d + 2) %(s - 48 - 32) %(w1 ++ partA text 1)
      %⟨by omega, by omega, by omega, by simp [partA, qp]; omega⟩
    ihave #S := f887_spec cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 48) y
      (s - 48 + 8) data vtab a0 pp argp kp k (by omega) ha0 (by omega)
      iprop(stk n ((s - 48 - 32).toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
        ta ↦[wt][ idx.toNat ] Ref.func a ∗ W (w1 ++ partA text 1) ∗ Xm)
      iprop(stk n ((s - 48 - 32).toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
        ta ↦[wt][ idx.toNat ] Ref.func a ∗ W ((w1 ++ partA text 1) ++ text) ∗ Xm) Km $$ [Hi H872 S0]
    · iframe Hi H872 S0
    iapply (MFunSpec_frame (GF := GF) (Fr := iprop((n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗
        n ↦[i32][ (s - 48 + 8).toNat ] 0 ∗ n ↦[i32][ (s - 48 + 8).toNat + 8 ] 0 ∗
        n ↦[i32][ (s - 48 + 8).toNat + 16 ] 0))
      (fun args => by
        iintro ⟨%ha, Hg, HF, Hs, HW, HX⟩
        iunfold fmtrP, fmtr at HF
        icases HF with ⟨⟨F0, F8, F24, F28, V12, Ht⟩, F16⟩
        iunfold XM at HX
        icases HX with ⟨P, Y0, HA, Hm⟩
        icases stkSp 160 32 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
        iframe P F0 F8 F16 Hg Y0 F24 F28 HA V12 Ht HW Hm
        isplitr
        · ipureintro; exact ha
        isplitl [Hs2]
        · iapply stkA (by omega) $$ Hs2
        iapply stkA (by omega) $$ Hs1)
      (fun args rs => by
        iintro ⟨⟨P, F0, F8, F16⟩, %hrs, Hg, Hs2, ⟨Y0, F24, F28⟩, HA, Hs1, V12, Ht, HW, Hm⟩
        iframe Hg
        isplitr
        · ipureintro; exact hrs
        isplitl [F0 F8 F16 F24 F28 V12 Ht]
        · iunfold fmtrP, fmtr; iframe F0 F8 F16 F24 F28 V12 Ht
        isplitl [Hs1 Hs2]
        · iapply stkJ (a := (s - 48).toNat - 192) (b := (s - 48).toNat - 32) (k1 := 160) (k2 := 32) (by omega)
            (by omega)
          isplitl [Hs1]
          · iapply stkA (by omega) $$ Hs1
          iexact Hs2
        isplitl [HW]
        · simp only [partA, List.append_assoc]; iexact HW
        iunfold XM
        iframe P Y0 HA Hm)) $$ S
  · intro j hj
    rcases hj1 j hj
    unfold KBM; omega

end Spec

end WNear.Binary.PanicMsg
