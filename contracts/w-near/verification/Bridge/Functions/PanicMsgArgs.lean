import Bridge.Functions.PanicDisplayMsg

/-!
# The two messages of `core`'s panics, on a sink

`PanicMsg.MsgW` for the two `Arguments` the panic entries build, on any `SinkW`:

* `msgW_expect`: `expect_failed`'s `format_args!("{}", msg)`: the piece `""` at 1070628 and the
  argument `(x, 195)` (880, `<&str as Display>`), `x` holding the `&str` `(m, l)`: 872 with one
  piece and one argument (`FmtWriteN.f872_gen` on `hypX`), the text `msg`;
* `msgW_str`: `core::panicking::panic`'s `Arguments { pieces: [(m, l)], args: [] }`: 872 with one
  piece and no argument (`FmtWriteP.f872_p1`), the text `msg`.
-/

namespace WNear.Binary.PanicMsg

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.PanicDisplay (SinkW sinkW_piece arg880 cost880)
open WNear.Binary.FmtWriteN (fmtrP Hyp872 argsN costN f872_gen)
open WNear.Binary.FmtWriteT (argsT)
open WNear.Binary.FmtWriteP (costP f872_p1)
open WNear.Binary.AllocFresh (MFunSpec_frame)

/-- The text after the `i`-th write of `format_args!("{}", msg)`. -/
def partX (msg : List UInt8) : Nat → List UInt8
  | 0 => []
  | 1 => []
  | _ => msg

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `core::panicking::panic`: one piece -/

/-- What `panic`'s message reads besides its header: the piece `(m, l)` at `pa` and its bytes. -/
def XmS (n : Nat) (pa m l : UInt32) (msg : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ pa.toNat ] m ∗ n ↦[i32][ pa.toNat + 4 ] l ∗ n ↦[wms][ m.toNat ] msg)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`MsgW` for `Arguments { pieces: [(m, l)] at pa, fmt: None, args: [] }`**: the text `msg`. -/
theorem msgW_str (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hD : D + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (data vtab idx pa m l : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF)
    (B Kw : Nat) (msg : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hpa : pa.toNat + 8 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim (D + 1) inst mi n g gt data code W B Kw Cg ⊢
      MsgW (GF := GF) cfg lim D inst mi n g ta gt data vtab idx a W B pa 1067136 1 0 (PanicDisplayMsg.XmT ta A (XmS n pa m l msg)) msg
        (costP cfg code Kw) Cg := by
  iintro ⟨#Hi, #Ha, #Sw⟩
  iunfold MsgW
  imodintro
  iintro %d %sp %w %⟨hdD, hsp, hsp2, hwB⟩
  have hlt := sp.toNat_lt
  have hs48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp + 8).toNat = sp.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have S := f872_p1 (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm (by omega) Cg gt sp data vtab
    (sp + 8) pa 1067136 idx m l (by omega) (by omega) hpa a code
    iprop(inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim (D + 1) inst mi n g gt data code W B Kw Cg)
    iprop(stk n ((sp - 48).toNat - 112) 112 ∗ W w ∗ n ↦[wms][ m.toNat ] msg)
    iprop(stk n ((sp - 48).toNat - 112) 112 ∗ W (w ++ msg) ∗ n ↦[wms][ m.toNat ] msg) Kw
    (by iintro ⟨#Hi, #Ha, -⟩; iframe Hi Ha)
    (by
      iintro ⟨-, -, #Sw⟩
      iapply sinkW_piece cfg lim (D + 1) (d + 1) inst mi n g gt data code W B Kw Cg (sp - 48) m l 112
        w (w ++ msg) msg iprop(n ↦[wms][ m.toNat ] msg) (by omega) le_rfl (by omega) hmsg hml
        (by omega) rfl (by iintro H; iframe H; iintro H; iexact H)
      iexact Sw)
  have S' := S.trans (MFunSpec_frame (GF := GF) (Fr := iprop(ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880)))
    (P' := fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 (sp + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      argsT n (sp + 8) pa 1067136 1 0 ∗ (stk n (sp.toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
        ta ↦[wt][ idx.toNat ] Ref.func a ∗ W w ∗ PanicDisplayMsg.XmT ta A (XmS n pa m l msg))))
    (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      argsT n (sp + 8) pa 1067136 1 0 ∗ (stk n (sp.toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
        ta ↦[wt][ idx.toNat ] Ref.func a ∗ W (w ++ msg) ∗ PanicDisplayMsg.XmT ta A (XmS n pa m l msg))))
    (fun args => by
      iintro ⟨%ha, Hg, HA, Hs, V12, Ht, HW, HX⟩
      iunfold PanicDisplayMsg.XmT, XmS at HX
      icases HX with ⟨T195, X0, X4, Hm⟩
      icases stkSp 112 48 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      isplitr [T195]
      · iframe Hg HA V12 Ht HW Hm X0 X4
        isplitr; · ipureintro; exact ha
        isplitl [Hs2]; · iapply stkA (by omega) $$ Hs2
        iapply stkA (by omega) $$ Hs1
      · iexact T195)
    (fun args rs => by
      iintro ⟨T195, %hrs, Hg, Hs2, HA, ⟨X0, X4⟩, V12, Ht, Hs1, HW, Hm⟩
      iframe Hg HA V12 Ht HW
      isplitr; · ipureintro; exact hrs
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - 160) (b := sp.toNat - 48) (k1 := 112) (k2 := 48) (by omega) rfl
        isplitl [Hs1]; · iapply stkA (by omega) $$ Hs1
        iexact Hs2
      iunfold PanicDisplayMsg.XmT, XmS; iframe T195 X0 X4 Hm))
  iapply S'
  iframe Hi Ha Sw

/-! ## `expect_failed`: `format_args!("{}", msg)` -/

/-- The arrays of `format_args!("{}", msg)`: the piece `(e0, 0)` at 1070628, the argument
`(x, 195)` at `argp`, the table entry 195. -/
def MX (n ta : Nat) (A : Nat → Nat) (e0 argp x : UInt32) : IProp GF :=
  iprop((n ↦[i32][ (1070628 : UInt32).toNat + 8 * 0 ] e0 ∗ n ↦[i32][ (1070628 : UInt32).toNat + 8 * 0 + 4 ] 0) ∗
    (n ↦[i32][ argp.toNat + 8 * 0 ] x ∗ n ↦[i32][ argp.toNat + 8 * 0 + 4 ] 195 ∗
      ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880)))

/-- `MX` without the table entry. -/
def MX0 (n : Nat) (e0 argp x : UInt32) : IProp GF :=
  iprop((n ↦[i32][ (1070628 : UInt32).toNat + 8 * 0 ] e0 ∗ n ↦[i32][ (1070628 : UInt32).toNat + 8 * 0 + 4 ] 0) ∗
    (n ↦[i32][ argp.toNat + 8 * 0 ] x ∗ n ↦[i32][ argp.toNat + 8 * 0 + 4 ] 195))

/-- The `&str` `(m, l)` at `x` and its bytes. -/
def XS (n : Nat) (x m l : UInt32) (msg : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ x.toNat ] m ∗ n ↦[i32][ x.toNat + 4 ] l ∗ n ↦[wms][ m.toNat ] msg)

/-- What `expect_failed`'s message reads besides its header. -/
def XmX (n ta : Nat) (A : Nat → Nat) (e0 argp x m l : UInt32) (msg : List UInt8) : IProp GF :=
  iprop(MX0 n e0 argp x ∗ XS n x m l msg)

/-- The state of `format_args!("{}", msg)`'s writes below 872's frame `s - 48`. -/
def StX (n : Nat) (s : UInt32) (W : List UInt8 → IProp GF) (w : List UInt8) (x m l : UInt32)
    (msg : List UInt8) (i : Nat) : IProp GF :=
  iprop(stk n ((s - 48).toNat - 112) 112 ∗ W (w ++ partX msg i) ∗ XS n x m l msg)

/-- The code `format_args!("{}", msg)`'s writes run (persistent). -/
def CX (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
    A 880 ↪[wf] FuncInst.wasm types[13]! inst f880 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
    SinkW cfg lim D inst mi n g gt data code W B Kw Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (CX cfg lim D inst mi A n g gt data a code W B Kw Cg) := by
  unfold CX; infer_instance

noncomputable def KBX (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  activationGas cfg.regularOpCost (entryLocals f880 [.i32 0, .i32 0]) + cost880 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp872` for `format_args!("{}", msg)`**: `""`, then the `&str` through 880. -/
theorem hypX (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 3 ≤ D) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s data vtab idx argp x m l e0 : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (w msg : List UInt8) (hs : 160 ≤ s.toNat)
    (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hwB : w.length + msg.length ≤ B) :
    Hyp872 (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1070628 argp 1 (fun _ => e0)
      (fun _ => 0) (fun _ => x) (fun _ => 195) (fun _ => A 880) (fun _ => f880) a code
      (CX cfg lim D inst mi A n g gt data a code W B Kw Cg) (MX n ta A e0 argp x)
      (StX n s W w x m l msg) Kw (cost880 cfg code Kw) (KBX cfg code Kw) := by
  have hlt := s.toNat_lt
  have hs48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, hs48]; omega
  have hj1 : ∀ j, j < (1 : UInt32).toNat → j = 0 := fun j hj => by
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MX at H
    icases H with ⟨⟨P0, P4⟩, Q⟩
    iframe P0 P4
    iintro ⟨P0, P4⟩
    iunfold MX
    iframe P0 P4 Q
  · intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MX at H
    icases H with ⟨P, ⟨Q0, Q4, Qt⟩⟩
    iframe Q0 Q4 Qt
    iintro ⟨Q0, Q4, Qt⟩
    iunfold MX
    iframe P Q0 Q4 Qt
  · iintro #C
    iunfold CX at C
    icases C with ⟨#Hi, -, -, #Ha, -⟩
    iframe Hi Ha
  · intro j hj
    rcases hj1 j hj
    simp only [StX, Nat.reduceMul]
    iintro #C
    iunfold CX at C
    icases C with ⟨-, -, -, -, #Sw⟩
    iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) e0 0 112
      (w ++ partX msg 0) (w ++ partX msg 1) [] _ (by omega) le_rfl (by omega) rfl (by have := e0.toNat_lt; simp; omega)
      (by simp [partX]; omega) (by simp [partX])
      (by
        iintro H
        iframe H
        isplitr
        · iapply FmtString.memBytes_nil
        iintro -; iempintro)
    iexact Sw
  · intro j hj
    rcases hj1 j hj
    iintro #C
    iunfold CX at C
    icases C with ⟨-, -, #H880, -⟩
    iexact H880
  · intro j hj
    rcases hj1 j hj
    simp only [StX, Nat.reduceMul, Nat.reduceAdd]
    iintro #C
    iunfold CX at C
    icases C with ⟨#Hi, #H856, -, #Ha, #Sw⟩
    simp only [partX, List.append_nil]
    iapply arg880 cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48) (s - 48 + 8)
      data vtab idx x m l (by omega) 112 le_rfl (by omega) a code W B Kw w (w ++ msg) msg hmsg hml
      (by omega) rfl (XS n x m l msg)
      (by
        iintro H
        iunfold XS at H
        icases H with ⟨X0, X4, Hm⟩
        iframe X0 X4 Hm
        iintro X0 X4 Hm
        iunfold XS
        iframe X0 X4 Hm)
    iframe Hi H856 Ha Sw
  · intro j hj
    rcases hj1 j hj
    unfold KBX; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`MsgW` for `format_args!("{}", msg)`** (the piece `""` at 1070628, the argument `(x, 195)` at
`argp`): the text `msg`. -/
theorem msgW_expect (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hD : D + 4 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (data vtab idx argp x m l e0 : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF)
    (B Kw : Nat) (msg : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hargp : argp.toNat + 16 ≤ 2 ^ 32) :
    CX cfg lim (D + 3) inst mi A n g gt data a code W B Kw Cg ⊢
      MsgW (GF := GF) cfg lim D inst mi n g ta gt data vtab idx a W B 1070628 argp 1 1
        (PanicDisplayMsg.XmT ta A (XmX n ta A e0 argp x m l msg)) msg (costN cfg code Kw (KBX cfg code Kw) 1) Cg := by
  iintro #C
  iunfold MsgW
  imodintro
  iintro %d %sp %w %⟨hdD, hsp, hsp2, hwB⟩
  have hlt := sp.toNat_lt
  have hs48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp + 8).toNat = sp.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have S := f872_gen (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm (by omega) Cg gt sp data vtab
    (sp + 8) 1070628 argp idx 1 (by decide) (by omega) (by omega) (by simp) (by simp; omega)
    (fun _ => e0) (fun _ => 0) (fun _ => x) (fun _ => 195) (fun _ => A 880) (fun _ => f880) a code
    (CX cfg lim (D + 3) inst mi A n g gt data a code W B Kw Cg) (MX n ta A e0 argp x)
    (StX n sp W w x m l msg) Kw (cost880 cfg code Kw) (KBX cfg code Kw)
    (hypX cfg lim d inst mi A n g ta hm (D + 3) (by omega) (by omega) Cg gt sp data vtab idx argp x m l e0 a
      code W B Kw w msg (by omega) (by omega) hmsg hml hwB)
  rw [show 2 * (1 : UInt32).toNat = 2 from rfl, show (1 : UInt32).toNat = 1 from rfl] at S
  have S' := S.trans (MFunSpec_frame (GF := GF) (Fr := iprop(emp))
    (P' := fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 (sp + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      argsT n (sp + 8) 1070628 argp 1 1 ∗ (stk n (sp.toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
        ta ↦[wt][ idx.toNat ] Ref.func a ∗ W w ∗ PanicDisplayMsg.XmT ta A (XmX n ta A e0 argp x m l msg))))
    (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      argsT n (sp + 8) 1070628 argp 1 1 ∗ (stk n (sp.toNat - 160) 160 ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗
        ta ↦[wt][ idx.toNat ] Ref.func a ∗ W (w ++ msg) ∗ PanicDisplayMsg.XmT ta A (XmX n ta A e0 argp x m l msg))))
    (fun args => by
      iintro ⟨%ha, Hg, HA, Hs, V12, Ht, HW, HX⟩
      iunfold PanicDisplayMsg.XmT, XmX, MX0 at HX
      icases HX with ⟨T195, ⟨HP0, HA0, HA4⟩, HS⟩
      ihave HM : MX n ta A e0 argp x $$ [HP0 HA0 HA4 T195]
      · iunfold MX; iframe HP0 HA0 HA4 T195
      icases stkSp 112 48 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      isplitl
      · iframe Hg V12 Ht HM
        isplitr; · ipureintro; exact ha
        isplitl [Hs2]; · iapply stkA (by omega) $$ Hs2
        isplitl [HA]; · iunfold argsT at HA; iunfold argsN; iexact HA
        iunfold StX
        isplitl [Hs1]; · iapply stkA (by omega) $$ Hs1
        simp only [partX, List.append_nil]
        iframe HW HS
      · iempintro)
    (fun args rs => by
      iintro ⟨-, %hrs, Hg, Hs2, HA, HM, V12, Ht, HSt⟩
      iunfold StX at HSt
      icases HSt with ⟨Hs1, HW, HS⟩
      iframe Hg V12 Ht
      isplitr; · ipureintro; exact hrs
      isplitl [HA]; · iunfold argsN at HA; iunfold argsT; iexact HA
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - 160) (b := sp.toNat - 48) (k1 := 112) (k2 := 48) (by omega) rfl
        isplitl [Hs1]; · iapply stkA (by omega) $$ Hs1
        iexact Hs2
      isplitl [HW]; · simp only [partX]; iexact HW
      iunfold MX at HM
      icases HM with ⟨HP0, HA0, HA4, T195⟩
      iunfold PanicDisplayMsg.XmT, XmX, MX0; iframe T195 HP0 HA0 HA4 HS))
  iapply S' $$ C

end Spec

end WNear.Binary.PanicMsg
