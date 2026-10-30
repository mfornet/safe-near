import Bridge.Functions.SerdeIgnValue
import Bridge.Functions.SerdeIgnoreString

/-! # Successful shallow ignored values with arbitrary string escapes -/

namespace WNear.Binary.SerdeIgnValueEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeIgnValue (StringHyp scratchTables)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Code, hex bytes and the lower half of 650's successful escape frame. -/
def extra (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (sp : UInt32) : IProp GF :=
  iprop(SerdeIgnoreEscape.code inst mi A ∗ A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ∗
    n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ stk n (sp.toNat - 160) 64)

/-- The complete successful 650 contract supplies 81's general string boundary. -/
theorem stringHyp (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (gt : GlobalType) (sp de ptr : UInt32) (bs : List UInt8)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hsp : 160 ≤ sp.toNat) :
    StringHyp (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr bs (extra inst mi A n sp) := by
  intro q s rest hq hmodel
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have base := SerdeIgnoreString.f650_model (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 32) de ptr bs rest s q hlen hptr hde (by rw [h32]; omega) hq hmodel
  iunfold MFunSpec
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, SB, Hrd, He, Hextra⟩
  iunfold extra at Hextra
  icases Hextra with ⟨#HC, #F652, Hhex, Lo⟩
  ihave #S := base $$ [HC F652]
  · iframe HC F652
  iunfold MFunSpec at S
  ihave H128 := stk_join n (sp.toNat - 160) 64 64 $$ [Lo SB]
  · rw [show sp.toNat - 160 + 64 = sp.toNat - 96 by omega]
    iframe Lo SB
  ihave H128 := stk_addr (show sp.toNat - 160 = (sp - 32).toNat - 128 by rw [h32]; omega) $$ H128
  iapply mwpInvoke_wand
  isplitl [Hg H128 Hrd He Hhex Hc]
  · iapply S $$ %args %R [Hg H128 Hrd He Hhex] Hc
    dsimp only
    iframe Hg H128 Hrd He Hhex
    ipureintro; exact ha
  isplit
  · iintro %rs ⟨Hc, %hrs, Hg, H128, Hrd, He, Hhex⟩
    dsimp only
    ihave H128 := stk_addr (show (sp - 32).toNat - 128 = sp.toNat - 160 by rw [h32]; omega) $$ H128
    icases stk_split n (sp.toNat - 160) 64 64 $$ H128 with ⟨Lo, SB⟩
    rw [show sp.toNat - 160 + 64 = sp.toNat - 96 by omega]
    iframe Hc Hg SB Hrd He
    isplitr
    · ipureintro; exact hrs
    iunfold extra
    iframe HC F652 Hhex Lo
  · iintro Htrap; iexact Htrap

/-- Shallow ignored values with arbitrary string escapes preserve reusable scratch and the complete 160-byte frame. -/
theorem f81_shallow_escaped (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr ptrS capS : UInt32) (bs : List UInt8) (j : Nat) (rest : List UInt8)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 160 ≤ sp.toNat) (hj : j ≤ bs.length)
    (hmodel : WNear.IgnoreShallow.ign1 (bs.drop j) = some rest) :
    SerdeIgnValue.code81 inst mi A ∗ SerdeIgnoreEscape.code inst mi A ∗
      A 652 ↪[wf] FuncInst.wasm types[32]! inst f652 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f81 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
          rd n de ptr bs j ∗ scratchTables n de ptrS capS ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (166 + 470 * (bs.length - rest.length - j)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
          rd n de ptr bs (bs.length - rest.length) ∗ scratchTables n de ptrS capS ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable)) := by
  have reader := stringHyp (GF := GF) cfg lim d inst mi A n g ta Cg hm hd gt sp de ptr bs hlen hptr (by omega) hsp
  have core := SerdeIgnValue.f81_shallow_core (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt
    sp de ptr ptrS capS bs j rest (by omega) hptr hde (by omega) hj (extra inst mi A n sp) reader hmodel
  iintro ⟨#C81, #HC, #F652⟩
  ihave #S := core $$ C81
  iunfold MFunSpec at S
  iunfold MFunSpec
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, H160, Hrd, Htables, Hhex⟩
  icases stk_split n (sp.toNat - 160) 64 96 $$ H160 with ⟨Lo, H96⟩
  rw [show sp.toNat - 160 + 64 = sp.toNat - 96 by omega]
  iapply mwpInvoke_wand
  isplitl [Hg H96 Hrd Htables Hhex Lo Hc]
  · iapply S $$ %args %R [Hg H96 Hrd Htables Hhex Lo] Hc
    dsimp only
    iframe Hg H96 Hrd Htables
    isplitr
    · ipureintro; exact ha
    iunfold extra
    iframe HC F652 Hhex Lo
  isplit
  · iintro %rs ⟨Hc, %hrs, Hg, H96, Hrd, Htables, Hextra⟩
    dsimp only
    iunfold extra at Hextra
    icases Hextra with ⟨_, _, Hhex, Lo⟩
    iframe Hc Hg Hrd Htables Hhex
    isplitr
    · ipureintro; exact hrs
    iapply stk_join n (sp.toNat - 160) 64 96
    rw [show sp.toNat - 160 + 64 = sp.toNat - 96 by omega]
    iframe Lo H96
  · iintro Htrap; iexact Htrap

end Proof
end WNear.Binary.SerdeIgnValueEsc
