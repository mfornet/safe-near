import Bridge.Functions.SerdeStructObjValueState
import Bridge.Functions.SerdeFromTrait

/-!
# The actual object struct path with concrete key and account-id readers

The remaining reader hypothesis is the ignored-value call. Quantitative
hypotheses describe only room, gas and reachable heap/scratch bounds; the actual
key and account-id reader behavior is supplied by their proved contracts.
-/

namespace WNear.Binary.SerdeStructObjModelState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjKeyState (Bounds member KeyConditions)
open WNear.Binary.SerdeStructObjValueState (ValueConditions)
open WNear.SerdeStructModel

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Code used by the loop and its concrete successful key and value calls. -/
def code (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A ∗
    SerdeAccountId.code169 n maxP inst mi A ∗
    A 205 ↪[wf] FuncInst.wasm types[14]! inst f205 ∗ A 201 ↪[wf] FuncInst.wasm types[32]! inst f201 ∗
    A 193 ↪[wf] FuncInst.wasm types[11]! inst f193 ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
    A 90 ↪[wf] FuncInst.wasm types[32]! inst f90 ∗ A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗
    A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ A 77 ↪[wf] FuncInst.wasm types[0]! inst f77)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code (GF := GF) n maxP inst mi A) := by
  unfold code; infer_instance

/-- Project the concrete key-reader code. -/
theorem code_keys (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    code (GF := GF) n maxP inst mi A ⊢ SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A := by
  iintro #H
  iunfold code at H
  icases H with ⟨#C193, #C646, -⟩
  iframe C193 C646

/-- Project the concrete map-value code. -/
theorem code_values (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    code (GF := GF) n maxP inst mi A ⊢ SerdeEnds.endCode n maxP inst mi A ∗
      A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗ A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
      SerdeAccountId.code169 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A := by
  iintro #H
  iunfold code at H
  icases H with ⟨#C193, #C646, #C169, -, -, -, #F89, -, -, #F169, -⟩
  iunfold SerdeNextKey.code193 at C193
  icases C193 with ⟨#Cend, -⟩
  iframe Cend F89 F169 C169 C646

set_option maxRecDepth 100000 in
/-- Model-accepted object prefixes through the real 228 loop, with only ignored-reader and pure-bound obligations left. -/
theorem f228_obj_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i maxP : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : Bounds) (K646 K169 K81 : Nat → Nat)
    (ign : List UInt8 → Option (Unit × List UInt8)) (hign : Agrees ign valueSkip)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : KeyConditions cfg maxP bs B K646) (hkeysSaved : KeyConditions cfg maxP bs Bsaved K646)
    (hvalues : ValueConditions cfg maxP bs B Bsaved K169)
    (hmono : ∀ i j hl F cap, i ≤ j → B i hl F cap → B j hl F cap)
    (hmonoSaved : ∀ i j hl F cap, i ≤ j → Bsaved i hl F cap → Bsaved j hl F cap)
    (hignore : SerdeStructObjState.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs ign K81
      (member n maxP ta (A 578) idx de live B Bsaved) iprop(code n maxP inst mi A ∗ Cd))
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ign N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    code n maxP inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n maxP ta (A 578) idx de live B Bsaved (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ign bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n maxP ta (A 578) idx de live B Bsaved (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hck : iprop(code n maxP inst mi A ∗ Cd) ⊢
      SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply code_keys n maxP inst mi A
    iexact Hcode
  have hcv : iprop(code n maxP inst mi A ∗ Cd) ⊢
      SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply code_values n maxP inst mi A
    iexact Hcode
  have hk := SerdeStructObjKeyState.keyHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K646 hlen hptr (by omega) hkeys hkeysSaved iprop(code n maxP inst mi A ∗ Cd) hck
  have hv := SerdeStructObjValueState.valueHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K169 hlen hptr (by omega) hvalues iprop(code n maxP inst mi A ∗ Cd) hcv
  obtain ⟨_, hdvs, higns, hstrs, _, _⟩ := SerdeFromTrait.reader_facts
    (dv := valueAs WNear.account) (ign := ign) (fun _ => Or.inl rfl) hign bs
  have result := SerdeStructObjState.f228_obj_state (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout (by omega) hptr hde hsp hal hi
    (valueAs WNear.account) ign K646 K169 K81 (member n maxP ta (A 578) idx de live B Bsaved)
    iprop(code n maxP inst mi A ∗ Cd) hk hv hignore
    (fun i j seen hij => SerdeStructObjKeyState.member_mono n maxP ta (A 578) idx de live B Bsaved hmono hmonoSaved i j seen hij)
    hdvs higns hstrs N a rF hb0 hloop
  iintro ⟨#Hcode, #HCd⟩
  iapply result
  iframe Hcode HCd
  iunfold code at Hcode
  icases Hcode with ⟨#C193, -, -, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77⟩
  iframe C193 F205 F201 F193 F89 F90 F81 F169 F77

end Proof
end WNear.Binary.SerdeStructObjModelState
