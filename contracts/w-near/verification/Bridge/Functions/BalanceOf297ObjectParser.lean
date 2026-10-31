import Bridge.Functions.BalanceOf297ObjectRoom
import Bridge.Functions.BalanceOf297ParserProvider

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.SerdeObjectNoEsc
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.SerdeStructModel
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def parserCode (n inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
    ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnValue.code81 inst mi A ∗
    A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
    inst ↪[inst] mi)
instance (n inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (parserCode (GF := GF) n inst mi A) := by
  unfold parserCode; infer_instance

def parserStatics (n : Nat) : IProp GF :=
  iprop(n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes)

def parserCost (cfg : WasmConfig) (F : Nat) (bs rest : List UInt8) (N : Nat) : Nat :=
  45 * cfg.regularOpCost + (700 + 96 * wsLen (bs.drop (bs.length - rest.length))) * cfg.regularOpCost +
    SerdeStructObj.costObj cfg (SerdeKeyNoEsc.K646 cfg bs) (SerdeAcctHyp.K169 cfg bs F)
      (SerdeIgnReuse.cost81 cfg bs) (valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem parser_contract (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (sp out ptr idx : UInt32) (ob bs rest : List UInt8) (a : WNear.AccountId) (N mlen F : Nat)
    (live : List (Nat × Nat)) (hd : d + 45 < lim.maxCallDepth)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (hnb : (0x5C : UInt8) ∉ bs)
    (hL : mlen = InitialState.memLen ∨ mlen = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.ParserCallContract (GF := GF) cfg lim d inst mi A n g ta Cg gt sp out ptr idx
      ob bs a mlen live F (parserCost cfg F bs rest N) (max F 1 + 1)
      (parserCode n inst mi A) (parserStatics n) := by
  unfold BalanceOf297AbsentCall.ParserCallContract
  have hs := f65_obj_room (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N (bs.length - rest.length) mlen F live hob hout hlen hptr hsp hal hnb hL ho hloop rfl hend
  unfold parserCode
  simp only [parserCost, Nat.add_assoc]
  apply hs.trans
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, HFr⟩
    iunfold parserStatics at HFr
    icases HFr with ⟨Hkey, Hident⟩
    iframe Hg Hs Hvt Hheap Ho Hbs He Hw Hhex Hkey Hident
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
    iunfold parserStatics
    iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident Hresult
    ipureintro; exact hrs

end WNear.Binary.SerdeObjectNoEsc
