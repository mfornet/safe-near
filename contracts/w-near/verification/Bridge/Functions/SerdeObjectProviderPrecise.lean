import Bridge.Functions.SerdeObjectParserPrecise
import Bridge.Functions.SerdeObjectLedgerGas

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
open WNear.Binary.LookupMapOps (HeapRoomK)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem f65_ledger_precise_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 45 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : PreciseKeyGasCharges cfg bs (Ledger bs mlen F false) K646)
    (hkeysSaved : PreciseKeyGasCharges cfg bs (Ledger bs mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Ledger bs mlen F false) K169)
    (hignored : IgnoreCharges cfg bs K81 (Ledger bs mlen F false))
    (hignoredSaved : IgnoreCharges cfg bs K81 (Ledger bs mlen F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 45 * cfg.regularOpCost + ((975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ hl', ⌜LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
          BalanceOf297AbsentCall.okAtFixed n out a live hl' (F + 43))) := by
  apply (f65_ledger_precise cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N k mlen F live hob hout hlen hptr hsp hal K646 K169 K81
    hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hk hend).trans
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, %p, %cap, %len, O0, O4, O8, O12, Hclean⟩
  iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident
  isplitr
  · ipureintro; exact hrs
  iapply ledger_result_room n mlen F live out p cap len a hsetup
  iframe O0 O4 O8 O12 Hclean


set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem ledger_precise_parser_contract (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (sp out ptr idx : UInt32) (ob bs rest : List UInt8) (a : WNear.AccountId) (N mlen F : Nat)
    (live : List (Nat × Nat)) (hd : d + 45 < lim.maxCallDepth)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : PreciseKeyGasCharges cfg bs (Ledger bs mlen F false) K646)
    (hkeysSaved : PreciseKeyGasCharges cfg bs (Ledger bs mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Ledger bs mlen F false) K169)
    (hignored : IgnoreCharges cfg bs K81 (Ledger bs mlen F false))
    (hignoredSaved : IgnoreCharges cfg bs K81 (Ledger bs mlen F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.ParserCallContract (GF := GF) cfg lim d inst mi A n g ta Cg gt sp out ptr idx
      ob bs a mlen live F (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43)
      (ledgerParserCode n inst mi A) (ledgerParserStatics n) := by
  unfold BalanceOf297AbsentCall.ParserCallContract
  have hs := f65_ledger_precise_room (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N (bs.length - rest.length) mlen F live hob hout hlen hptr hsp hal K646 K169 K81 hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop rfl hend
  unfold ledgerParserCode
  simp only [ledgerParserCost, Nat.add_assoc]
  apply hs.trans
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, HFr⟩
    iunfold ledgerParserStatics at HFr
    icases HFr with ⟨Hkey, Hident⟩
    iframe Hg Hs Hvt Hheap Ho Hbs He Hw Hhex Hkey Hident
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
    iunfold ledgerParserStatics
    iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident Hresult
    ipureintro; exact hrs



set_option maxRecDepth 100000 in
/-- General object parsing supplies the same checked family used by the full balance pipeline. -/
theorem ledger_precise_parser_family (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (bs rest : List UInt8) (a : WNear.AccountId) (N F : Nat) (K646 K169 K81 : Nat → Nat)
    (hlen : bs.length ≤ 4194304) (hF : 1 ≤ F)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges cfg bs (Ledger bs len F false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges cfg bs (Ledger bs len F true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges cfg bs (Ledger bs len F false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg bs K81 (Ledger bs len F false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg bs K81 (Ledger bs len F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.ParserFamily (GF := GF) cfg lim inst mi A n g ta gt bs a F
      (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43) (ledgerParserCode n inst mi A) := by
  intro Cg d sp out ptr idx ob len live hd hob hout _ hptr hsp hal hL
  exact ledger_precise_parser_contract cfg lim d inst mi A n g ta Cg hm gt sp out ptr idx ob bs rest a N len F live
    hd hob hout hlen hptr hsp hal K646 K169 K81 (input_ledger_bounds bs len F hlen hF hL)
    (hkeys len hL) (hkeysSaved len hL) (hvalues len hL) (hignored len hL) (hignoredSaved len hL) ho hloop hend

end Resource

theorem ledger_precise_deployed_parser_provider (cfg : RuntimeConfig) (bs rest : List UInt8) (a : WNear.AccountId)
    (N : Nat) (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges cfg.wasm bs (Ledger bs len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges cfg.wasm bs (Ledger bs len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges cfg.wasm bs (Ledger bs len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg.wasm bs K81 (Ledger bs len 1 false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg.wasm bs K81 (Ledger bs len 1 true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.DeployedParserProvider cfg bs a (ledgerParserCost cfg.wasm K646 K169 K81 bs rest N) 44 := by
  intro h _
  apply BalanceOf297AbsentCall.parser_family_mono cfg.wasm execLimits 0 wInst id 0 0 0
    InitialState.g0.type bs a 1 (ledgerParserCost cfg.wasm K646 K169 K81 bs rest N) 44
    (FromSliceSpec.codeCtx cfg h) (ledgerParserCode 0 0 wInst id) (ledger_parser_code_of_context cfg h)
  exact ledger_precise_parser_family cfg.wasm execLimits 0 wInst id 0 0 0 Interface.wInst_ifaceMod InitialState.g0.type
    bs rest a N 1 K646 K169 K81 hlen (by decide) hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend

open NearInterface ContractModel in
/-- The original model-budget witness is coupled to this actual general-object parser. -/
theorem ledger_precise_provider_plan (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw modelSt ctx S a
      (ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N) 44) :
    BalanceOf297AbsentCall.AbsentParserPlan cfg size raw modelSt ctx S a bs := by
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact ⟨ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N, 44, by omega, hpos,
    ledger_precise_deployed_parser_provider ctx.protocol bs rest a N K646 K169 K81 hlen
      hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend, hbudget⟩

open NearInterface ContractModel in
theorem ledger_precise_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      PreciseKeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N) 44)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∉ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hPlan := ledger_precise_provider_plan cfg ctx raw (some S) S a bs rest N size K646 K169 K81 hlen
    hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend hbudget
  exact BalanceOf297AbsentCall.provider_plan_refines_init cfg size codeOf raw ctx S a bs
    hp hwf hm hl hPlan hargs hrep ha



end WNear.Binary.SerdeObjectMixedTrace
