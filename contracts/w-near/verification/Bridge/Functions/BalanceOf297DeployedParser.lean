import Bridge.Functions.BalanceOf297ParserFamily
import Bridge.Functions.FromSliceSpec
import Bridge.Methods.Statics297Object

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/

namespace WNear.Binary.SerdeObjectNoEsc
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open WNear.Binary
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem parser_code_of_context (cfg : RuntimeConfig) (h : NearState) :
    FromSliceSpec.codeCtx (GF := GF) cfg h ⊢ parserCode 0 0 wInst id := by
  iintro HC
  iunfold FromSliceSpec.codeCtx at HC
  icases HC with ⟨#HF, #Hi, #Hm⟩
  ihave HP := InitialState.code297_parser_of cfg h $$ []
  · iframe HF Hi Hm
  ihave HR := InitialState.code297_return_of cfg h $$ []
  · iframe HF Hi Hm
  ihave HG := InitialState.ignored_code_of cfg h $$ []
  · iframe HF Hi
  iunfold BalanceOf297AbsentCall.code297Parser at HP
  icases HP with ⟨P0, P1, P2, P3, P4, -, -⟩
  iunfold BalanceOf297AbsentCall.code297Return at HR
  icases HR with ⟨-, -, -, -, -, -, D, -⟩
  iunfold parserCode
  iframe P0 P1 P2 P3 P4 D HG Hi

end WNear.Binary.SerdeObjectNoEsc

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem parser_family_mono (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (gt : GlobalType) (bs : List UInt8) (a : WNear.AccountId)
    (F parseGas outF : Nat) (Cd Ce : IProp GF) (hCode : Cd ⊢ Ce)
    (hp : ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Ce) :
    ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd := by
  intro Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL
  exact hCode.trans (hp Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL)

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary

/-- A parser family over the actual instantiated code at every entry host state. -/
def DeployedParserProvider (cfg : RuntimeConfig) (bs : List UInt8) (a : WNear.AccountId)
    (parseGas outF : Nat) : Prop :=
  ∀ (h : NearState) [WasmGS NearState (WasmLogic.GF NearState)],
    ParserFamily (GF := WasmLogic.GF NearState) cfg.wasm execLimits 0 wInst id 0 0 0 InitialState.g0.type bs a 1 parseGas outF
      (FromSliceSpec.codeCtx cfg h)

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.SerdeObjectNoEsc
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead
open WNear.SerdeStructModel

theorem deployed_parser_provider (cfg : RuntimeConfig) (bs rest : List UInt8) (a : WNear.AccountId) (N : Nat)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.DeployedParserProvider cfg bs a (parserCost cfg.wasm 1 bs rest N) 2 := by
  intro h _
  apply BalanceOf297AbsentCall.parser_family_mono cfg.wasm execLimits 0 wInst id 0 0 0
    InitialState.g0.type bs a 1 (parserCost cfg.wasm 1 bs rest N) 2
    (FromSliceSpec.codeCtx cfg h) (parserCode 0 0 wInst id) (parser_code_of_context cfg h)
  exact parser_family cfg.wasm execLimits 0 wInst id 0 0 0 Interface.wInst_ifaceMod InitialState.g0.type
    bs rest a N 1 hnb ho hloop hend

end WNear.Binary.SerdeObjectNoEsc
