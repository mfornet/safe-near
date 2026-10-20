import NearRuntime.FunctionCallInvariants
import NearVM.PromiseGas
import Interpreter.Wasm.ByteEncoding

namespace Near
open Wasm Wasm.Near Wasm.ByteEncoding

@[simp] theorem bytesOfString_length (s : String) : (bytesOfString s).length = s.utf8ByteSize :=
  string_utf8_length s

@[simp] theorem stringOfBytes_bytesOfString (s : String) : stringOfBytes (bytesOfString s) = s := by
  unfold stringOfBytes bytesOfString
  rw [byteArray_of_toList, string_fromUTF8_toUTF8]
  rfl

/-- Size is fixed by the actual promise payload, independent of decoder metadata. -/
theorem actionOfPromise_deploy_size (decoder : Bytes → ContractCode) (bytes : Bytes) :
    actionOfPromise decoder (.deployContract bytes) =
      .deployContract { decoder bytes with size := bytes.length } := rfl

theorem deployPromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (bytes : Bytes) :
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver (actionOfPromise decoder (.deployContract bytes)) =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver) (.deployContract bytes) := rfl

/-- Byte-preserving UTF-8 method encoding supplies the exact runtime billing
length. No gas or financial equation is assumed. -/
theorem functionCallPromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver method : String) (args : Bytes) (deposit : Nat) (gas : UInt64) :
    let action := actionOfPromise decoder (.functionCall (bytesOfString method) args deposit gas)
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver action + action.attachedGas =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver)
        (.functionCall (bytesOfString method) args deposit gas) := by
  simp [actionOfPromise, Fees.exec, Action.attachedGas, actionExecutionGas]

theorem functionCallPromise_executionGas_of_utf8 (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (method args : Bytes) (decoded : String) (deposit : Nat) (gas : UInt64)
    (hutf8 : String.fromUTF8? (ByteArray.mk method.toArray) = some decoded) :
    let action := actionOfPromise decoder (.functionCall method args deposit gas)
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver action + action.attachedGas =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver)
        (.functionCall method args deposit gas) := by
  have hb := congrArg ByteArray.toList (string_fromUTF8_some_bytes _ decoded hutf8)
  have he : bytesOfString decoded = method := by
    simpa only [bytesOfString, byteArray_toList_ofArray] using hb
  rw [← he]
  exact functionCallPromise_executionGas cfg decoder receiver decoded args deposit gas

/-- These action variants have no method-list encoding obligation. Deployment
uses actual byte length; transfers share the implicit-account fee calculation. -/
def SimpleGasAction : PromiseAction → Prop
  | .functionCall .. => False
  | .addKey _ _ (.functionCall ..) => False
  | _ => True

theorem simplePromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (action : PromiseAction) (h : SimpleGasAction action) :
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver (actionOfPromise decoder action) +
      (actionOfPromise decoder action).attachedGas =
        actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver) action := by
  cases action <;> try contradiction
  case addKey pk nonce permission =>
    cases permission <;> first | rfl | contradiction
  all_goals rfl

end Near
