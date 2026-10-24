import NearNode.Primitives.Basic

/-!
# Block approvals

`near-primitives::block_header` at `=0.37.4`: `ApprovalInner` (endorse a block or skip a height),
`Approval` with its signing payload (`Approval::get_data_for_sig`) and `ApprovalMessage`.
-/

namespace Near.Node

open Borsh

/-- `ApprovalInner`: an endorsement of a block hash, or a skip of everything up to a height. -/
inductive ApprovalInner where
  | endorsement (h : CryptoHash)
  | skip (height : BlockHeight)
  deriving BEq, Inhabited

instance : Codec ApprovalInner :=
  .enum "ApprovalInner"
    [.variant 0 CryptoHash .endorsement fun
        | .endorsement h => some h
        | _ => none,
      .variant 1 BlockHeight .skip fun
        | .skip h => some h
        | _ => none]

/-- `Approval`. -/
structure Approval where
  inner : ApprovalInner
  targetHeight : BlockHeight
  signature : Signature
  accountId : AccountId
  deriving BEq, Inhabited

instance : Codec Approval :=
  .iso (ApprovalInner × BlockHeight × Signature × AccountId) (fun (i, t, s, a) => ⟨i, t, s, a⟩)
    fun x => (x.inner, x.targetHeight, x.signature, x.accountId)

/-- `Approval::get_data_for_sig`: the bytes the approval signature covers. -/
def Approval.getDataForSig (inner : ApprovalInner) (targetHeight : BlockHeight) : ByteArray :=
  Codec.encode inner ++ Codec.encode targetHeight

/-- The signed bytes of an approval. -/
def Approval.sigData (a : Approval) : ByteArray :=
  Approval.getDataForSig a.inner a.targetHeight

/-- `ApprovalMessage`: an approval sent to the block producer of its target height. -/
structure ApprovalMessage where
  approval : Approval
  target : AccountId
  deriving BEq, Inhabited

instance : Codec ApprovalMessage :=
  .iso (Approval × AccountId) (fun (a, t) => ⟨a, t⟩) fun x => (x.approval, x.target)

end Near.Node
