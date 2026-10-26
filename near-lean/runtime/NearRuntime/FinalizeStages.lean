import NearRuntime.Apply

namespace Near
open Wasm.Near

/-- `finalizeReceipt` as a chain of stages: a property of the rolled-back
attempt that every stage preserves holds of the finalized receipt. The
stages are the charge record, the deposit refund, the gas refund, the
receipt reward, the delivered result and the default return value with the receipt's compute. -/
theorem finalizeReceipt_stages (P : Exec → Prop) (c : ReceiptCtx) (st0 : ChainState) (exec : Exec)
    (failed : Option RuntimeError)
    (base : P (rollbackReceipt st0 exec failed))
    (charge : ∀ e tokens other, P e → P { e with tokensBurnt := tokens, otherTokensBurnt := other })
    (balance : ∀ e receiver amount, P e → P (e.addBalanceRefund receiver amount))
    (gas : ∀ e receiver pk amount, P e → P (e.addGasRefund receiver pk amount))
    (reward : ∀ e burnPrice purchasePrice, P e →
      P (e.creditReceiptReward c.cfg c.receipt.receiverId burnPrice purchasePrice))
    (finish : ∀ e, P e → P (e.finishReceiptResult c failed))
    (result : ∀ e r k, P e → P { e with result := r, computeUsage := k }) :
    P (finalizeReceipt c st0 exec failed) := by
  unfold finalizeReceipt
  dsimp only
  apply result; apply finish; apply reward
  repeat' (first | (apply charge; exact base) | apply gas | apply balance | split)

end Near
