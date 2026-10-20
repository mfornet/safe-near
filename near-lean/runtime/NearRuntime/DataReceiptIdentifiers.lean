import NearRuntime.IdentifierBounds

namespace Near
open Wasm.Near

theorem emitFunctionCallData_cons (receiver : AccountId) (bytes : Bytes)
    (output : DataReceiver) (outputs : List DataReceiver) (initial : ChainState) (receipts : List Receipt) :
    emitFunctionCallData receiver bytes (output :: outputs) initial receipts =
      emitFunctionCallData receiver bytes outputs { initial with nextId := initial.nextId + 1 }
        (receipts ++ [{ predecessorId := receiver, receiverId := output.receiverId, receiptId := initial.nextId, receipt := .data { dataId := output.dataId, data := some bytes } }]) := by
  simp only [emitFunctionCallData, ChainState.freshId, List.forIn_pure_yield_eq_foldl, List.foldl_cons]

/-- Data-delivery receipt identities are the exact fresh consecutive range,
independent of the already allocated callback data identities they carry. -/
theorem emitFunctionCallData_receiptIds (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (receipts : List Receipt) :
    ((emitFunctionCallData receiver bytes outputs initial receipts).2.map (·.receiptId)) =
      receipts.map (·.receiptId) ++ List.range' initial.nextId outputs.length := by
  induction outputs generalizing initial receipts with
  | nil => simp [emitFunctionCallData, Id.run, bind, pure]
  | cons output outputs ih =>
    rw [emitFunctionCallData_cons, ih]
    simp [List.map_append, List.range'_succ, List.append_assoc]

/-- Routing payload observed by a callback, separately from the envelope id. -/
def Receipt.dataDelivery (receipt : Receipt) : Option (DataId × AccountId × Option Bytes) :=
  match receipt.receipt with
  | .data data => some (data.dataId, receipt.receiverId, data.data)
  | .action _ => none

/-- The actual emitter preserves callback data ids, destination order and exact
return bytes. Allocating envelope ids does not reallocate dependency ids. -/
theorem emitFunctionCallData_deliveries (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (receipts : List Receipt) :
    ((emitFunctionCallData receiver bytes outputs initial receipts).2.map Receipt.dataDelivery) =
      receipts.map Receipt.dataDelivery ++ outputs.map (fun output => some (output.dataId, output.receiverId, some bytes)) := by
  induction outputs generalizing initial receipts with
  | nil => simp [emitFunctionCallData, Id.run, bind, pure]
  | cons output outputs ih =>
    rw [emitFunctionCallData_cons, ih]
    simp [List.map_append, Receipt.dataDelivery, List.append_assoc]

theorem emitFunctionCallData_receiptIds_nodup (receiver : AccountId) (bytes : Bytes)
    (outputs : List DataReceiver) (initial : ChainState) :
    ((emitFunctionCallData receiver bytes outputs initial).2.map (·.receiptId)).Nodup := by
  rw [emitFunctionCallData_receiptIds]
  simpa using List.nodup_range' (s := initial.nextId) (n := outputs.length)

/-- Each new envelope id is within this pass's allocation range. -/
theorem emitFunctionCallData_receiptId_bounds (receiver : AccountId) (bytes : Bytes)
    (outputs : List DataReceiver) (initial : ChainState) (receipt : Receipt)
    (hmem : receipt ∈ (emitFunctionCallData receiver bytes outputs initial).2) :
    initial.nextId ≤ receipt.receiptId ∧
      receipt.receiptId < (emitFunctionCallData receiver bytes outputs initial).1.nextId := by
  have hm : receipt.receiptId ∈ ((emitFunctionCallData receiver bytes outputs initial).2.map (·.receiptId)) :=
    List.mem_map.mpr ⟨receipt, hmem, rfl⟩
  rw [emitFunctionCallData_receiptIds] at hm
  simp only [List.map_nil, List.nil_append] at hm
  rw [emitFunctionCallData_nextId]
  exact List.mem_range'_1.mp hm

/-- New data envelopes cannot collide with pre-existing routing references. -/
theorem emitFunctionCallData_receiptId_fresh (receiver : AccountId) (bytes : Bytes)
    (outputs : List DataReceiver) (initial : ChainState) (h : initial.IdsBelowNext) (receipt : Receipt)
    (hmem : receipt ∈ (emitFunctionCallData receiver bytes outputs initial).2) :
    receipt.receiptId ∉ initial.liveIds := by
  have hb := (emitFunctionCallData_receiptId_bounds receiver bytes outputs initial receipt hmem).1
  intro hold
  have := h receipt.receiptId hold
  omega

/-- With bounded existing receipts and callback references, every id in emitted
data work is below the resulting allocator, including carried dependency ids. -/
theorem emitFunctionCallData_liveIds_below (receiver : AccountId) (bytes : Bytes)
    (outputs : List DataReceiver) (initial : ChainState) (receipts : List Receipt)
    (hreceipts : ∀ receipt ∈ receipts, ∀ id ∈ receipt.liveIds, id < initial.nextId)
    (houtputs : ∀ output ∈ outputs, output.dataId < initial.nextId) :
    ∀ receipt ∈ (emitFunctionCallData receiver bytes outputs initial receipts).2,
      ∀ id ∈ receipt.liveIds, id < (emitFunctionCallData receiver bytes outputs initial receipts).1.nextId := by
  induction outputs generalizing initial receipts with
  | nil => exact hreceipts
  | cons output outputs ih =>
    rw [emitFunctionCallData_cons]
    apply ih
    · intro receipt hmem id hid
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | rfl
      · exact (hreceipts receipt hold id hid).trans (Nat.lt_succ_self _)
      · simp only [Receipt.liveIds, List.mem_cons, List.not_mem_nil, or_false] at hid
        rcases hid with rfl | rfl
        · exact Nat.lt_succ_self _
        · exact (houtputs output (by simp)).trans (Nat.lt_succ_self _)
    · intro next hnext
      exact (houtputs next (by simp [hnext])).trans (Nat.lt_succ_self _)

end Near
