import Bridge.Functions.BalanceOf297ComposeCleanup

/-! Copy the parsed account string descriptor to the balance-call argument. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.AllocNewCell (memBytes_addr)

def argumentCopyCode : List Instr :=
  [.local_get 0, .i32_const 88, .i32_binop .add, .i32_const 8, .i32_binop .add,
   .local_get 3, .load .i32 none ⟨2, 0⟩, .store .i32 none ⟨2, 0⟩,
   .local_get 0, .local_get 0, .load .i64 none ⟨3, 32⟩, .store .i64 none ⟨3, 88⟩]

theorem argumentCopyCode_eq : (f297.body.drop 79).take 12 = argumentCopyCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Copy the parsed string descriptor into the exact balance-call argument. -/
theorem argument_copy (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat) (s x1 : UInt32) (x2 : UInt64) (p c L : UInt32)
    (ob : List UInt8) (hob : ob.length = 12) (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : Post NearState GF) :
    credits Cg (12 * cfg.regularOpCost + R) ∗
      n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
      n ↦[wms][ (s + 88).toNat ] ob ∗
      ▷ (credits Cg R ∗ n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
        n ↦[wms][ (s + 88).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) -∗
        Φ.normal [] (frame inst mi s x1 x2 (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 (s + 40)) [] ((f297.body.drop 79).take 12) Φ := by
  iintro ⟨Hc, Hsrc, Hdst, HΦ⟩
  have hlt := s.toNat_lt
  ihave Hsrc := U128From.memBytes_split n (s + 32).toNat 8 (bytes32 p ++ (bytes32 c ++ bytes32 L)) (by simp) $$ Hsrc
  icases Hsrc with ⟨S0, S8⟩
  ihave Hdst := U128From.memBytes_split n (s + 88).toNat 8 ob (by omega) $$ Hdst
  icases Hdst with ⟨D0, D8⟩
  ihave S8 := memBytes_addr (show (s + 32).toNat + 8 = (s + 40).toNat by simp [UInt32.toNat_add]; omega) $$ S8
  ihave D8 := memBytes_addr (show (s + 88).toNat + 8 = (s + 96).toNat by simp [UInt32.toNat_add]; omega) $$ D8
  rw [argumentCopyCode_eq]
  simp only [argumentCopyCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [S8] with (simp [loadWidth, NumType.byteWidth, bytes32_length])
  mstep [D8] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep
  mstep [S0] with (simp [loadWidth, NumType.byteWidth, bytes32_length])
  mstep [D0] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mcredits R
  have ht : (bytes32 p).take 8 = bytes32 p := by apply List.take_of_length_le; simp [bytes32_length]
  have hd : (bytes32 p).drop 8 = [] := by apply List.drop_eq_nil_of_le; simp [bytes32_length]
  have ht4 : (bytes32 c).take 4 = bytes32 c := by apply List.take_of_length_le; simp [bytes32_length]
  have hd4 : (bytes32 c).drop 4 = [] := by apply List.drop_eq_nil_of_le; simp [bytes32_length]
  simp only [List.take_append, List.drop_append, bytes32_length, Nat.reduceSub, List.take_zero,
    List.drop_zero, List.nil_append, List.append_nil, ht, hd, ht4, hd4]
  have h64 : storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE (bytes32 p ++ bytes32 c)))) 8 = bytes32 p ++ bytes32 c := by
    simpa [loadValue] using FtTotalSupplyGetter.storeBytes_load_i64 (bytes32 p ++ bytes32 c) (by simp [bytes32_length])
  rw [h64, decodeLE_bytes32]
  simp only [UInt32.ofNat_toNat]
  ihave S8 := memBytes_addr (show (s + 40).toNat = (s + 32).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ S8
  ihave Hsrc := U128From.memBytes_join n (s + 32).toNat 8 (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32_length]) $$ [S0 S8]
  · iframe S0 S8
  ihave D8 := memBytes_addr (show (s + 96).toNat = (s + 88).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ D8
  ihave Hdst := U128From.memBytes_join n (s + 88).toNat 8 (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32_length]) $$ [D0 D8]
  · iframe D0 D8
  simp only [List.append_assoc]
  iapply HΦ $$ [Hc Hsrc Hdst]
  iframe Hc Hsrc Hdst

end Spec
end WNear.Binary.BalanceOf297AbsentCall
