import Bridge.Functions.BalanceOf297ComposeExpect
import Bridge.Functions.ValueReturn

/-! Return the bytes of the successful balance-result vector. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)

def returnCode : List Instr :=
  [.local_get 0, .local_get 0, .i32_const 144, .i32_binop .add, .call 779,
   .local_get 0, .load .i32 none ⟨2, 0⟩, .local_get 0, .load .i32 none ⟨2, 4⟩, .call 545]

theorem returnCode_eq : (f297.body.drop 128).take 10 = returnCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The actual dereference and value-return instructions for a serialized vector. -/
theorem return_vec (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 5 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (x3 q L : UInt32) (bs ob : List UInt8) (hbs : bs.length = L.toNat) (hob : ob.length = 8)
    (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0) (_hframe : s.toNat + 160 ≤ 2 ^ 32)
    (h : NearState) (hlim : withinLimit h.config.maxReturnLen L.toNat = true) (hpos : 0 < L.toNat)
    (s8 s12 w0 w4 w8 w12 : UInt32) (Φ : Post NearState GF) :
    A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗
      A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (306 * cfg.regularOpCost + valueReturnUse h L.toNat + R) ∗
      n ↦[wms][ s.toNat ] ob ∗ n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ bytes32 128 ++ bytes32 L) ∗
      ValueReturn.pre n g ta A ⟨gt, .i32 s⟩ s q L bs s8 s12 w0 w4 w8 w12 h [.i32 q, .i32 L] ∗
      ▷ (∀ rs, (credits Cg R ∗ n ↦[wms][ s.toNat ] (bytes32 q ++ bytes32 L) ∗
        n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ bytes32 128 ++ bytes32 L) ∗
        ValueReturn.post n g ta A ⟨gt, .i32 s⟩ s q L bs h [.i32 q, .i32 L] rs) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 128).take 10) Φ := by
  iintro ⟨#F779, #F545, #F456, #HIC, #Hi, Hc, Ho, Hv, HP, HΦ⟩
  have hn := hm.mem
  have ha779 := hm.funcs 779 (by decide)
  have ha545 := hm.funcs 545 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  have hlt := s.toNat_lt
  rw [returnCode_eq]
  simp only [returnCode, frame]
  mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg s (s + 144) ob
    (bytes32 q ++ bytes32 128 ++ bytes32 L) hob (by simp)) using [Ho Hv]
  · iunfold VecDeref.pre
    iframe Ho Hv
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, Ho, Hv⟩
  subst hrs
  have hvb : (bytes32 q ++ (bytes32 128 ++ bytes32 L)).take 4 ++
      (bytes32 q ++ (bytes32 128 ++ bytes32 L)).drop 8 = bytes32 q ++ bytes32 L := by
    simp [List.drop_append, bytes32_length]
  rw [hvb]
  icases BorshFT.split64' (a := s.toNat) (b := s.toNat + 4) q L (by omega) $$ Ho with ⟨O0, O4⟩
  mstep; mstep [O0]; mstep; mstep [O4]
  ihave #S545 := ValueReturn.f545_spec cfg lim (d + 1) types[14]! rfl inst mi e A n g ta mx hm (by omega)
    Cg ⟨gt, .i32 s⟩ s rfl hs hal h q L bs hbs hlim hpos s8 s12 w0 w4 w8 w12 $$ [F456 HIC]
  · iframe F456 HIC
  mcall S545 using [HP]
  · iexact HP
  mcredits R
  ihave Ho := BorshFT.join64' (a := s.toNat) (b := s.toNat + 4) q L (by omega) $$ [O0 O4]
  · iframe O0 O4
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Ho Hv HQ]
  iframe Hc Ho Hv HQ

end Spec
end WNear.Binary.BalanceOf297AbsentCall
