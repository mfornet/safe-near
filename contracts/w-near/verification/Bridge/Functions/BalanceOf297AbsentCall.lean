import Bridge.Functions.BalanceOfCallerAbsent

/-! The actual function-297 instruction segment that calls the token balance method. -/

namespace WNear.Binary.BalanceOf297AbsentCall

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293 pre293 post293)

/-- Actual argument setup and the call to function 293 in the decoded function 297. -/
def callCode : List Instr :=
  [.local_get 0, .i32_const 8, .i32_binop .add,
   .local_get 0, .i32_const 48, .i32_binop .add,
   .local_get 0, .i32_const 88, .i32_binop .add, .call 293]

theorem callCode_eq : (f297.body.drop 91).take 10 = callCode := by rfl

/-- Function 297's locals at this point: the remaining locals are preserved. -/
def frame (inst : Nat) (mi : ModuleInst) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32) : Frame :=
  ⟨#[.i32 s, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual 297 call segment composes the absent token-balance proof. -/
theorem call_absent (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 20 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest ob : List UInt8) (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 2 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hnone : h.storage (pre ++ (bytes32 L ++ key)) = none) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      credits Cg (2100 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)) + R) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      ▷ (∀ rs, credits Cg R -∗ post293 n g ta A gt s (s + 8) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)
        [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] rs -∗ Φ.normal rs (frame inst mi s x1 x2 x3))
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 10) Φ := by
  iintro ⟨#Hcode, #F293, Hc, HP, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code293 at Hcode
    icases Hcode with ⟨#H415, -⟩
    iunfold BalanceOfAbsent.code415 at H415
    icases H415 with ⟨-, #Hd, -⟩
    iunfold DropVec.dropCode at Hd
    icases Hd with ⟨#H, -⟩
    iexact H
  have ha293 := hm.funcs 293 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  unfold cost399None
  generalize hK395 : LookupMapBorsh.cost395 cfg F L = K395
  generalize hK510 : LookupMapLeaves.cost510 cfg F pl (0 + 4 + L) = K510
  generalize hKr : storageReadUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  rw [callCode_eq]
  simp only [callCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  ihave #S293 := BalanceOfAbsent.f293_none (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      s (s + 8) (s + 48) pp pc pl (s + 88) p c L idx maxP len live F hF pre key rest ob
      hs hal hob (by simp [UInt32.toNat_add]; omega) hpre hkey hrest hc hL hpl hl0 hpp
      (by simp [UInt32.toNat_add]; omega) hp hroom h st hacc hlim hb hz hlink hproof hbud hnone $$ Hcode
  mcall S293 using [HP] with (simp only [cost399None, hK395, hK510, hKr]; mstep_norm_full; omega)
  · iexact HP
  simp only [cost399None, hK395, hK510, hKr]
  mcredits R
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc]
  · iexact Hc
  · iexact HQ

end Spec
end WNear.Binary.BalanceOf297AbsentCall
