import Bridge.Functions.SerdeStructObjRun

/-!
# `Input::deserialize` (78) for `ft_balance_of`: the struct's accepting run (M6)

78 calls `deserialize_struct` (228) with the struct's name and fields (unused by the code). This
file joins the two forms: wherever `SerdeStructModel.structDe` reads the struct from the input (the
reader at 0), 78 returns `Ok(a)` at `out`, the reader past the struct (`f78_acc`). The object form is
`SerdeStructObj.f228_obj`, the array form `SerdeStructArr.f228_arr`; `structDe_cases` says which.

The hypotheses are those of `f228_obj` and `f228_arr`, plus `hdv0`: `dv` reads nothing from the
empty input (true of any reader that agrees with the model, since `valueR [] = none`).
-/

namespace WNear.Binary.SerdeStruct78

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeErrBox (roomFor4)
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169 arrOk costArr)
open WNear.Binary.SerdeStructObj (Hyp646 Hyp81 costObj)
open NearInterface.Json

/-- The struct read by `structDe` is in the object form (the members read by `objLoop`) or in the
array form (`arrOk`). -/
theorem structDe_cases {dv : List UInt8 → Option (WNear.AccountId × List UInt8)}
    {ign : List UInt8 → Option (Unit × List UInt8)} {bs r : List UInt8} {a : WNear.AccountId}
    (h : SerdeStructModel.structDe "account_id" dv ign bs = some (a, r)) (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r) :
    (bs[wsLen bs]? = some 0x7B ∧
      SerdeStructModel.objLoop "account_id" dv ign (bs.length - (wsLen bs + 1) + 1) none (bs.drop (wsLen bs + 1)) =
        some (some a, r)) ∨
    (∃ r1, arrOk dv bs 0 a r1 ∧
      r = bs.drop (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) := by
  have hs := SerdeStructLoop.skip_drop bs 0
  simp only [List.drop_zero, Nat.zero_add] at hs
  by_cases ho : bs[wsLen bs]? = some 0x7B
  · left
    refine ⟨ho, ?_⟩
    have hsk := SerdeStructLoop.skip_drop_of (bs := bs) (x := 0) (by simpa using ho)
    simp only [List.drop_zero, Nat.zero_add] at hsk
    by_cases he : ∃ r', skipWhitespace (bs.drop (wsLen bs + 1)) = 0x7D :: r'
    · obtain ⟨r', he⟩ := he
      rw [SerdeStructModel.structDe_objE "account_id" dv ign hsk he] at h
      simp at h
    · rw [SerdeStructModel.structDe_objM "account_id" dv ign hsk (fun r' e => he ⟨r', e⟩)] at h
      have hl : (bs.drop (wsLen bs + 1)).length + 1 = bs.length - (wsLen bs + 1) + 1 := by simp
      rw [hl] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨seen, r2⟩, h1, h2⟩ := h
      cases seen with
      | none => simp at h2
      | some a2 =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact h1
  · right
    by_cases ha : bs[wsLen bs]? = some 0x5B
    · have hsk := SerdeStructLoop.skip_drop_of (bs := bs) (x := 0) (by simpa using ha)
      simp only [List.drop_zero, Nat.zero_add] at hsk
      have hj0l := SerdeNextKey.getElem_lt ha
      by_cases he : ∃ r', skipWhitespace (bs.drop (wsLen bs + 1)) = 0x5D :: r'
      · obtain ⟨r', he⟩ := he
        rw [SerdeStructModel.structDe_arrE "account_id" dv ign hsk he] at h
        simp at h
      · rw [SerdeStructModel.structDe_arrM "account_id" dv ign hsk (fun r' e => he ⟨r', e⟩)] at h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨⟨a1, r1⟩, hd, h2⟩ := h
        rw [SerdeStructLoop.skip_drop] at hd he
        have hne : bs.drop (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) ≠ [] := by
          intro e; rw [e, hdv0] at hd; simp at hd
        obtain ⟨b, hb⟩ : ∃ b, bs[wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))]? = some b := by
          rcases hx : bs.drop (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) with _ | ⟨b, t⟩
          · exact absurd hx hne
          · exact ⟨b, (SerdeStructLoop.drop_cons hx).1⟩
        have hb93 : b ≠ 0x5D := by
          intro e; subst e
          apply he
          have := SerdeStructLoop.skip_drop_of (bs := bs) (x := wsLen bs + 1) hb
          rw [SerdeStructLoop.skip_drop] at this
          exact ⟨_, this⟩
        have hj2 : wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) ≤ bs.length := (SerdeNextKey.getElem_lt hb).le
        have hr1 := hdvs _ a1 r1 hj2 hd
        unfold SerdeStructModel.arrEnd at h2
        split at h2
        · rename_i r3 hsk3
          simp only [Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          rw [← hr1] at hsk3
          obtain ⟨h4, h5⟩ := SerdeStructLoop.skip_drop_cons hsk3
          refine ⟨r1, ⟨by simpa using ha, ⟨b, by simpa using hb, hb93⟩, by simpa using hd, ?_⟩, h5⟩
          rw [hr1]; rw [hr1] at h4; exact h4
        · simp at h2
    · exfalso
      rw [SerdeStructModel.structDe_other "account_id" dv ign] at h
      · simp at h
      · intro r' e; rw [hs] at e; exact ho (SerdeStructLoop.drop_cons e).1
      · intro r' e; rw [hs] at e; exact ha (SerdeStructLoop.drop_cons e).1

/-- The cost of the struct: the object form's or the array form's, whichever the input is in (both
counted, a bound). -/
def costS (cfg : WasmConfig) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) : Nat :=
  costObj cfg K646 K169 K81 dv ign bs (bs.length - (wsLen bs + 1) + 1) 0 +
  match dv (bs.drop (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)))) with
  | some (_, r1) => costArr cfg K169 bs 0 r1
  | none => 0

section L78

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Input::deserialize` (78) on an accepted struct**: wherever `structDe` reads `a` from the
input, leaving `r`, `out` gets `Ok(a)` and the reader is at `|bs| - |r|`. -/
theorem f78_acc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 21 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 336 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hr : roomFor4 mlen maxP 20)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat) (Cd : IProp GF) [Persistent Cd]
    (h646 : Hyp646 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP K646 Cd)
    (h169 : Hyp169 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Cd)
    (h81 : Hyp81 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP ign K81 Cd)
    (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (higns : ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r)
    (hstrs : ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r)
    (a : WNear.AccountId) (r : List UInt8)
    (h : SerdeStructModel.structDe "account_id" dv ign bs = some (a, r)) :
    SerdeNextKey.code193 n maxP inst mi A ∗ A 205 ↪[wf] FuncInst.wasm types[14]! inst f205 ∗
      A 201 ↪[wf] FuncInst.wasm types[32]! inst f201 ∗ A 193 ↪[wf] FuncInst.wasm types[11]! inst f193 ∗
      A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗ A 90 ↪[wf] FuncInst.wasm types[32]! inst f90 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
      A 77 ↪[wf] FuncInst.wasm types[0]! inst f77 ∗ A 214 ↪[wf] FuncInst.wasm types[14]! inst f214 ∗
      A 91 ↪[wf] FuncInst.wasm types[32]! inst f91 ∗ A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f78 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs 0 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => 40 * cfg.regularOpCost + costS cfg K646 K169 K81 dv ign bs)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - r.length))) := by
  iintro ⟨#H193c, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77, #F214, #F91, #F228, #HCd⟩
  ihave #Hv := H193c
  iunfold SerdeNextKey.code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  ihave #Hv' := Hv
  iunfold SerdeEnds.endCode at Hv'
  icases Hv' with ⟨#Hcode, -⟩
  iunfold SerdeErrBox.errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha228 := hm.funcs 228 (by decide)
  have t36 : types[36]!.params.length = 6 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hd, Ht, Hkey⟩
  subst hargs
  simp only [f78]
  unfold costS
  rcases structDe_cases h hdv0 hdvs with ⟨ho, hl⟩ | ⟨r1, hok, hrr⟩
  · have s := SerdeStructObj.f228_obj (GF := GF) cfg lim (d + 1) types[36]! (by rfl) inst mi A n g ta hm (by omega) Cg
      gt sp out de ptr idx out out out out ob bs 0 maxP mlen F live hob hout hlen hptr hde hsp hal (by omega) hr dv ign
      K646 K169 K81 Cd h646 h169 h81 hdvs higns hstrs (bs.length - (wsLen bs + 1) + 1) a r (by simpa using ho)
      (by simpa using hl)
    try simp only [List.drop_zero, Nat.zero_add] at s
    generalize hC : costObj cfg K646 K169 K81 dv ign bs (bs.length - (wsLen bs + 1) + 1) 0 = C at s ⊢
    ihave #S := s $$ [H193c F205 F201 F193 F89 F90 F81 F169 F77 HCd]
    · iframe H193c F205 F201 F193 F89 F90 F81 F169 F77 HCd
    clear s
    clear hl ho h hdvs higns hstrs h646 h169 h81
    mstep; mstep; mstep; mstep; mstep; mstep
    mcall S using [Hg Hs Hvt Hh Ho Hrd Hd Ht Hkey]
    · iframe Hg Hs Hvt Hh Ho Hrd Hd Ht Hkey
    icases HQ with ⟨%hrs, HQ⟩
    subst hrs
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    icases HQ with ⟨Hg, Hs, Hvt, Hd, Ht, Hkey, HR⟩
    iframe Hg Hs Hvt Hd Ht Hkey HR
    ipureintro; simp [htype]
  · have s := SerdeStructArr.f228_arr (GF := GF) cfg lim (d + 1) types[36]! (by rfl) inst mi A n g ta hm (by omega) Cg
      gt sp out de ptr idx out out out out ob bs 0 maxP mlen F live hob hout hlen hptr hde hsp (by omega) hr dv
      K169 Cd h169 a r1 hok
    obtain ⟨-, -, hdv, hb4⟩ := hok
    simp only [List.drop_zero, Nat.zero_add] at hdv
    have hrl : bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1 = bs.length - r.length := by
      have := SerdeNextKey.getElem_lt hb4
      rw [hrr]; simp; omega
    rw [hrl] at s
    rw [hdv]
    generalize hC : costArr cfg K169 bs 0 r1 = C at s ⊢
    ihave #S := s $$ [Hv F214 F169 F91 HCd]
    · iframe Hv F214 F169 F91 HCd
    clear s
    clear hdv hb4 hrr hrl h hdvs higns hstrs h646 h169 h81
    mstep; mstep; mstep; mstep; mstep; mstep
    mcall S using [Hg Hs Hvt Hh Ho Hrd Hd Ht]
    · iframe Hg Hs Hvt Hh Ho Hrd Hd Ht
    icases HQ with ⟨%hrs, HQ⟩
    subst hrs
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    icases HQ with ⟨Hg, Hs, Hvt, Hd, Ht, HR⟩
    iframe Hg Hs Hvt Hd Ht Hkey HR
    ipureintro; simp [htype]

end L78

end WNear.Binary.SerdeStruct78
