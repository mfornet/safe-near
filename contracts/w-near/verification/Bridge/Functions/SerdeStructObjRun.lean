import Bridge.Functions.SerdeStructObj

/-!
# `deserialize_struct` (228) on the object form: the run (M6)

`f228_obj`: on an input whose struct is in the object form and accepted (`{`, then
`objLoop "account_id" dv ign N none` reads the members up to the `}` with the account `a`), 228
returns `Ok(a)` at `out`, the reader past the `}`. The callees not proved yet are the hypotheses
`Hyp646` (keys), `Hyp169` (the account id) and `Hyp81` (ignored values), with the heap unchanged by
646 and 81. The loop's invariant `inv228` holds the members left (`loopRes`), the field read so far
(`seenRes`), and the credits `objCost` for the rest of the loop.
-/

namespace WNear.Binary.SerdeStructObj

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit)
open WNear.Binary.SerdeNextKey (Spec646 keyQ keyWs fieldOf)
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169 stk_join' store1)
open WNear.SerdeStructLoop (loopRes)
open NearInterface.Json

theorem or4 (x : UInt32) (h : x.toNat % 8 = 0) : (x ||| 4).toNat = x.toNat + 4 := by
  rw [UInt32.toNat_or]
  obtain ⟨k, hk⟩ : ∃ k, x.toNat = 8 * k := ⟨x.toNat / 8, by omega⟩
  rw [hk]
  have := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := 4) (by norm_num) k
  simp at this ⊢
  omega

theorem wsLen_brace {bs : List UInt8} {j : Nat} (h : bs[j]? = some 0x7D) : wsLen (bs.drop j) = 0 := by
  have hl := SerdeNextKey.getElem_lt h
  rw [List.drop_eq_getElem_cons hl]
  rw [List.getElem?_eq_getElem hl] at h
  simp only [Option.some.injEq] at h
  rw [h]; simp [wsLen]; decide

section Run

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 228's frame at the loop head: the locals, `l7`, `l8`, `l10` free. -/
def fr228 (inst : Nat) (mi : ModuleInst) (out de x2 x3 x4 x5 s : UInt32) (l7 : UInt64) (l8 l10 : UInt32) : Frame :=
  ⟨#[.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5, .i32 s, .i64 l7, .i32 l8, .i32 (s + 8 ||| 4),
    .i32 l10], inst, mi⟩

/-- The field read so far, at `s + 40` (`Option<ValidAccountId>`, `None` the pointer 0), and the
heap: before it, the heap with room for an error box; after it, the string (`strRes`). -/
def seenRes (n maxP : Nat) (live : List (Nat × Nat)) (s : UInt32) : Option WNear.AccountId → IProp GF
  | none => iprop(∃ (mlen F : Nat) (b8 : List UInt8), ⌜roomFor4 mlen maxP 20 ∧ b8.length = 8⌝ ∗
      n ↦[i32][ s.toNat + 40 ] 0 ∗ n ↦[wms][ s.toNat + 44 ] b8 ∗ heapInv n maxP mlen live F)
  | some a => iprop(∃ (p cap : UInt32), n ↦[i32][ s.toNat + 40 ] p ∗ n ↦[i32][ s.toNat + 44 ] cap ∗
      n ↦[i32][ s.toNat + 48 ] (UInt32.ofNat a.val.utf8ByteSize) ∗ strRes n maxP live a p cap)

/-- **The object loop's invariant**: at the loop head, the reader at `i`, `first` at `s + 36`, the
field read so far `sA` (`seenRes`), the members left `loopRes … N first sA (bs.drop i)` reading the
account `a` and leaving `rF`, and the credits for the rest (`objCost`, then `E` after the loop).
`Fr` is the rest of the state, unchanged by the loop. -/
def inv228 (n inst : Nat) (mi : ModuleInst) (Cg c : Nat) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (maxP : Nat) (live : List (Nat × Nat)) (out de ptr x2 x3 x4 x5 s : UInt32) (bs : List UInt8)
    (a : WNear.AccountId) (rF : List UInt8) (E R : Nat) (Fr : IProp GF) : List Wasm.Value → Frame → IProp GF :=
  fun X f => iprop(∃ (N : Nat) (first : Bool) (i : Nat) (sA : Option WNear.AccountId) (l7 : UInt64) (l8 l10 : UInt32)
      (b16 : List UInt8),
    ⌜X = [] ∧ f = fr228 inst mi out de x2 x3 x4 x5 s l7 l8 l10 ∧ i ≤ bs.length ∧ b16.length = 16 ∧
      loopRes "account_id" dv ign N first sA (bs.drop i) = some (some a, rF)⌝ ∗
    credits Cg (objCost c K646 K169 K81 dv ign bs N first i + E + R) ∗
    n ↦[wms][ s.toNat + 36 ] [if first then 1 else 0] ∗ n ↦[wms][ s.toNat + 8 ] b16 ∗
    seenRes n maxP live s sA ∗ rd n de ptr bs i ∗ Fr)

theorem costEnd_ok (cfg : WasmConfig) (F K w j : Nat) (ok : Prop) [Decidable ok] (h : ok) :
    SerdeEnds.costEnd cfg F K w j ok = (K + 96 * w) * cfg.regularOpCost := by
  unfold SerdeEnds.costEnd; rw [if_pos h]; simp

/-- 228's 64-byte frame, from the pieces the object path leaves. -/
theorem frame64o (n s : Nat) :
    stk (GF := GF) n s 8 ∗ stk n (s + 8) 4 ∗ stk n (s + 12) 4 ∗ stk n (s + 16) 8 ∗ stk n (s + 24) 4 ∗
      stk n (s + 28) 4 ∗ stk n (s + 32) 4 ∗ stk n (s + 36) 1 ∗ stk n (s + 37) 3 ∗ stk n (s + 40) 4 ∗
      stk n (s + 44) 8 ∗ stk n (s + 52) 12 ⊢ stk n s 64 := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12⟩
  ihave H11 := stk_join' n (s + 44) (s + 52) 8 12 (by omega) $$ [H11 H12]
  · iframe H11 H12
  ihave H10 := stk_join' n (s + 40) (s + 44) 4 20 (by omega) $$ [H10 H11]
  · iframe H10 H11
  ihave H9 := stk_join' n (s + 37) (s + 40) 3 24 (by omega) $$ [H9 H10]
  · iframe H9 H10
  ihave H8 := stk_join' n (s + 36) (s + 37) 1 27 (by omega) $$ [H8 H9]
  · iframe H8 H9
  ihave H7 := stk_join' n (s + 32) (s + 36) 4 28 (by omega) $$ [H7 H8]
  · iframe H7 H8
  ihave H6 := stk_join' n (s + 28) (s + 32) 4 32 (by omega) $$ [H6 H7]
  · iframe H6 H7
  ihave H5 := stk_join' n (s + 24) (s + 28) 4 36 (by omega) $$ [H5 H6]
  · iframe H5 H6
  ihave H4 := stk_join' n (s + 16) (s + 24) 8 40 (by omega) $$ [H4 H5]
  · iframe H4 H5
  ihave H3 := stk_join' n (s + 12) (s + 16) 4 48 (by omega) $$ [H3 H4]
  · iframe H3 H4
  ihave H2 := stk_join' n (s + 8) (s + 12) 4 52 (by omega) $$ [H2 H3]
  · iframe H2 H3
  iapply stk_join' n s (s + 8) 8 56 (by omega)
  iframe H1 H2

theorem keyQ_le {first : Bool} {bs : List UInt8} {i q : Nat} (h : keyQ first bs i = some q) : q ≤ bs.length := by
  unfold keyQ at h
  split at h
  · split at h
    · rename_i h1; simp at h; have := SerdeNextKey.getElem_lt h1; omega
    · simp at h
  · split at h
    · split at h
      · rename_i _ h1; simp at h; have := SerdeNextKey.getElem_lt h1; omega
      · simp at h
    · simp at h

theorem drop_pos {bs r : List UInt8} {q : Nat} (h : bs.drop q = r) (hq : q ≤ bs.length) : q = bs.length - r.length := by
  have := congrArg List.length h; simp at this; omega

/-- The heap inside `seenRes`, lent and given back unchanged. -/
theorem seen_lens (n maxP : Nat) (live : List (Nat × Nat)) (s : UInt32) (sA : Option WNear.AccountId) :
    seenRes (GF := GF) n maxP live s sA ⊢ ∃ (mlen F : Nat) (lv : List (Nat × Nat)), ⌜roomFor4 mlen maxP 20⌝ ∗
      heapInv n maxP mlen lv F ∗ (heapInv n maxP mlen lv F -∗ seenRes n maxP live s sA) := by
  iintro H
  cases sA with
  | none =>
    iunfold seenRes at H
    icases H with ⟨%m, %F, %b8, %⟨hr, hb8⟩, H40, H44, Hh⟩
    iexists m
    iexists F
    iexists live
    iframe Hh
    isplitr
    · ipureintro; exact hr
    iintro Hh
    iunfold seenRes
    iexists m
    iexists F
    iexists b8
    iframe H40 H44 Hh
    ipureintro; exact ⟨hr, hb8⟩
  | some a =>
    iunfold seenRes at H
    icases H with ⟨%p, %cap, H40, H44, H48, Hs⟩
    iunfold strRes at Hs
    icases Hs with ⟨%m, %F, %⟨hp, hc, hr⟩, Hb, Hbl, Hh⟩
    iexists m
    iexists F
    iexists ((p.toNat, cap.toNat) :: live)
    iframe Hh
    isplitr
    · ipureintro; exact hr
    iintro Hh
    iunfold seenRes
    iexists p
    iexists cap
    iframe H40 H44 H48
    iunfold strRes
    iexists m
    iexists F
    iframe Hb Hbl Hh
    ipureintro; exact ⟨hp, hc, hr⟩

theorem ite_pos_ent {P : Prop} [Decidable P] (h : P) (X Y : IProp GF) : (if P then X else Y) ⊢ X := by
  rw [if_pos h]

theorem depth_down : MemSet.byteOf (UInt32.ofNat (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE [128])
      else Memory.decodeLE [128]) + 4294967295) = 127 := by decide

theorem depth_up : MemSet.byteOf (UInt32.ofNat (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE [127])
      else Memory.decodeLE [127]) + 1) = 128 := by decide

/-- The cost of 228 on the object form: the prologue up to the loop (`400·c` and the whitespace before
`{`), the loop (`objCost`), the exit (`300·c`). -/
def costObj (cfg : WasmConfig) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) (N i : Nat) : Nat :=
  (400 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
    objCost cfg.regularOpCost K646 K169 K81 dv ign bs N true (i + wsLen (bs.drop i) + 1) + 300 * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **228 on the object form**: `out` gets `Ok(a)` (`strRes`), the reader past the `}`,
`remaining_depth` back at 128. -/
theorem f228_obj (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 336 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat) (Cd : IProp GF) [Persistent Cd]
    (h646 : Hyp646 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP K646 Cd)
    (h169 : Hyp169 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Cd)
    (h81 : Hyp81 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP ign K81 Cd)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (higns : ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r)
    (hstrs : ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : SerdeStructModel.objLoop "account_id" dv ign N none (bs.drop (i + wsLen (bs.drop i) + 1)) =
      some (some a, rF)) :
    SerdeNextKey.code193 n maxP inst mi A ∗ A 205 ↪[wf] FuncInst.wasm types[14]! inst f205 ∗
      A 201 ↪[wf] FuncInst.wasm types[32]! inst f201 ∗ A 193 ↪[wf] FuncInst.wasm types[11]! inst f193 ∗
      A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗ A 90 ↪[wf] FuncInst.wasm types[32]! inst f90 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
      A 77 ↪[wf] FuncInst.wasm types[0]! inst f77 ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => costObj cfg K646 K169 K81 dv ign bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - rF.length))) := by
  iintro ⟨#H193c, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77, #HCd⟩
  ihave #Hv := H193c
  iunfold SerdeNextKey.code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha193 := hm.funcs 193 (by decide)
  have ha205 := hm.funcs 205 (by decide)
  have ha201 := hm.funcs 201 (by decide)
  have ha90 := hm.funcs 90 (by decide)
  have ha77 := hm.funcs 77 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  unfold costObj
  generalize hw0 : wsLen (bs.drop i) = w0 at hb0 hloop ⊢
  generalize hj0 : i + w0 = j0 at hb0 hloop ⊢
  have hj0l := SerdeNextKey.getElem_lt hb0
  generalize hOC : objCost cfg.regularOpCost K646 K169 K81 dv ign bs N true (j0 + 1) = OC
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hd, Ht, Hkey⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h80 : (sp - 64 - 16).toNat = (sp - 64).toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  -- the frame and the stack below it
  icases stk_split n (sp.toNat - 336) 272 64 $$ Hs with ⟨S272, F64⟩
  rw [show sp.toNat - 336 + 272 = (sp - 64).toNat by omega,
    show sp.toNat - 336 = (sp - 64).toNat - 272 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨X0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 16 40 $$ F56 with ⟨R16, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16) 8 32 $$ F40 with ⟨X24, F32⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8) 4 28 $$ F32 with ⟨M32, F28⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8 + 4) 4 24 $$ F28 with ⟨M36, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8 + 4 + 4) 4 20 $$ F24 with ⟨M40, F20⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8 + 4 + 4 + 4) 8 12 $$ F20 with ⟨M44, X52⟩
  rw [show (sp - 64).toNat + 8 + 16 + 8 + 4 + 4 + 4 + 8 = (sp - 64).toNat + 52 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 + 4 + 4 + 4 = (sp - 64).toNat + 44 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 + 4 + 4 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 + 4 = (sp - 64).toNat + 36 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 = (sp - 64).toNat + 32 by omega,
    show (sp - 64).toNat + 8 + 16 = (sp - 64).toNat + 24 by omega]
  iunfold stk at M32 M36 M40 M44 R16
  icases M32 with ⟨%b32, %hb32, M32⟩
  icases M36 with ⟨%b36, %hb36, M36⟩
  icases M40 with ⟨%b40, %hb40, M40⟩
  icases M44 with ⟨%b44, %hb44, M44⟩
  icases R16 with ⟨%b16, %hb16, R16⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 36) 1 b36 (by omega) $$ M36 with ⟨M36, M37⟩
  -- up to the loop
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw0, hj0] at key
  generalize hW0 : (100 + 96 * w0) * cfg.regularOpCost = W0 at key
  rw [show (400 + 96 * w0) * cfg.regularOpCost + OC + 300 * cfg.regularOpCost + R =
    100 * cfg.regularOpCost + (W0 + (200 * cfg.regularOpCost + (OC + 300 * cfg.regularOpCost + R))) by
      rw [← hW0]; simp only [Nat.add_mul]; omega]
  generalize hE : 300 * cfg.regularOpCost = E
  simp only [f228]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (280 * cfg.regularOpCost + (OC + E + R))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb0]
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [Hd]
  ihave Hd := store1 n _ _ 127 depth_down $$ Hd
  mstep; mstep
  mstep_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j0 hj0l
    (by omega) (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (200 * cfg.regularOpCost + (OC + E + R))
  mstep; mstep; mstep [M36]
  ihave M36 := store1 n _ _ 1 (by decide) $$ M36
  mstep; mstep; mstep [M32]
  mstep; mstep; mstep [M40]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  iapply mwpi_cons
  mcredits (cfg.regularOpCost + (OC + E + R))
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := OC + E + R)
    (I := inv228 n inst mi Cg cfg.regularOpCost K646 K169 K81 dv ign maxP live out de ptr x2 x3 x4 x5 (sp - 64) bs a rF E R
      iprop(g ↦[wg] ⟨gt, .i32 (sp - 64)⟩ ∗ stk n ((sp - 64).toNat - 272) 272 ∗ vt n 1057464 idx ta (A 578) ∗
        tbl n de ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ de.toNat + 24 ] [127] ∗
        stk n (sp - 64).toNat 8 ∗ stk n ((sp - 64).toNat + 24) 8 ∗ stk n ((sp - 64).toNat + 52) 12 ∗
        n ↦[i32][ (sp - 64).toNat + 32 ] de ∗ n ↦[wms][ (sp - 64).toNat + 36 + 1 ] List.drop 1 b36 ∗
        n ↦[wms][ out.toNat ] ob)) _ _ rfl
  isplitr [Hc Hg S272 Hvt Ht Hkey Hd X0 X24 X52 M32 M37 Ho M36 R16 M40 M44 Hh Hrd]
  · imodintro
    iintro %X %l HI
    iunfold inv228 at HI
    icases HI with ⟨%N', %first, %i', %sA, %l7, %l8, %l10, %b16', %⟨hX, hf, hil, hb16', hres⟩, Hc, M36, R16, HS, Hrd,
      Hg, S272, Hvt, Ht, Hkey, Hd, X0, X24, X52, M32, M37, Ho⟩
    subst hX
    rw [hf]
    simp only [fr228]
    have hA32 : (sp - 64 + 32).toNat = (sp - 64).toNat + 32 := by simp [UInt32.toNat_add]; omega
    have hA8 : (sp - 64 + 8).toNat = (sp - 64).toNat + 8 := by simp [UInt32.toNat_add]; omega
    have hA12 : (sp - 64 + 8 ||| 4).toNat = (sp - 64).toNat + 12 := by rw [or4 _ (by rw [hA8]; omega), hA8]
    by_cases hend : bs[i' + wsLen (bs.drop i')]? = some 0x7D
    · -- `}`: 193 gives `None`, the loop ends with the field read, then `end_map` (90) and `Ok`
      obtain ⟨hfirst, hsA, hrF⟩ := SerdeStructLoop.loop_end "account_id" dv ign hres hend
      subst hfirst hsA
      rw [objCost_end _ _ _ _ _ _ bs hend]
      generalize hw : wsLen (bs.drop i') = w at hend hrF ⊢
      generalize hj : i' + w = j at hend hrF ⊢
      have hjl := SerdeNextKey.getElem_lt hend
      have s193 := SerdeNextKey.f193_end (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
        (sp - 64) (sp - 64 + 32) de ptr 0 bs i' maxP hlen hptr (by omega) (by omega) (by omega) hil
        (by rw [hw, hj]; exact hend)
      rw [hA32, hw, hj, show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega] at s193
      generalize hW : (200 + 96 * w) * cfg.regularOpCost = W at s193
      ihave #S193 := s193 $$ H193c
      clear s193
      icases stk_split n ((sp - 64).toNat - 272) 96 176 $$ S272 with ⟨S96, S176⟩
      rw [show (sp - 64).toNat - 272 + 96 = (sp - 64).toNat - 176 by omega]
      simp only [Bool.false_eq_true, if_false]
      rw [show (300 + 96 * w) * cfg.regularOpCost + E + R =
        20 * cfg.regularOpCost + ((200 + 96 * w) * cfg.regularOpCost + (80 * cfg.regularOpCost + E + R)) by
          simp only [Nat.add_mul]; omega]
      rw [hW]
      mstep; mstep; mstep; mstep
      mcall S193 using [M32 M36 Hg S176 Hrd]
      · iframe M32 M36 Hg S176 Hrd
      icases HQ with ⟨%⟨v, hrs, hv⟩, M32, M36, Hg, S176, Hrd⟩
      subst hrs
      have hv1 : v &&& 1 = 0 := by
        have : v &&& 1 = (v &&& 65281) &&& 1 := by bv_decide
        rw [this, hv]; decide
      have hv2 : v &&& 65280 = 512 := by
        have : v &&& 65280 = (v &&& 65281) &&& 65280 := by bv_decide
        rw [this, hv]; decide
      mstep; mstep; mstep
      rw [hv1]
      mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep
      rw [hv2]
      mstep; mstep
      mstep_not_taken with decide
      iunfold seenRes at HS
      icases HS with ⟨%p, %cap, S40, S44, S48, Hstr⟩
      ihave Hstr := SerdeStructArr.strRes_ne $$ Hstr
      icases Hstr with ⟨%hp, Hstr⟩
      mstep; mstep [S40]; mstep
      mstep_taken with (simp [hp])
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      ihave S44 := KeyGet.join64 n ((sp - 64).toNat + 44) cap (UInt32.ofNat a.val.utf8ByteSize) $$ [S44 S48]
      · rw [show (sp - 64).toNat + 44 + 4 = (sp - 64).toNat + 48 by omega]; iframe S44 S48
      mstep; mstep [S44]
      rw [VecFromElem.ofNat_decode_pair]
      mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      iunfold strRes at Hstr
      icases Hstr with ⟨%mlen', %F', %⟨hp', hcap, hr'⟩, Hbytes, Hblk, Hh⟩
      have hw0j := wsLen_brace hend
      have s90 := SerdeEnds.f90_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
        (sp - 64) de ptr idx bs j maxP mlen' ((p.toNat, cap.toNat) :: live) F' hlen hptr (by omega) (by omega) hjl.le hr'
      rw [hw0j, Nat.add_zero, costEnd_ok _ _ _ _ _ _ (by simpa using hend)] at s90
      ihave #S90 := s90 $$ Hv
      clear s90
      icases stk_split n ((sp - 64).toNat - 176) 80 96 $$ S176 with ⟨S80, S96b⟩
      rw [show (sp - 64).toNat - 176 + 80 = (sp - 64).toNat - 96 by omega]
      mstep; mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with decide
      mstep; mstep; mstep [Hd]
      ihave Hd := store1 n _ _ 128 depth_up $$ Hd
      mstep
      mcall S90 using [Hg S96b Hvt Hh Hrd]
      · iframe Hg S96b Hvt Hh Hrd
      icases HQ with ⟨Hg, S96b, Hvt, HQ⟩
      ihave HQ := SerdeValueSeed.resEnd_pos (by simpa using hend) $$ HQ
      icases HQ with ⟨%hrs, Hh, Hrd⟩
      subst hrs
      icases U128From.memBytes_split n ((sp - 64).toNat + 8) 4 b16' (by omega) $$ R16 with ⟨R8, R16⟩
      icases U128From.memBytes_split n ((sp - 64).toNat + 8 + 4) 4 (b16'.drop 4) (by simp; omega) $$ R16 with ⟨R12, R16⟩
      rw [show (sp - 64).toNat + 8 + 4 + 4 = (sp - 64).toNat + 16 by omega,
        show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega]
      iunfold stk at X24
      icases X24 with ⟨%b24, %hb24, X24⟩
      icases U128From.memBytes_split n ((sp - 64).toNat + 24) 4 b24 (by omega) $$ X24 with ⟨X24, X28⟩
      icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
      icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
      rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
      mstep; mstep; mstep; mstep; mstep
      mstep [R16] with (simp [UInt32.toNat_add]; omega)
      rw [VecFromElem.storeBytes_pair64]
      mstep; mstep; mstep [X24] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep; mstep [R12] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep; mstep [R8] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep_not_taken with decide
      mstep; mstep
      mstep_taken with decide
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep [O4]
      mstep; mstep; mstep; mstep; mstep [O8] with (simp [UInt32.toNat_add]; omega)
      rw [VecFromElem.storeBytes_pair64]
      mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep [O0]
      mstep; mstep; mstep; mstep [Hg]
      rw [show sp - 64 + 64 = sp by simp]
      repeat mstep
      have hjr : bs.length - rF.length = j + 1 := by rw [hrF]; simp; omega
      rw [hjr]
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe Hg Hvt Hd Ht Hkey
      isplitl [S96 S80 S96b X0 R8 R12 R16 X24 X28 M32 M36 M37 S40 S44 X52]
      · ihave S80 := stk_addr (show (sp - 64).toNat - 176 = (sp - 64).toNat - 272 + 96 by omega) $$ S80
        ihave S176 := stk_join n ((sp - 64).toNat - 272) 96 80 $$ [S96 S80]
        · iframe S96 S80
        ihave S96b := stk_addr (show (sp - 64).toNat - 96 = (sp - 64).toNat - 272 + (96 + 80) by omega) $$ S96b
        ihave S272 := stk_join n ((sp - 64).toNat - 272) (96 + 80) 96 $$ [S176 S96b]
        · iframe S176 S96b
        ihave R8 := stk_word $$ R8
        ihave R12 := stk_word $$ R12
        ihave R16 := stk_intro $$ R16
        ihave X24 := stk_word $$ X24
        ihave X28 := stk_intro $$ X28
        ihave M32 := stk_word $$ M32
        ihave M36 := stk_intro $$ M36
        ihave M37 := stk_intro $$ M37
        ihave S40 := stk_word $$ S40
        ihave S44 := stk_intro $$ S44
        rw [show (bytes32 cap ++ bytes32 (UInt32.ofNat a.val.utf8ByteSize)).length = 8 by simp,
          show (List.drop 4 b24).length = 4 by simp; omega,
          show (List.drop 1 b36).length = 3 by simp; omega,
          show ([0] : List UInt8).length = 1 by rfl,
          show (sp - 64).toNat + 24 + 4 = (sp - 64).toNat + 28 by omega,
          show (sp - 64).toNat + 36 + 1 = (sp - 64).toNat + 37 by omega]
        ihave F64 := frame64o n (sp - 64).toNat $$ [X0 R8 R12 R16 X24 X28 M32 M36 M37 S40 S44 X52]
        · iframe X0 R8 R12 R16 X24 X28 M32 M36 M37 S40 S44 X52
        ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 272 + (96 + 80 + 96) by omega) $$ F64
        iapply stk_join n ((sp - 64).toNat - 272) (96 + 80 + 96) 64
        iframe S272 F64
      iexists p
      iexists cap
      ihave O8 := KeyGet.split64 n (out.toNat + 8) cap (UInt32.ofNat a.val.utf8ByteSize) $$ O8
      icases O8 with ⟨O8, O12⟩
      rw [show out.toNat + 8 + 4 = out.toNat + 12 by omega]
      iframe O0 O4 O8 O12 Hrd
      iunfold strRes
      iexists mlen'
      iexists F'
      iframe Hbytes Hblk Hh
      ipureintro; exact ⟨hp', hcap, hr'⟩
    · -- a member: 193 reads the key (646), then 205 or 201 the value
      obtain ⟨n', q, k, rest1, hN, hq, hs, hdup, rest2, hc, hv⟩ :=
        SerdeStructLoop.loop_member "account_id" dv ign hres hend
      subst hN
      have hql := keyQ_le hq
      ihave HS := seen_lens $$ HS
      icases HS with ⟨%mh, %Fh, %lv, %hrh, Hh, HSw⟩
      iunfold tbl at Ht
      icases Ht with ⟨Hsl, He, Hw8⟩
      icases Hsl with ⟨%sl, Hsl⟩
      rw [show de.toNat + 20 = (de + 12).toNat + 8 by simp [UInt32.toNat_add]; omega]
      icases stk_split n ((sp - 64).toNat - 272) 256 16 $$ S272 with ⟨S256, S16⟩
      icases stk_split n ((sp - 64).toNat - 272) 96 160 $$ S256 with ⟨S96, S160⟩
      rw [show (sp - 64).toNat - 272 + 256 = (sp - 64 - 16).toNat by omega,
        show (sp - 64).toNat - 272 + 96 = (sp - 64).toNat - 176 by omega]
      iunfold stk at S16
      icases S16 with ⟨%ob16, %hob16, S16⟩
      have s646 := h646 (d + 2) (sp - 64) ob16 q k rest1 mh Fh lv (by omega) hob16 (by omega) hql hrh hs
      ihave #S646 := s646 $$ HCd
      clear s646
      have s193 := SerdeNextKey.f193_key (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
        (sp - 64) (sp - 64 + 32) de ptr first ob16 bs k.toUTF8.toList i' q sl maxP hob16 hlen hptr (by omega) (by omega)
        (by omega) hil hq
        iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mh lv Fh ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width)
        (K646 q)
        iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mh lv Fh ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗
          ∃ q', ⌜bs.drop q' = rest1 ∧ q' ≤ bs.length⌝ ∗ rd n de ptr bs q')
      rw [hA32, show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega] at s193
      generalize hKk : (800 + 96 * keyWs first bs i' + SerdeKey.cost194) * cfg.regularOpCost + K646 q = Kk at s193
      ihave #S193 := s193 $$ [H193c S646]
      · iframe H193c S646
      clear s193
      -- the positions after the key, and the cost of this member
      have hsuf := hstrs q k rest1 hql hs
      generalize hq1 : bs.length - rest1.length = q1 at hsuf
      have hq1l : q1 ≤ bs.length := by omega
      obtain ⟨hcol, hrest2⟩ : bs[q1 + wsLen (bs.drop q1)]? = some 0x3A ∧ rest2 = bs.drop (q1 + wsLen (bs.drop q1) + 1) := by
        unfold WNear.JsonFuel.colonAt at hc
        split at hc
        · rename_i r hsk
          rw [← hsuf] at hsk
          obtain ⟨h1, h2⟩ := SerdeStructLoop.skip_drop_cons hsk
          simp only [Option.some.injEq] at hc
          exact ⟨h1, hc ▸ h2⟩
        · simp at hc
      generalize hw1 : wsLen (bs.drop q1) = w1 at hcol hrest2
      subst hrest2
      have hvl : q1 + w1 + 1 ≤ bs.length := by have := SerdeNextKey.getElem_lt hcol; omega
      have hcost : ∃ KV OCn, objCost cfg.regularOpCost K646 K169 K81 dv ign bs (n' + 1) first i' =
          (1200 + 96 * (keyWs first bs i' + w1) + SerdeKey.cost194) * cfg.regularOpCost + K646 q + (KV + OCn) := by
        rcases hv with ⟨hk, a', r3, hdv, -⟩ | ⟨hk, r3, hig, -⟩
        · refine ⟨K169 (q1 + w1 + 1), objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length), ?_⟩
          rw [objCost_field _ _ _ _ _ _ bs hend hq hs hk (by rw [hq1, hw1]; exact hdv), hq1, hw1]
        · refine ⟨K81 (q1 + w1 + 1), objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length), ?_⟩
          rw [objCost_ign _ _ _ _ _ _ bs hend hq hs hk (by rw [hq1, hw1]; exact hig), hq1, hw1]
      obtain ⟨KV, OCn, hOCe⟩ := hcost
      rw [hOCe, show (1200 + 96 * (keyWs first bs i' + w1) + SerdeKey.cost194) * cfg.regularOpCost + K646 q +
          (KV + OCn) + E + R =
        60 * cfg.regularOpCost + (Kk + (140 * cfg.regularOpCost + ((200 + 96 * w1) * cfg.regularOpCost + (KV + (OCn + E + R))))) by
          rw [← hKk]; simp only [Nat.add_mul, Nat.mul_add]; omega]
      mstep; mstep; mstep; mstep
      mcall S193 using [M32 M36 Hg S160 S16 Hrd Hsl Hkey Hvt Hh He Hw8]
      · iframe M32 M36 Hg S160 S16 Hrd Hsl Hkey Hvt Hh He Hw8
      icases HQ with ⟨%hrs, M32, M36, Hg, S176, Hkey, Hvt, Hh, He, Hw8, Hsl, %q', %⟨hq', hq'l⟩, Hrd⟩
      subst hrs
      have hq'e : q1 = q' := by rw [← hq1]; exact (drop_pos hq' hq'l).symm
      subst hq'e
      mcredits (150 * cfg.regularOpCost + ((200 + 96 * w1) * cfg.regularOpCost + (KV + (OCn + E + R))))
      ihave HS := HSw $$ Hh
      have hf1 : fieldOf k.toUTF8.toList &&& 1 = 0 := by unfold fieldOf; split <;> decide
      have hf2 : fieldOf k.toUTF8.toList &&& 65280 ≠ 512 := by unfold fieldOf; split <;> decide
      mstep; mstep; mstep
      rw [hf1]
      mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep
      generalize hf65 : fieldOf k.toUTF8.toList &&& 65280 = f65 at hf2
      mstep; mstep
      mstep_taken with (simp [Numeric.bool, Numeric.irelop64, hf2])
      -- the stack for the value readers, the tables back
      ihave S176 := stk_addr (show (sp - 64).toNat - 176 = (sp - 64).toNat - 272 + 96 by omega) $$ S176
      ihave S272 := stk_join n ((sp - 64).toNat - 272) 96 176 $$ [S96 S176]
      · iframe S96 S176
      icases stk_split n ((sp - 64).toNat - 272) 16 256 $$ S272 with ⟨S16, S256⟩
      icases stk_split n ((sp - 64).toNat - 272 + 16) 160 96 $$ S256 with ⟨S160, S96⟩
      rw [show (sp - 64).toNat - 272 + 16 + 160 = (sp - 64).toNat - 96 by omega,
        show (sp - 64).toNat - 272 + 16 = (sp - 64).toNat - 256 by omega]
      ihave Ht : tbl n de $$ [Hsl He Hw8]
      · iunfold tbl
        iframe He Hw8
        iexists 0
        rw [show de.toNat + 20 = (de + 12).toNat + 8 by simp [UInt32.toNat_add]; omega]
        iexact Hsl
      rcases hv with ⟨hk, a', r3, hdv, hres'⟩ | ⟨hk, r3, hig, hres'⟩
      · -- `account_id`: 205 (169), then the field moved to `s + 40`
        have hsA : sA = none := by
          cases sA with
          | none => rfl
          | some x => exact absurd ⟨hk, rfl⟩ hdup
        subst hsA
        have hk2 : fieldOf k.toUTF8.toList &&& 256 = 0 := by
          unfold fieldOf; rw [if_pos ((key_iff k).mpr hk)]; decide
        mstep; mstep; mstep; mstep
        rw [hk2]
        mstep
        mstep_taken with decide
        iunfold seenRes at HS
        icases HS with ⟨%mlen0, %F0, %b8, %⟨hr0, hb8⟩, S40, S44, Hh⟩
        mstep; mstep; mstep [S40]; mstep
        mstep_taken with decide
        have s169 := spec169_205 (GF := GF) cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Cd h169 (d + 2)
          (by omega) (sp - 64) (sp - 64 + 8) b16' hb16' (by omega) (by omega) (q1 + w1 + 1) a' r3 hvl mlen0 F0 live hr0 hdv
        rw [hA8] at s169
        ihave #S169 := s169 $$ HCd
        clear s169
        have s205 := SerdeValueSeed.f205_of_169 (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm
          (by omega) Cg gt (sp - 64) (sp - 64 + 8) (sp - 64 + 32) de ptr idx b16' bs q1 maxP mlen0 live F0 hb16'
          (by omega) hlen hptr (by omega) (by omega) (by omega) hq1l hr0
          iprop(stk n ((sp - 64).toNat - 256) 160 ∗ tbl n de) (K169 (q1 + w1 + 1))
          iprop(g ↦[wg] ⟨gt, .i32 (sp - 64)⟩ ∗ stk n ((sp - 64).toNat - 256) 256 ∗ vt n 1057464 idx ta (A 578) ∗
            tbl n de ∗ ∃ (p cap : UInt32), n ↦[i32][ (sp - 64).toNat + 8 ] 0 ∗ n ↦[i32][ (sp - 64).toNat + 8 + 4 ] p ∗
            n ↦[i32][ (sp - 64).toNat + 8 + 8 ] cap ∗
            n ↦[i32][ (sp - 64).toNat + 8 + 12 ] (UInt32.ofNat a'.val.utf8ByteSize) ∗
            strRes n maxP live a' p cap ∗ rd n de ptr bs (bs.length - r3.length))
        rw [hw1, hA8, hA32, costEnd_ok _ _ _ _ _ _ hcol, if_pos hcol] at s205
        ihave #S205 := s205 $$ [Hv F89 F169 S169]
        · iframe Hv F89 F169 S169
        clear s205
        have he := objCost_field cfg.regularOpCost K646 K169 K81 dv ign bs (n := n') hend hq hs hk
          (by rw [hq1, hw1]; exact hdv)
        rw [hOCe, hq1, hw1] at he
        have hKV : KV + OCn = K169 (q1 + w1 + 1) +
            objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length) := by omega
        mcredits (120 * cfg.regularOpCost + ((200 + 96 * w1) * cfg.regularOpCost + (K169 (q1 + w1 + 1) +
          (objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length) + E + R))))
        have e1 : (40 + (200 + 96 * w1)) * cfg.regularOpCost = 40 * cfg.regularOpCost + (200 + 96 * w1) * cfg.regularOpCost := by
          rw [Nat.add_mul]
        mstep; mstep; mstep; mstep; mstep; mstep
        mcall S205 using [M32 Hg S96 Hvt Hh R16 Hrd S160 Ht]
        · iframe M32 Hg S96 Hvt Hh R16 Hrd S160 Ht
        icases HQ with ⟨%hrs, M32, HQ⟩
        subst hrs
        ihave HQ := ite_pos_ent hcol $$ HQ
        icases HQ with ⟨Hg, S256, Hvt, Ht, %p, %cap, W8, W12, W16, W20, Hstr, Hrd⟩
        mcredits (60 * cfg.regularOpCost +
          (objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length) + E + R))
        mstep; mstep; mstep [W8]; mstep; mstep
        mstep_taken with decide
        have hA40 : (sp - 64 + 40).toNat = (sp - 64).toNat + 40 := by simp [UInt32.toNat_add]; omega
        have s77 := f77_none (GF := GF) cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg (sp - 64 + 40) (by omega)
        rw [hA40] at s77
        mstep; mstep; mstep
        mcall s77 using [S40]
        · iframe S40
        icases HQ with ⟨%hrs, S40⟩
        subst hrs
        icases U128From.memBytes_split n ((sp - 64).toNat + 44) 4 b8 (by omega) $$ S44 with ⟨S44, S48⟩
        rw [show (sp - 64).toNat + 44 + 4 = (sp - 64).toNat + 48 by omega]
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep [W20] with (simp [UInt32.toNat_add]; omega)
        mstep [S48] with (simp [UInt32.toNat_add]; omega)
        ihave W12 := KeyGet.join64 n ((sp - 64).toNat + 8 + 4) p cap $$ [W12 W16]
        · rw [show (sp - 64).toNat + 8 + 4 + 4 = (sp - 64).toNat + 8 + 8 by omega]; iframe W12 W16
        ihave S40 := U128From.memBytes_join n ((sp - 64).toNat + 40) 4 (bytes32 0) (b8.take 4) (by simp) $$ [S40 S44]
        · rw [show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega]; iframe S40 S44
        mstep; mstep
        mstep [W12] with (simp [UInt32.toNat_add]; omega)
        rw [VecFromElem.ofNat_decode_pair]
        mstep [S40] with (simp [UInt32.toNat_add]; omega)
        rw [VecFromElem.storeBytes_pair64]
        mstep
        have hr3 := hdvs (q1 + w1 + 1) a' r3 hvl hdv
        have hr3l : bs.length - r3.length ≤ bs.length := by omega
        simp only [Post.mloop, List.reverse_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iunfold inv228
        iexists n'
        iexists false
        iexists bs.length - r3.length
        iexists some a'
        iexists fieldOf k.toUTF8.toList
        iexists l8
        iexists l10
        iexists bytes32 0 ++ ((bytes32 p ++ bytes32 cap) ++ bytes32 (UInt32.ofNat a'.val.utf8ByteSize))
        rw [show (if false = true then (1 : UInt8) else 0) = 0 from rfl]
        iframe M36 Hrd Hg Hvt Hkey Hd X0 X24 X52 M32 M37 Ho Ht
        isplitr [Hc S16 S256 W8 W12 W20 S40 S48 Hstr]
        · ipureintro
          refine ⟨rfl, rfl, hr3l, by simp, ?_⟩
          rw [hr3]; exact hres'
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        isplitl [W8 W12 W20]
        · ihave W12 := U128From.memBytes_join n ((sp - 64).toNat + 8 + 4) 8 (bytes32 p ++ bytes32 cap)
            (bytes32 (UInt32.ofNat a'.val.utf8ByteSize)) (by simp) $$ [W12 W20]
          · rw [show (sp - 64).toNat + 8 + 4 + 8 = (sp - 64).toNat + 8 + 12 by omega]; iframe W12 W20
          iapply U128From.memBytes_join n ((sp - 64).toNat + 8) 4 (bytes32 0) _ (by simp)
          iframe W8 W12
        isplitl [S40 S48 Hstr]
        · iunfold seenRes
          iexists p
          iexists cap
          ihave S40 := KeyGet.split64 n ((sp - 64).toNat + 40) p cap $$ S40
          icases S40 with ⟨S40, S44⟩
          rw [show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega]
          iframe S40 S44 S48 Hstr
        ihave S256 := stk_addr (show (sp - 64).toNat - 256 = (sp - 64).toNat - 272 + 16 by omega) $$ S256
        iapply stk_join n ((sp - 64).toNat - 272) 16 256
        iframe S16 S256
      · -- another key: 201 (81)
        have hk' : fieldOf k.toUTF8.toList = 256 := by
          unfold fieldOf; rw [if_neg (fun h => hk ((key_iff k).mp h))]
        have hk2 : fieldOf k.toUTF8.toList &&& 256 = 256 := by rw [hk']; decide
        mstep; mstep; mstep; mstep
        rw [hk2]
        mstep
        mstep_not_taken with decide
        ihave HS := seen_lens $$ HS
        icases HS with ⟨%mh2, %Fh2, %lv2, %hrh2, Hh, HSw⟩
        have s81 := h81 (d + 2) (sp - 64) (q1 + w1 + 1) r3 mh2 Fh2 lv2 (by omega) (by omega) hvl hrh2 hig
        ihave #S81 := s81 $$ HCd
        clear s81
        have s201 := SerdeValueSeed.f201_of_81 (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm
          (by omega) Cg gt (sp - 64) (sp - 64 + 32) de ptr idx bs q1 maxP mh2 lv2 Fh2 hlen hptr (by omega) (by omega)
          (by omega) hq1l hrh2 iprop(stk n ((sp - 64).toNat - 256) 160 ∗ tbl n de) (K81 (q1 + w1 + 1))
          (fun rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 64)⟩ ∗
            stk n ((sp - 64).toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mh2 lv2 Fh2 ∗
            rd n de ptr bs (bs.length - r3.length) ∗ stk n ((sp - 64).toNat - 256) 160 ∗ tbl n de))
        rw [hw1, hA32, costEnd_ok _ _ _ _ _ _ hcol, if_pos hcol] at s201
        ihave #S201 := s201 $$ [Hv F89 F81 S81]
        · iframe Hv F89 F81 S81
        clear s201
        have he := objCost_ign cfg.regularOpCost K646 K169 K81 dv ign bs (n := n') hend hq hs hk
          (by rw [hq1, hw1]; exact hig)
        rw [hOCe, hq1, hw1] at he
        have hKV : KV + OCn = K81 (q1 + w1 + 1) +
            objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length) := by omega
        mcredits (100 * cfg.regularOpCost + ((200 + 96 * w1) * cfg.regularOpCost + (K81 (q1 + w1 + 1) +
          (objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length) + E + R))))
        have e1 : (40 + (200 + 96 * w1)) * cfg.regularOpCost = 40 * cfg.regularOpCost + (200 + 96 * w1) * cfg.regularOpCost := by
          rw [Nat.add_mul]
        mstep; mstep; mstep
        mcall S201 using [M32 Hg S96 Hvt Hh Hrd S160 Ht]
        · iframe M32 Hg S96 Hvt Hh Hrd S160 Ht
        icases HQ with ⟨M32, HQ⟩
        ihave HQ := ite_pos_ent hcol $$ HQ
        icases HQ with ⟨%hrs, Hg, S96, Hvt, Hh, Hrd, S160, Ht⟩
        subst hrs
        ihave HS := HSw $$ Hh
        mstep; mstep
        mstep_taken with decide
        have hr3 := higns (q1 + w1 + 1) r3 hvl hig
        have hr3l : bs.length - r3.length ≤ bs.length := by omega
        simp only [Post.mloop, List.reverse_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iunfold inv228
        iexists n'
        iexists false
        iexists bs.length - r3.length
        iexists sA
        iexists fieldOf k.toUTF8.toList
        iexists 0
        iexists l10
        iexists b16'
        rw [show (if false = true then (1 : UInt8) else 0) = 0 from rfl]
        iframe M36 R16 HS Hrd Hg Hvt Hkey Hd X0 X24 X52 M32 M37 Ho Ht
        isplitr [Hc S16 S160 S96]
        · ipureintro
          refine ⟨rfl, rfl, hr3l, hb16', ?_⟩
          rw [hr3]; exact hres'
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        ihave S160 := stk_addr (show (sp - 64).toNat - 256 = (sp - 64).toNat - 272 + 16 by omega) $$ S160
        ihave S176 := stk_join n ((sp - 64).toNat - 272) 16 160 $$ [S16 S160]
        · iframe S16 S160
        ihave S96 := stk_addr (show (sp - 64).toNat - 96 = (sp - 64).toNat - 272 + (16 + 160) by omega) $$ S96
        iapply stk_join n ((sp - 64).toNat - 272) (16 + 160) 96
        iframe S176 S96
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  iunfold inv228
  iexists N
  iexists true
  iexists j0 + 1
  iexists none
  iexists optByte (some 123)
  iexists (UInt32.ofNat (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE [128])
    else Memory.decodeLE [128]) + 4294967295)
  iexists 0
  iexists b16
  rw [hOC, show (if true = true then (1 : UInt8) else 0) = 1 from rfl]
  iframe Hc M36 R16 Hrd Hg S272 Hvt Ht Hkey Hd X0 X24 X52 M32 M37 Ho
  isplitr [M40 M44 Hh]
  · ipureintro
    refine ⟨rfl, rfl, by omega, hb16, ?_⟩
    simpa [loopRes] using hloop
  iunfold seenRes
  iexists mlen
  iexists F
  iexists b44
  iframe M40 M44 Hh
  ipureintro; exact ⟨hr, hb44⟩

end Run

end WNear.Binary.SerdeStructObj
