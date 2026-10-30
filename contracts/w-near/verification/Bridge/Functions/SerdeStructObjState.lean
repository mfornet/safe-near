import Bridge.Functions.SerdeStructObjRun
import Bridge.Functions.SerdeEndMapSuccess

/-!
# The object struct loop with changing member state

`J i seen` owns the heap, scratch and retained String bytes at reader position
`i`. Full key/value/ignore contracts move that state across each member; the
loop owns its local descriptor words separately.
-/

namespace WNear.Binary.SerdeStructObjState

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
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169 roomS stk_join' store1)
open WNear.Binary.SerdeStructObj (fr228 frame64o or4 wsLen_brace keyQ_le drop_pos key_iff
  objCost objCost_end objCost_field objCost_ign depth_down depth_up f77_none)
open WNear.SerdeStructLoop (loopRes)
open NearInterface.Json

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Member state, excluding the local `Option<ValidAccountId>` descriptor. -/
abbrev MemberState := Nat → Option (WNear.AccountId × UInt32 × UInt32) → IProp GF

/-- The saved account-id descriptor and its independently changing member state. -/
def seenRes (n : Nat) (s : UInt32) (J : MemberState (GF := GF)) (i : Nat) : Option WNear.AccountId → IProp GF
  | none => iprop(∃ b8 : List UInt8, ⌜b8.length = 8⌝ ∗ n ↦[i32][ s.toNat + 40 ] 0 ∗
      n ↦[wms][ s.toNat + 44 ] b8 ∗ J i none)
  | some a => iprop(∃ (p cap : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ s.toNat + 40 ] p ∗
      n ↦[i32][ s.toNat + 44 ] cap ∗ n ↦[i32][ s.toNat + 48 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
      J i (some (a, p, cap)))

/-- A key call advances the cursor and member state without changing the saved descriptor. -/
def KeyHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g Cg : Nat)
    (gt : GlobalType) (de ptr : UInt32) (bs : List UInt8) (K : Nat → Nat) (J : MemberState (GF := GF))
    (Cd : IProp GF) : Prop :=
  ∀ (d : Nat) (s : UInt32) (first : Bool) (i q : Nat) (key : String) (rest : List UInt8)
    (seen : Option WNear.AccountId),
    d + 40 < lim.maxCallDepth → 304 ≤ s.toNat → s.toNat + 64 ≤ 2 ^ 32 → i ≤ bs.length →
    keyQ first bs i = some q → stringBody (bs.drop q) [] = some (some key, rest) →
    Cd ⊢ MFunSpec cfg lim d types[11]! inst mi f193 Cg
      (fun args => iprop(⌜args = [.i32 (s + 32)]⌝ ∗ n ↦[i32][ s.toNat + 32 ] de ∗
        n ↦[wms][ s.toNat + 36 ] [if first then 1 else 0] ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 304) 304 ∗ rd n de ptr bs i ∗ seenRes n s J i seen))
      (fun _ => (572 + 96 * keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost + K q)
      (fun _ rs => iprop(⌜rs = [.i64 (fieldOf key.toUTF8.toList)]⌝ ∗ n ↦[i32][ s.toNat + 32 ] de ∗
        n ↦[wms][ s.toNat + 36 ] [0] ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗
        rd n de ptr bs (bs.length - rest.length) ∗ seenRes n s J (bs.length - rest.length) seen))

/-- The full colon/value call installs the field and its changed member state. -/
def ValueHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g Cg : Nat)
    (gt : GlobalType) (de ptr : UInt32) (bs : List UInt8)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (K : Nat → Nat)
    (J : MemberState (GF := GF)) (Cd : IProp GF) : Prop :=
  ∀ (d : Nat) (s : UInt32) (ob : List UInt8) (i : Nat) (a : WNear.AccountId) (rest : List UInt8),
    d + 40 < lim.maxCallDepth → 304 ≤ s.toNat → s.toNat + 64 ≤ 2 ^ 32 → ob.length = 16 → i ≤ bs.length →
    bs[i + wsLen (bs.drop i)]? = some 0x3A → dv (bs.drop (i + wsLen (bs.drop i) + 1)) = some (a, rest) →
    Cd ⊢ MFunSpec cfg lim d types[14]! inst mi f205 Cg
      (fun args => iprop(⌜args = [.i32 (s + 8), .i32 (s + 32)]⌝ ∗ n ↦[i32][ s.toNat + 32 ] de ∗
        g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗
        n ↦[wms][ (s + 8).toNat ] ob ∗ rd n de ptr bs i ∗ J i none))
      (fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + K (i + wsLen (bs.drop i) + 1))
      (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ s.toNat + 32 ] de ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 304) 304 ∗ rd n de ptr bs (bs.length - rest.length) ∗
        ∃ (p cap : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ (s + 8).toNat ] 0 ∗ n ↦[i32][ (s + 8).toNat + 4 ] p ∗
          n ↦[i32][ (s + 8).toNat + 8 ] cap ∗ n ↦[i32][ (s + 8).toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
          J (bs.length - rest.length) (some (a, p, cap))))

/-- An ignored member advances the state while retaining a previously read account id. -/
def IgnoreHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g Cg : Nat)
    (gt : GlobalType) (de ptr : UInt32) (bs : List UInt8)
    (ign : List UInt8 → Option (Unit × List UInt8)) (K : Nat → Nat)
    (J : MemberState (GF := GF)) (Cd : IProp GF) : Prop :=
  ∀ (d : Nat) (s : UInt32) (i : Nat) (rest : List UInt8) (seen : Option WNear.AccountId),
    d + 40 < lim.maxCallDepth → 304 ≤ s.toNat → s.toNat + 64 ≤ 2 ^ 32 → i ≤ bs.length →
    bs[i + wsLen (bs.drop i)]? = some 0x3A → ign (bs.drop (i + wsLen (bs.drop i) + 1)) = some ((), rest) →
    Cd ⊢ MFunSpec cfg lim d types[32]! inst mi f201 Cg
      (fun args => iprop(⌜args = [.i32 (s + 32)]⌝ ∗ n ↦[i32][ s.toNat + 32 ] de ∗
        g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗
        rd n de ptr bs i ∗ seenRes n s J i seen))
      (fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + K (i + wsLen (bs.drop i) + 1))
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ s.toNat + 32 ] de ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 304) 304 ∗ rd n de ptr bs (bs.length - rest.length) ∗
        seenRes n s J (bs.length - rest.length) seen))

/-- The object invariant keeps the member state at the actual reader cursor. -/
def inv228 (n inst : Nat) (mi : ModuleInst) (Cg c : Nat) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (J : MemberState (GF := GF)) (out de ptr x2 x3 x4 x5 s : UInt32) (bs : List UInt8)
    (a : WNear.AccountId) (rF : List UInt8) (E R : Nat) (Fr : IProp GF) : List Wasm.Value → Frame → IProp GF :=
  fun X f => iprop(∃ (N : Nat) (first : Bool) (i : Nat) (sA : Option WNear.AccountId) (l7 : UInt64) (l8 l10 : UInt32)
      (b16 : List UInt8),
    ⌜X = [] ∧ f = fr228 inst mi out de x2 x3 x4 x5 s l7 l8 l10 ∧ i ≤ bs.length ∧ b16.length = 16 ∧
      loopRes "account_id" dv ign N first sA (bs.drop i) = some (some a, rF)⌝ ∗
    credits Cg (objCost c K646 K169 K81 dv ign bs N first i + E + R) ∗
    n ↦[wms][ s.toNat + 36 ] [if first then 1 else 0] ∗ n ↦[wms][ s.toNat + 8 ] b16 ∗
    seenRes n s J i sA ∗ rd n de ptr bs i ∗ Fr)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **228 on the object form**: `out` gets `Ok(a)` with changed member state, the reader past the `}`,
`remaining_depth` back at 128. -/
theorem f228_obj_state (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP : Nat) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat) (J : MemberState (GF := GF)) (Cd : IProp GF) [Persistent Cd]
    (h646 : KeyHyp cfg lim inst mi n g Cg gt de ptr bs K646 J Cd)
    (h169 : ValueHyp cfg lim inst mi n g Cg gt de ptr bs dv K169 J Cd)
    (h81 : IgnoreHyp cfg lim inst mi n g Cg gt de ptr bs ign K81 J Cd)
    (hmono : ∀ i j seen, i ≤ j → J i seen ⊢ J j seen)
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
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ J (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 dv ign bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            ⌜p ≠ 0⌝ ∗ J (bs.length - rF.length) (some (a, p, cap)) ∗ rd n de ptr bs (bs.length - rF.length))) := by
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
  unfold SerdeStructObj.costObj
  generalize hw0 : wsLen (bs.drop i) = w0 at hb0 hloop ⊢
  generalize hj0 : i + w0 = j0 at hb0 hloop ⊢
  have hj0l := SerdeNextKey.getElem_lt hb0
  generalize hOC : objCost cfg.regularOpCost K646 K169 K81 dv ign bs N true (j0 + 1) = OC
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hrd, Hd, HJ⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h80 : (sp - 64 - 16).toNat = (sp - 64).toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  -- the frame and the stack below it
  icases stk_split n (sp.toNat - 368) 304 64 $$ Hs with ⟨S304, F64⟩
  rw [show sp.toNat - 368 + 304 = (sp - 64).toNat by omega,
    show sp.toNat - 368 = (sp - 64).toNat - 304 by omega]
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
    (I := inv228 n inst mi Cg cfg.regularOpCost K646 K169 K81 dv ign J out de ptr x2 x3 x4 x5 (sp - 64) bs a rF E R
      iprop(g ↦[wg] ⟨gt, .i32 (sp - 64)⟩ ∗ stk n ((sp - 64).toNat - 304) 304 ∗ n ↦[wms][ de.toNat + 24 ] [127] ∗
        stk n (sp - 64).toNat 8 ∗ stk n ((sp - 64).toNat + 24) 8 ∗ stk n ((sp - 64).toNat + 52) 12 ∗
        n ↦[i32][ (sp - 64).toNat + 32 ] de ∗ n ↦[wms][ (sp - 64).toNat + 36 + 1 ] List.drop 1 b36 ∗
        n ↦[wms][ out.toNat ] ob)) _ _ rfl
  isplitr [Hc Hg S304 Hd X0 X24 X52 M32 M37 Ho M36 R16 M40 M44 HJ Hrd]
  · imodintro
    iintro %X %l HI
    iunfold inv228 at HI
    icases HI with ⟨%N', %first, %i', %sA, %l7, %l8, %l10, %b16', %⟨hX, hf, hil, hb16', hres⟩, Hc, M36, R16, HS, Hrd,
      Hg, S304, Hd, X0, X24, X52, M32, M37, Ho⟩
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
      icases stk_split n ((sp - 64).toNat - 304) 128 176 $$ S304 with ⟨S128, S176⟩
      rw [show (sp - 64).toNat - 304 + 128 = (sp - 64).toNat - 176 by omega]
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
        have : v &&& 1 = (v &&& 65281) &&& 1 := by rw [UInt64.and_assoc]; rfl
        rw [this, hv]; decide
      have hv2 : v &&& 65280 = 512 := by
        have : v &&& 65280 = (v &&& 65281) &&& 65280 := by rw [UInt64.and_assoc]; rfl
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
      icases HS with ⟨%p, %cap, %hp, S40, S44, S48, HJ⟩
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
      have hw0j := wsLen_brace hend
      have s90 := SerdeEndMapSuccess.f90_close (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
        (by omega) Cg gt (sp - 64) de ptr bs j (by omega) (by omega) (by omega) hjl.le
        (by rw [hw0j, Nat.add_zero]; exact hend)
      rw [hw0j, Nat.add_zero] at s90
      ihave #S90 := s90 $$ [F332 F333 F339 Hi]
      · iframe F332 F333 F339 Hi
      clear s90
      icases stk_split n ((sp - 64).toNat - 176) 80 96 $$ S176 with ⟨S80, S96b⟩
      rw [show (sp - 64).toNat - 176 + 80 = (sp - 64).toNat - 96 by omega]
      mstep; mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with decide
      mstep; mstep; mstep [Hd]
      ihave Hd := store1 n _ _ 128 depth_up $$ Hd
      mstep
      mcall S90 using [Hg Hrd]
      · iframe Hg Hrd
      icases HQ with ⟨%hrs, Hg, Hrd⟩
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
      iframe Hg Hd
      isplitl [S128 S80 S96b X0 R8 R12 R16 X24 X28 M32 M36 M37 S40 S44 X52]
      · ihave S80 := stk_addr (show (sp - 64).toNat - 176 = (sp - 64).toNat - 304 + 128 by omega) $$ S80
        ihave S176 := stk_join n ((sp - 64).toNat - 304) 128 80 $$ [S128 S80]
        · iframe S128 S80
        ihave S96b := stk_addr (show (sp - 64).toNat - 96 = (sp - 64).toNat - 304 + (128 + 80) by omega) $$ S96b
        ihave S304 := stk_join n ((sp - 64).toNat - 304) (128 + 80) 96 $$ [S176 S96b]
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
        ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 304 + (128 + 80 + 96) by omega) $$ F64
        iapply stk_join n ((sp - 64).toNat - 304) (128 + 80 + 96) 64
        iframe S304 F64
      iexists p
      iexists cap
      ihave O8 := KeyGet.split64 n (out.toNat + 8) cap (UInt32.ofNat a.val.utf8ByteSize) $$ O8
      icases O8 with ⟨O8, O12⟩
      rw [show out.toNat + 8 + 4 = out.toNat + 12 by omega]
      iframe O0 O4 O8 O12 Hrd
      isplitr
      · ipureintro; exact hp
      iapply hmono i' (j + 1) (some (a, p, cap)) (by omega)
      iexact HJ
    · -- a member: 193 reads the key (646), then 205 or 201 the value
      obtain ⟨n', q, k, rest1, hN, hq, hs, hdup, rest2, hc, hv⟩ :=
        SerdeStructLoop.loop_member "account_id" dv ign hres hend
      subst hN
      have hql := keyQ_le hq
      have s193 := h646 (d + 1) (sp - 64) first i' q k rest1 sA
        (by omega) (by omega) (by omega) hil hq hs
      generalize hKk : (572 + 96 * keyWs first bs i' + SerdeKey.cost194) * cfg.regularOpCost + K646 q = Kk at s193
      ihave #S193 := s193 $$ HCd
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
          (942 + 96 * (keyWs first bs i' + w1) + SerdeKey.cost194) * cfg.regularOpCost + K646 q + (KV + OCn) := by
        rcases hv with ⟨hk, a', r3, hdv, -⟩ | ⟨hk, r3, hig, -⟩
        · refine ⟨K169 (q1 + w1 + 1), objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length), ?_⟩
          rw [objCost_field _ _ _ _ _ _ bs hend hq hs hk (by rw [hq1, hw1]; exact hdv), hq1, hw1]
        · refine ⟨K81 (q1 + w1 + 1), objCost cfg.regularOpCost K646 K169 K81 dv ign bs n' false (bs.length - r3.length), ?_⟩
          rw [objCost_ign _ _ _ _ _ _ bs hend hq hs hk (by rw [hq1, hw1]; exact hig), hq1, hw1]
      obtain ⟨KV, OCn, hOCe⟩ := hcost
      rw [hOCe, show (942 + 96 * (keyWs first bs i' + w1) + SerdeKey.cost194) * cfg.regularOpCost + K646 q +
          (KV + OCn) + E + R =
        30 * cfg.regularOpCost + (Kk + (140 * cfg.regularOpCost + ((200 + 96 * w1) * cfg.regularOpCost + (KV + (OCn + E + R))))) by
          rw [← hKk]; simp only [Nat.add_mul, Nat.mul_add]; omega]
      mstep; mstep; mstep; mstep
      mcall S193 using [M32 M36 Hg S304 Hrd HS]
      · iframe M32 M36 Hg S304 Hrd HS
      icases HQ with ⟨%hrs, M32, M36, Hg, S304, Hrd, HS⟩
      subst hrs
      mcredits (150 * cfg.regularOpCost + ((200 + 96 * w1) * cfg.regularOpCost + (KV + (OCn + E + R))))
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
        icases HS with ⟨%b8, %hb8, S40, S44, HJ⟩
        mstep; mstep; mstep [S40]; mstep
        mstep_taken with decide
        have s205 := h169 (d + 1) (sp - 64) b16' q1 a' r3
          (by omega) (by omega) (by omega) hb16' hq1l
          (by rw [hw1]; exact hcol) (by rw [hw1]; exact hdv)
        rw [hw1, hA8] at s205
        ihave #S205 := s205 $$ HCd
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
        have e2 : (240 + 96 * w1) * cfg.regularOpCost = 40 * cfg.regularOpCost + (200 + 96 * w1) * cfg.regularOpCost := by
          simp only [Nat.add_mul]; omega
        mstep; mstep; mstep; mstep; mstep; mstep
        mcall S205 using [M32 Hg S304 R16 Hrd HJ]
        · iframe M32 Hg S304 R16 Hrd HJ
        icases HQ with ⟨%hrs, M32, Hg, S304, Hrd, %p, %cap, %hp, W8, W12, W16, W20, HJ⟩
        subst hrs
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
        iframe M36 Hrd Hg Hd X0 X24 X52 M32 M37 Ho
        isplitr [Hc S304 W8 W12 W20 S40 S48 HJ]
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
        isplitl [S40 S48 HJ]
        · iunfold seenRes
          iexists p
          iexists cap
          ihave S40 := KeyGet.split64 n ((sp - 64).toNat + 40) p cap $$ S40
          icases S40 with ⟨S40, S44⟩
          rw [show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega]
          isplitr
          · ipureintro; exact hp
          iframe S40 S44 S48 HJ
        iexact S304
      · -- another key: 201 (81)
        have hk' : fieldOf k.toUTF8.toList = 256 := by
          unfold fieldOf; rw [if_neg (fun h => hk ((key_iff k).mp h))]
        have hk2 : fieldOf k.toUTF8.toList &&& 256 = 256 := by rw [hk']; decide
        mstep; mstep; mstep; mstep
        rw [hk2]
        mstep
        mstep_not_taken with decide
        have s201 := h81 (d + 1) (sp - 64) q1 r3 sA
          (by omega) (by omega) (by omega) hq1l
          (by rw [hw1]; exact hcol) (by rw [hw1]; exact hig)
        rw [hw1] at s201
        ihave #S201 := s201 $$ HCd
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
        have e2 : (240 + 96 * w1) * cfg.regularOpCost = 40 * cfg.regularOpCost + (200 + 96 * w1) * cfg.regularOpCost := by
          simp only [Nat.add_mul]; omega
        mstep; mstep; mstep
        mcall S201 using [M32 Hg S304 Hrd HS]
        · iframe M32 Hg S304 Hrd HS
        icases HQ with ⟨%hrs, M32, Hg, S304, Hrd, HS⟩
        subst hrs
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
        iframe M36 R16 HS Hrd Hg Hd X0 X24 X52 M32 M37 Ho
        isplitr [Hc S304]
        · ipureintro
          refine ⟨rfl, rfl, hr3l, hb16', ?_⟩
          rw [hr3]; exact hres'
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        iexact S304
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
  iframe Hc M36 R16 Hrd Hg S304 Hd X0 X24 X52 M32 M37 Ho
  isplitr [M40 M44 HJ]
  · ipureintro
    refine ⟨rfl, rfl, by omega, hb16, ?_⟩
    simpa [loopRes] using hloop
  iunfold seenRes
  iexists b44
  iframe M40 M44 HJ
  ipureintro; exact hb44

end Proof
end WNear.Binary.SerdeStructObjState
