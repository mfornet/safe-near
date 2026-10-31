import Bridge.Functions.SerdeStructObjPhase
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

def CloseHyp (bs : List UInt8) (J : MemberState (GF := GF)) : Prop :=
  ∀ i j seen, j = i + wsLen (bs.drop i) → bs[j]? = some 0x7D → J i seen ⊢ J (j + 1) seen


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

/-- Forgetting phases preserves the exact previously checked key interface. -/
theorem phase_key_hyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (n g Cg : Nat) (gt : GlobalType) (de ptr : UInt32) (bs : List UInt8) (K : Nat → Nat)
    (J : SerdeStructObjState.MemberState (GF := GF)) (Cd : IProp GF)
    (h : SerdeStructObjState.KeyHyp cfg lim inst mi n g Cg gt de ptr bs K J Cd) :
    SerdeStructObjPhase.KeyHyp cfg lim inst mi n g Cg gt de ptr bs K (fun _ => J) Cd := h

/-- Forgetting phases preserves the exact previously checked account interface. -/
theorem phase_value_hyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (n g Cg : Nat) (gt : GlobalType) (de ptr : UInt32) (bs : List UInt8)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (K : Nat → Nat)
    (J : SerdeStructObjState.MemberState (GF := GF)) (Cd : IProp GF)
    (h : SerdeStructObjState.ValueHyp cfg lim inst mi n g Cg gt de ptr bs dv K J Cd) :
    SerdeStructObjPhase.ValueHyp cfg lim inst mi n g Cg gt de ptr bs dv K (fun _ => J) Cd := h

/-- The old universal ignore interface supplies every phase-aware unknown-key branch. -/
theorem phase_ignore_hyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (n g Cg : Nat) (gt : GlobalType) (de ptr : UInt32) (bs : List UInt8)
    (ign : List UInt8 → Option (Unit × List UInt8)) (K : Nat → Nat)
    (J : SerdeStructObjState.MemberState (GF := GF)) (Cd : IProp GF)
    (h : SerdeStructObjState.IgnoreHyp cfg lim inst mi n g Cg gt de ptr bs ign K J Cd) :
    SerdeStructObjPhase.IgnoreHyp cfg lim inst mi n g Cg gt de ptr bs ign K (fun _ => J) Cd := by
  intro d s i rest seen key hkey
  exact h d s i rest seen

/-- Closing with a phase-independent state is the original brace transport. -/
theorem phase_close_hyp (bs : List UInt8) (J : SerdeStructObjState.MemberState (GF := GF))
    (h : SerdeStructObjState.CloseHyp bs J) : SerdeStructObjPhase.CloseHyp bs (fun _ => J) := by
  intro first i j seen
  exact h i j seen


set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **228 on the object form**: `out` gets `Ok(a)` with changed member state, the reader past the `}`,
`remaining_depth` back at 128. -/
theorem f228_obj_state_closing (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
    (hclose : CloseHyp bs J)
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
  exact SerdeStructObjPhase.f228_obj_state_closing (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout hlen hptr hde hsp hal hi
    dv ign K646 K169 K81 (fun _ => J) Cd
    (phase_key_hyp cfg lim inst mi n g Cg gt de ptr bs K646 J Cd h646)
    (phase_value_hyp cfg lim inst mi n g Cg gt de ptr bs dv K169 J Cd h169)
    (phase_ignore_hyp cfg lim inst mi n g Cg gt de ptr bs ign K81 J Cd h81)
    (phase_close_hyp bs J hclose)
    hdvs higns hstrs N a rF hb0 hloop



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
  apply f228_obj_state_closing cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5 ob bs i
    maxP hob hout hlen hptr hde hsp hal hi dv ign K646 K169 K81 J Cd h646 h169 h81 ?_ hdvs higns hstrs N a rF hb0 hloop
  intro i j seen hj _
  exact hmono i (j + 1) seen (by omega)


end Proof
end WNear.Binary.SerdeStructObjState
