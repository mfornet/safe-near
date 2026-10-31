import Bridge.Functions.BalanceOf297ParserRoom
import Bridge.Functions.SerdeStructObjModelState
import Bridge.Functions.SerdeIgnReuse

/-! Escape-free object readers with concrete key, account-value and shallow-ignore instances.
The initial-room theorem does not establish ownership of the required method resources. -/

namespace WNear.Binary.SerdeObjectNoEsc
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open ParseStr ParseStrSuccess ScratchGrow


/-- A successful escape-free string borrows its source and has no scratch appends. -/
theorem noesc_parts (bs : List UInt8) (q : Nat) (s : String) (rest : List UInt8)
    (hnb : (0x5C : UInt8) ∉ bs)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some s, rest)) :
    borrowed (bs.drop q) ∧ appendChunks (bs.drop q) [] = [] ∧
      s.toUTF8.toList = SerdeKeyNoEsc.keyBody bs q := by
  obtain ⟨_, _, _, _, hd, hb⟩ := SerdeKeyNoEsc.key_noesc hnb hmodel
  have hbor : borrowed (bs.drop q) := by unfold borrowed; rw [hd]; rfl
  obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  exact ⟨hbor, (SerdeValueReuse.borrowed_parts _ _ _ hbor hok).2.2, hb⟩

/-- Uniform key calls preserve every cursor-independent bound on escape-free input. -/
theorem key_conditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : WNear.Binary.SerdeStructObjKeyState.Bounds)
    (hnb : (0x5C : UInt8) ∉ bs)
    (htransport : ∀ i j hl F cap, B i hl F cap → B j hl F cap)
    (hroom : ∀ i hl F cap, B i hl F cap → hl % 65536 = 0 → 0 < hl →
      SerdeErrBox.roomFor4 hl maxP 20) :
    WNear.Binary.SerdeStructObjKeyState.KeyConditions cfg maxP bs B (SerdeKeyNoEsc.K646 cfg bs) := by
  intro first i q key rest hl F cap hi hq hmodel hb hcap hal hpos
  obtain ⟨hbor, hchunks, hbytes⟩ := noesc_parts bs q key rest hnb hmodel
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  refine ⟨?_, ?_, ?_⟩
  · simpa only [SerdeKeyReuse.keyRoom, if_pos hbor] using hroom i hl F cap hb hal hpos
  · rw [SerdeKeyReuse.keyCost_borrowed cfg F cap bs key.toUTF8.toList rest q hbor hok hu]
    unfold SerdeKeyNoEsc.K646
    rw [← hbytes]
    unfold FromUtf8.cost927
    have he := (SerdeValueReuse.borrowed_parts _ _ _ hbor hok).1
    have hlen := congrArg List.length he
    simp only [List.length_append, List.length_cons] at hlen
    apply Nat.mul_le_mul_right
    omega
  · intro hl' hlo hhi
    simp only [hchunks, growthPages, Nat.zero_mul, Nat.add_zero] at hhi
    have he : hl' = hl := by omega
    subst hl'
    simp only [hchunks, endFreeBound, endState]
    exact htransport i _ hl F cap hb

/-- Resource bounds before the sole accepted account-id allocation. -/
def before (L F0 : Nat) : WNear.Binary.SerdeStructObjKeyState.Bounds := fun _ hl F cap => hl = L ∧ F ≤ F0 ∧ cap = 0
/-- Resource bounds after the account-id allocation; keys and ignored values preserve these. -/
def saved (L F0 : Nat) : WNear.Binary.SerdeStructObjKeyState.Bounds := fun _ hl F cap =>
  L ≤ hl ∧ hl ≤ L + 65536 ∧ F ≤ max F0 1 ∧ cap = 0

/-- The heap budget survives the single account-id allocation and bounds all key reserves. -/
theorem saved_room (L F0 maxP i hl F : Nat) (cap : UInt32)
    (hr : LookupMapOps.HeapRoomK 132 L maxP) (hb : saved L F0 i hl F cap)
    (ha : hl % 65536 = 0) (hp : 0 < hl) : LookupMapOps.HeapRoomK 131 hl maxP := by
  rcases hr with ⟨_, _, hm, hw⟩
  exact ⟨ha, hp, by have := hb.2.1; omega, by have := hb.2.1; omega⟩

/-- Keys concretely preserve the pre-value bounds on escape-free objects. -/
theorem keys_before (cfg : WasmConfig) (L F0 maxP : Nat) (bs : List UInt8)
    (hnb : (0x5C : UInt8) ∉ bs) (hr : LookupMapOps.HeapRoomK 132 L maxP) :
    WNear.Binary.SerdeStructObjKeyState.KeyConditions cfg maxP bs (before L F0) (SerdeKeyNoEsc.K646 cfg bs) := by
  apply key_conditions cfg maxP bs (before L F0) hnb
  · intro i j hl F cap hb; exact hb
  · intro i hl F cap hb ha hp
    obtain ⟨rfl, _⟩ := hb
    exact ParseStrRoom.error_room hr (by omega)

/-- Keys concretely preserve the retained-value bounds on escape-free objects. -/
theorem keys_saved (cfg : WasmConfig) (L F0 maxP : Nat) (bs : List UInt8)
    (hnb : (0x5C : UInt8) ∉ bs) (hr : LookupMapOps.HeapRoomK 132 L maxP) :
    WNear.Binary.SerdeStructObjKeyState.KeyConditions cfg maxP bs (saved L F0) (SerdeKeyNoEsc.K646 cfg bs) := by
  apply key_conditions cfg maxP bs (saved L F0) hnb
  · intro i j hl F cap hb; exact hb
  · intro i hl F cap hb ha hp
    exact ParseStrRoom.error_room (saved_room L F0 maxP i hl F cap hr hb ha hp) (by omega)

/-- The account-id reader concretely discharges the object's value bounds on escape-free input. -/
theorem values (cfg : WasmConfig) (L F0 maxP : Nat) (bs : List UInt8)
    (hnb : (0x5C : UInt8) ∉ bs) (hr : LookupMapOps.HeapRoomK 132 L maxP) :
    SerdeStructObjValueState.ValueConditions cfg maxP bs (before L F0) (saved L F0)
      (SerdeAcctHyp.K169 cfg bs F0) := by
  intro i j a rest hl F cap hi hc hj hq hmodel hb hcap hal hpos
  obtain ⟨rfl, hF, rfl⟩ := hb
  obtain ⟨hbor, hchunks, hbytes⟩ := noesc_parts bs (j + 1) a.val rest hnb hmodel
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  have hv : validAccountIdBytes a.val.toUTF8.toList = true := a.toNear.property
  have hsmall : a.val.toUTF8.toList.length ≤ 64 := by
    unfold validAccountIdBytes at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.2
  have hsize : (UInt32.ofNat a.val.toUTF8.toList.length).toNat = a.val.toUTF8.toList.length := by
    simp only [UInt32.toNat_ofNat']; omega
  have hpage := SerdeAcctHyp.cellPages_one (UInt32.ofNat a.val.toUTF8.toList.length) (by rw [hsize]; omega)
  refine ⟨ParseStrRoom.error_room hr (by omega), ?_, ?_, ?_, ?_⟩
  · apply ParseStrRoom.roomRun_short maxP hl 0 [] _ _ rest (by decide) (by simp) hsmall hok
    exact ParseStrRoom.heap_room_mono hr (by
      have : 2 * (a.val.toUTF8.toList.length - ([] : List UInt8).length) + 3 ≤ 132 := by
        simp only [List.length_nil, Nat.sub_zero]; omega
      exact this)
  · simp only [hchunks, growthPages, Nat.zero_mul, Nat.add_zero]
    exact LookupMapOps.roomFor_ofK _ (by rw [hsize]; omega) hr (LookupMapOps.lenIn_zero hl hr.1) (by omega)
  · have hjl := SerdeNextKey.getElem_lt hq
    have h380 : SerdeDeStr.ok380 bs a.val.toUTF8.toList (0x22 :: rest) j := ⟨hjl, rfl, hu⟩
    have htail := (SerdeKeyNoEsc.key_noesc hnb hmodel).2.2.2.2.1
    unfold SerdeValueReuse.valueCost SerdeAcctHyp.K169
    rw [if_pos hbor, ← hj, ← hbytes, htail]
    have := SerdeAcctHyp.cost380_mono cfg hF bs a.val.toUTF8.toList (0x22 :: rest) j
      (SerdeRead.wsLen (bs.drop (i + SerdeRead.wsLen (bs.drop i) + 1))) h380
    omega
  · intro hl' hlo hhi
    simp only [hchunks, growthPages, endFreeBound, endState, hpage, Nat.zero_add] at hhi ⊢
    exact ⟨hlo, hhi, max_le_max hF (le_refl 1), rfl⟩

/-- The actual initial heap, after the input allocation, supplies every object-reader reserve. -/
theorem initial_room (bs : List UInt8) (L : Nat) (hlen : bs.length < 2 ^ 24)
    (hL : L = InitialState.memLen ∨ L = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length)) :
    LookupMapOps.HeapRoomK 132 L 2048 := by
  have hp := BalanceOf297AbsentCall.input_pages_le bs hlen
  have hr : LookupMapOps.HeapRoomK
      ((AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat + 132)
      InitialState.memLen 2048 := by
    apply ParseStrRoom.heap_room_mono (show LookupMapOps.HeapRoomK 389 InitialState.memLen 2048 from by
      unfold LookupMapOps.HeapRoomK InitialState.memLen
      decide +kernel)
    omega
  apply BalanceOf297AbsentCall.room_after_input_pages hr
  simpa only [VecFromElem.grownLen] using hL

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.SerdeStructModel

set_option maxRecDepth 100000 in
/-- The real object loop on escape-free input, with concrete key, value and shallow-ignore contracts. -/
theorem f228_obj_noesc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i maxP : Nat)
    (live : List (Nat × Nat)) (L F0 : Nat) (hnb : (0x5C : UInt8) ∉ bs) (hr : LookupMapOps.HeapRoomK 132 L maxP)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ (SerdeIgnValue.code81 inst mi A) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n maxP ta (A 578) idx de live (before L F0) (saved L F0) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg (SerdeKeyNoEsc.K646 cfg bs) (SerdeAcctHyp.K169 cfg bs F0) (SerdeIgnReuse.cost81 cfg bs) (valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n maxP ta (A 578) idx de live (before L F0) (saved L F0) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hck : iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ (SerdeIgnValue.code81 inst mi A)) ⊢
      SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply SerdeStructObjModelState.code_keys n maxP inst mi A
    iexact Hcode
  have hcv : iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ (SerdeIgnValue.code81 inst mi A)) ⊢
      SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply SerdeStructObjModelState.code_values n maxP inst mi A
    iexact Hcode
  have hk := SerdeStructObjKeyState.keyHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live (before L F0) (saved L F0) (SerdeKeyNoEsc.K646 cfg bs) hlen hptr (by omega) (keys_before cfg L F0 maxP bs hnb hr) (keys_saved cfg L F0 maxP bs hnb hr) iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ (SerdeIgnValue.code81 inst mi A)) hck
  have hv := SerdeStructObjValueState.valueHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live (before L F0) (saved L F0) (SerdeAcctHyp.K169 cfg bs F0) hlen hptr (by omega) (values cfg L F0 maxP bs hnb hr) iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ (SerdeIgnValue.code81 inst mi A)) hcv
  have hmono : ∀ i j hl F cap, i ≤ j → before L F0 i hl F cap → before L F0 j hl F cap := by
    intro i j hl F cap hij hb; exact hb
  have hmonoSaved : ∀ i j hl F cap, i ≤ j → saved L F0 i hl F cap → saved L F0 j hl F cap := by
    intro i j hl F cap hij hb; exact hb
  have hci : iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ SerdeIgnValue.code81 inst mi A) ⊢
      SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnValue.code81 inst mi A := by
    iintro ⟨#Hcode, #H81⟩
    iunfold SerdeStructObjModelState.code at Hcode
    icases Hcode with ⟨#H193, -, -, -, -, -, #F89, -, #F81, -⟩
    iunfold SerdeNextKey.code193 at H193
    icases H193 with ⟨#Hend, -⟩
    iframe Hend F89 F81 H81
  have hignore := SerdeIgnReuse.ignoreHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live (before L F0) (saved L F0) hlen hptr (by omega) hnb hmono hmonoSaved
    iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ SerdeIgnValue.code81 inst mi A) hci
  obtain ⟨_, hdvs, _, hstrs, _, _⟩ := SerdeFromTrait.reader_facts
    (dv := valueAs WNear.account) (ign := WNear.IgnoreShallow.vSkipR)
    (fun _ => Or.inl rfl) WNear.IgnoreModel.vSkip_agrees bs
  have higns : ∀ j r, j ≤ bs.length → WNear.IgnoreShallow.ign1R (bs.drop j) = some ((), r) →
      bs.drop (bs.length - r.length) = r := by
    intro j r hj h
    exact WNear.JsonSuffix.drop_suf' (WNear.IgnoreShallow.ign1R_suf h)
  have result := SerdeStructObjState.f228_obj_state (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout (by omega) hptr hde hsp hal hi
    (valueAs WNear.account) WNear.IgnoreShallow.ign1R (SerdeKeyNoEsc.K646 cfg bs) (SerdeAcctHyp.K169 cfg bs F0) (SerdeIgnReuse.cost81 cfg bs) (member n maxP ta (A 578) idx de live (before L F0) (saved L F0))
    iprop(SerdeStructObjModelState.code (GF := GF) n maxP inst mi A ∗ (SerdeIgnValue.code81 inst mi A)) hk hv hignore
    (fun i j seen hij => SerdeStructObjKeyState.member_mono n maxP ta (A 578) idx de live (before L F0) (saved L F0) hmono hmonoSaved i j seen hij)
    hdvs higns hstrs N a rF hb0 hloop
  iintro ⟨#Hcode, #HCd⟩
  iapply result
  iframe Hcode HCd
  iunfold SerdeStructObjModelState.code at Hcode
  icases Hcode with ⟨#C193, -, -, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77⟩
  iframe C193 F205 F201 F193 F89 F90 F81 F169 F77

set_option maxRecDepth 100000 in
/-- The concrete object loop at the instantiated memory size, with no unresolved reader or room hypothesis. -/
theorem f228_obj_initial_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (L F0 : Nat) (hnb : (0x5C : UInt8) ∉ bs)
    (hL : L = InitialState.memLen ∨ L = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code (GF := GF) n 2048 inst mi A ∗ (SerdeIgnValue.code81 inst mi A) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live (before L F0) (saved L F0) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg (SerdeKeyNoEsc.K646 cfg bs) (SerdeAcctHyp.K169 cfg bs F0) (SerdeIgnReuse.cost81 cfg bs) (valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live (before L F0) (saved L F0) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  exact f228_obj_noesc cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx
    x2 x3 x4 x5 ob bs i 2048 live L F0 hnb (initial_room bs L hlen hL) hob hout hlen hptr hde
    hsp hal hi N a rF hb0 hloop

end Proof
end WNear.Binary.SerdeObjectNoEsc
