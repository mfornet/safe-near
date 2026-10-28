import Bridge.Methods.Statics309
import Bridge.Functions.MetadataStruct

/-!
# The body of `ft_metadata` (309) on an initialized contract

`FtMetadataBody` has the prologue and the path on an absent `STATE`. Here the rest, the shape of
`storage_balance_bounds` (StorageBalanceBoundsBody.lean) in a frame of 160 bytes:

* `segM309`: `state_read` (219) on the model state, `unwrap_or_default` (155), the metadata (308)
  at `sp0 + 48`, `Vec::with_capacity(128)` (94) at `sp0 + 144`, the serializer at `sp0 + 128` and
  the struct (102, `MetadataStruct.f102_meta`, which reallocates the `Vec` to 256 bytes), the
  result `Ok(vec)` at `sp0 + 128`;
* `segC309`: `expect`, `deref`, `value_return` of the 138 bytes, then the drops: the `Vec`, the three
  `String`s, the two `None`s (147), `reference_hash`'s `None` skipped, the prefix's `Vec`;
* `body309`: the body from its entry frame, with 1024 bytes of stack.

The heap needs room for eight one-page grows (`HeapRoom8`): `state_read`'s two, the three
strings', the `Vec`'s and the realloc's.
-/

namespace WNear.Binary.FtMetadataBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply
open WNear.Binary.Interface (IfaceMod iface ifaceCode dataWord iface_of_setup)
open WNear.Binary.ReadRegister (ifaceR ifaceR_of_iface iface_of_ifaceR)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages cellPages_toNat cellBytes_toNat)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.BorshFT (join64' split64' joinB splitB stkJ stkW stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.StateReadLen (LenStep postModelL f219_spec_model_len)
open WNear.Binary.StateReadModel (contractBytes)
open WNear.Binary.StateRead (stateCode pre219 post219None noneAt)
open WNear.Binary.DropVec (dropCode pre747 post747 f68_spec)
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.MetadataFields (metaJson metaJson_length escT)
open WNear.Binary.MetadataGetter (metaOut metaStrs specStr nameStr symbolStr strCode cost308 Room3)
open WNear.Binary.MetadataStruct (metaSer metaCode cost102 f102_meta)

/-! ## The middle segment -/

/-- Room for eight grows of one page under the limit `maxP` (and `2^32`). -/
def HeapRoom8 (len maxP : Nat) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + 7 * 65536 ≤ maxP * 65536 ∧ len + 8 * 65536 ≤ 2 ^ 32

section SegM

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the middle segment (persistent). -/
def codeM309 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(stateCode e inst mi A n maxP (some maxP) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
    A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    A 308 ↪[wf] FuncInst.wasm types[14]! inst f308 ∗ strCode n maxP inst mi A ∗
    VecWithCap.vecCode2 n maxP inst mi A ∗ A 94 ↪[wf] FuncInst.wasm types[14]! inst f94 ∗
    metaCode n maxP inst mi A ∗ A 102 ↪[wf] FuncInst.wasm types[13]! inst f102 ∗ inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (codeM309 (GF := GF) e inst mi A n maxP) := by
  unfold codeM309; infer_instance

/-- The cost of `state_read`, `unwrap_or_default`, the metadata, the `Vec` and the JSON. -/
noncomputable def costM309 (cfg : WasmConfig) (h : NearState) (S : WNear.State) : Nat :=
  1500 * cfg.regularOpCost + cost219 cfg h S + cost308 cfg 2 + VecWithCap.costAllocF cfg 2 128 + cost102 cfg 2

/-- The data `ft_metadata`'s middle segment reads: the metadata's and `ft_total_supply`'s quote and
digits' `ESCAPE` entries. -/
def dataM309 (n : Nat) : IProp GF :=
  iprop(metaData n ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] SerializeStr.esc)

/-- The serializer's data from `dataM309`, and the getter's constants. -/
theorem metaSer_of (n : Nat) :
    dataM309 (GF := GF) n ⊢ metaSer n ∗ n ↦[wms][ 1051277 ] metaStrs := by
  iintro H
  iunfold dataM309 at H
  icases H with ⟨HD, Hq, He⟩
  iunfold metaData at HD
  icases HD with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, HA, HB⟩
  iframe H8
  iunfold metaSer
  iframe H1 H2 H3 H4 H5 H6 H7 Hq H9 H10
  rw [show (1061808 + 32 : Nat) = 1061840 from rfl, escT_split]
  ihave HAe := joinB (a := 1061840) (b := 1061856) escA SerializeStr.esc rfl $$ [HA He]
  · iframe HA He
  iapply joinB (a := 1061840) (b := 1061866) (escA ++ SerializeStr.esc) escB rfl
  iframe HAe HB

end SegM


section SegM2

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- The middle segment (`bodyB309 ++ bodyM309`): `state_read` (219) on the model state `S`,
`unwrap_or_default` (155), the metadata (308) at `sp0 + 48`, `Vec::with_capacity(128)` (94) at
`sp0 + 144`, the serializer `&mut vec` at `sp0 + 128` and the struct (102), the result `Ok(vec)` at
`sp0 + 128`: the `Vec` `(q, 256, 138)` holding `metaJson`. -/
theorem segM309 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 1024 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (idx : UInt32) (maxP len : Nat) (hroom : HeapRoom8 len maxP)
    (h : NearState) (S : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeM309 e inst mi A n maxP ∗ credits Cg (costM309 cfg h S + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 160)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 752) 592 ∗
      stk n (s.toNat - 152) 40 ∗ stk n (s.toNat - 112) 76 ∗ stk n (s.toNat - 32) 16 ∗ stk n (s.toNat - 16) 12 ∗
      vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      dataM309 n ∗ mhostPt h ∗
      (∀ (q p ps pn py : UInt32) (rst : List UInt8) (hl F : Nat) (h1 : NearState),
        ⌜StorageReadPost h StateRead.stateKey 0 st h1 ∧ metaJson.length + rst.length = 256 ∧
          q.toNat + 256 < 2 ^ 32⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 160)⟩ -∗ ifaceR n ta A -∗ stk n (s.toNat - 752) 592 -∗
        n ↦[i32][ s.toNat - 32 ] 0 -∗ n ↦[i32][ s.toNat - 28 ] q -∗ n ↦[i32][ s.toNat - 24 ] 256 -∗
        n ↦[i32][ s.toNat - 20 ] UInt32.ofNat 138 -∗ stk n (s.toNat - 16) 12 -∗
        n ↦[i32][ s.toNat - 128 ] p -∗ n ↦[i32][ s.toNat - 124 ] 1 -∗ n ↦[i32][ s.toNat - 120 ] 1 -∗
        metaOut n (s.toNat - 112) ps pn py -∗ n ↦[wms][ ps.toNat ] specStr -∗ n ↦[wms][ pn.toNat ] nameStr -∗
        n ↦[wms][ py.toNat ] symbolStr -∗
        n ↦[wms][ q.toNat ] (metaJson ++ rst) -∗ n ↦[wms][ p.toNat ] WNear.accountsPrefix -∗
        heapInv n maxP hl [(q.toNat, 256), (py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] F -∗
        mhostPt h1 -∗
        mwpi cfg lim d ⟨#[.i32 (s - 160), .i32 0, .i32 0], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 160), .i32 1, .i32 0], inst, mi⟩ [] ((bodyB309 ++ bodyM309) ++ rest) Φ := by
  iintro ⟨#Hk, Hc, Hg, HI, Lo, F8, F48, F128, F144, Hvt, Hinv, Hkey, HD, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeM309 at Hk'
  icases Hk' with ⟨#HSC, #F219, #F155, #F951, #F308, #HStr, #HV2, #F94, #HMC, #F102, #Hi⟩
  icases metaSer_of n $$ HD with ⟨HMS, Hstrs⟩
  unfold costM309 cost219
  have hn := hm.mem
  have hg := hm.glob
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have ha308 := hm.funcs 308 (by decide)
  have ha94 := hm.funcs 94 (by decide)
  have ha102 := hm.funcs 102 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have t13 : types[13]!.params.length = 2 := rfl
  have hlt := s.toNat_lt
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  have hr4 : HeapRoom len maxP := ⟨r1, r2, by omega, by omega⟩
  have e0 : (s - 160).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp; omega)]; simp
  have a48 : (s - 160 + 48).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have a8 : (s - 160 + 8).toNat = s.toNat - 152 := by simp [UInt32.toNat_add, e0]; omega
  have a128 : (s - 160 + 128).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  have a144 : (s - 160 + 144).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB309, bodyM309, List.cons_append, List.nil_append]
  -- state_read(sp0 + 48)
  icases stkSp 40 36 rfl $$ F48 with ⟨F48, F88⟩
  icases stk_bytes' $$ F48 with ⟨%ob, %hob, F48⟩
  mstep; mstep; mstep
  mcall (f219_spec_model_len cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm (by omega) Cg gt
      (s - 160) (s - 160 + 48) (by omega) (by omega) (by omega) idx maxP len [] ob hob h S hv
      (roomFor_of len maxP len 29 (by decide) hr4 (by omega) (by omega) r1)
      (by
        intro l hl
        rw [grownLen_small _ _ (by decide)] at hl
        exact roomFor_of len maxP l 1 (by decide) hr4 (by omega) (by omega) (by omega))
      st hacc hlim hb hz hlink hproof hreg)
    using [Hg HI Lo Hvt Hinv F48 Hkey Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 160).toNat - 592) (by omega) $$ Lo
    ihave F48 := memBytes_addr (b := (s - 160 + 48).toNat) (by omega) $$ F48
    iframe Hg HI Lo Hvt Hinv F48 Hkey Hh
    ipureintro; rfl
  iunfold postModelL at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, Hvt, Hkey, ⟨%pv, %p, %pad, %len', %⟨hpad, hstep⟩, Hopt, Hinv, Hp⟩,
    ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  have hlive : ((p.toNat, 1) :: (pv.toNat, 29) :: ([] : List (Nat × Nat))).erase (pv.toNat, 29) =
      [(p.toNat, 1)] := by simp
  rw [hlive]
  ihave Hinv := heapInv_live8 n maxP len' _ 2 $$ Hinv
  icases Hinv with ⟨%h8, Hinv⟩
  have hp8 : 8 ≤ p.toNat := h8 _ 1 (by simp)
  obtain ⟨hl1, hl2, hl3⟩ := lenStep_bounds len len' r1 hstep
  -- unwrap_or_default(sp0 + 8, sp0 + 48)
  icases stk_bytes' $$ F8 with ⟨%ob8, %hob8, F8⟩
  have hsb : (contractBytes S p ++ pad).length = 40 := by rw [List.length_append, contractBytes_length, hpad]
  have hniche : ((contractBytes S p ++ pad).drop 24).take 4 = bytes32 p := by
    rw [contractBytes_split]; simp [List.drop_append, List.take_append, u128_length, u64_length]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (UnwrapOrDefault.f155_spec cfg lim (d + 1) types[14]! rfl inst mi n (A 951) hn (hm.funcs 951 (by decide))
      types[15]! rfl rfl (by omega) Cg (s - 160 + 8) (s - 160 + 48) (by omega) (by omega) ob8
      (contractBytes S p ++ pad) hob8 hsb (by rw [hniche, decodeLE_bytes32]; omega))
    using [F8 Hopt]
  · iunfold UnwrapOrDefault.pre
    ihave F8 := memBytes_addr (b := (s - 160 + 8).toNat) (by omega) $$ F8
    iframe F8 Hopt
    ipureintro; rfl
  iunfold UnwrapOrDefault.post at HQ
  icases HQ with ⟨%hrs, C8, Hopt⟩
  subst hrs
  ihave Hopt := (show (n ↦[wms][ (s - 160 + 48).toNat ] (contractBytes S p ++ pad) : IProp GF) ⊢
      stk n (s.toNat - 112) 40 by
    iintro H; iunfold stk; iexists contractBytes S p ++ pad; iframe %hsb
    iapply memBytes_addr (by omega) $$ H) $$ Hopt
  rw [contractBytes_split]
  ihave C8 := memBytes_addr (b := s.toNat - 152) (by omega) $$ C8
  icases splitB (a := s.toNat - 152) (b := s.toNat - 136) (WNear.Borsh.u128 S.totalSupply) _
    (by rw [u128_length]; omega) $$ C8 with ⟨C0, C16⟩
  icases splitB (a := s.toNat - 136) (b := s.toNat - 128) (WNear.Borsh.u64 S.accountStorageUsage) _
    (by rw [u64_length]; omega) $$ C16 with ⟨Cx, C24⟩
  -- the metadata (308) at sp0 + 48
  ihave M76 := stkJ (a := s.toNat - 112) (b := s.toNat - 112 + 40) (k1 := 40) (k2 := 36) (k := 76) rfl rfl
    $$ [Hopt F88]
  · iframe Hopt F88
  ihave M76 := stkA (b := (s - 160 + 48).toNat) (by omega) $$ M76
  icases stkSp 480 112 rfl $$ Lo with ⟨Lo480, L112⟩
  ihave L112 := stkA (b := (s - 160).toNat - 112) (by omega) $$ L112
  mstep; mstep; mstep; mstep
  mcall (MetadataGetter.f308_spec cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 160)
      (s - 160 + 48) (s - 160) idx maxP len' [(p.toNat, 1)] 2 (by decide) (by omega) (by omega)
      ⟨hl3, by omega, by omega, by omega⟩)
    using [Hg L112 Hvt Hinv M76 Hstrs]
  · iframe Hg L112 Hvt Hinv M76 Hstrs
  icases HQ with ⟨%hrs, Hg, L112, Hvt, Hstrs, %ps, %pn, %py, %len'', %⟨hm1, hm2, hm3, hps0, hpn0, hpy0, hps, hpn, hpy⟩,
    HMO, Hinv, Hps, Hpn, Hpy⟩
  subst hrs
  -- Vec::with_capacity(sp0 + 144, 128)
  icases stk_bytes' $$ F144 with ⟨%ob12, %hob12, F144⟩
  icases stkSp 32 80 rfl $$ L112 with ⟨L32, L80⟩
  ihave L80 := stkA (b := (s - 160).toNat - 80) (by omega) $$ L80
  mstep; mstep; mstep; mstep
  have hr94 : roomFor len'' maxP 128 := by
    refine ⟨hm3, by omega, ?_, ?_⟩ <;> rw [cellPages_small _ (by decide)] <;> omega
  mcall (SerdeLeaves.f94_spec cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 160)
      (s - 160 + 144) 128 idx maxP len'' [(py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] ob12 hob12
      (by omega) (by decide) (fun _ => hr94) (F := 2) (hF := by decide))
    using [Hg L80 Hvt Hinv F144]
  · iunfold VecWithCap.pre373
    ihave F144 := memBytes_addr (b := (s - 160 + 144).toNat) (by omega) $$ F144
    iframe Hg L80 Hvt Hinv F144
    ipureintro; rfl
  iunfold VecWithCap.post373 at HQ
  icases HQ with ⟨%hrs, %q, Hg, L80, Hvt, V0, V4, V8, Ha⟩
  subst hrs
  icases FmtSink.heapAfter_grown (by simp) $$ Ha with ⟨%⟨hq0, hqb⟩, Hblk, Hgr⟩
  iunfold FmtSink.grown at Hgr
  icases Hgr with ⟨%hl1, %hhl1, Hinv⟩
  rw [grownLen_small _ _ (by decide)] at hhl1
  iunfold block at Hblk
  icases Hblk with ⟨%bs, %hbs, Hqb⟩
  have h128 : (128 : UInt32).toNat = 128 := rfl
  rw [h128] at hbs hqb
  rw [h128]
  -- the serializer: [sp0 + 128] := sp0 + 144
  icases stkSp 4 12 rfl $$ F128 with ⟨W128, F128⟩
  icases stkSp 8 4 rfl $$ F128 with ⟨Q132, L140⟩
  icases stk_bytes' $$ W128 with ⟨%w128, %hw128, W128⟩
  ihave W128 := memBytes_addr (b := (s - 160).toNat + 128) (by omega) $$ W128
  mstep; mstep; mstep; mstep; mstep [W128]
  -- serialize(sp0 + 48, sp0 + 128)
  ihave L80 := stkA (b := (s - 160).toNat - 112 + 32) (by omega) $$ L80
  ihave L112 := stkJ (a := (s - 160).toNat - 112) (b := (s - 160).toNat - 112 + 32) (k1 := 32) (k2 := 80) (k := 112)
    rfl rfl $$ [L32 L80]
  · iframe L32 L80
  icases stkSp 416 64 rfl $$ Lo480 with ⟨Lo416, L64⟩
  ihave L64 := stkA (b := (s - 160).toNat - 176) (by omega) $$ L64
  ihave L112 := stkA (b := (s - 160).toNat - 176 + 64) (by omega) $$ L112
  ihave L176 := stkJ (a := (s - 160).toNat - 176) (b := (s - 160).toNat - 176 + 64) (k1 := 64) (k2 := 112)
    (k := 176) rfl rfl $$ [L64 L112]
  · iframe L64 L112
  have S102 := f102_meta (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 160)
    (s - 160 + 48) (s - 160 + 128) (s - 160 + 144) q idx ps pn py maxP (len + 6 * 65536) hl1
    [(py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] 2 (by omega) (by omega) (by omega) hps hpn hpy
    hq0 (by omega) (by omega) (by omega) (by omega) (by omega)
  ihave #S102 := S102 $$ HMC
  repeat mstep
  mcall S102 using [Hg L176 HMS HMO Hps Hpn Hpy W128 Hvt V0 V4 V8 Hqb Hinv]
  · iframe Hg L176 HMS HMO Hps Hpn Hpy Hvt Hinv
    isplitl [W128]
    · iapply memBytes_addr (show (s - 160).toNat + 128 = (s - 160 + 128).toNat by omega) $$ W128
    iunfold SerdeStruct.outV
    iexists bs
    iframe V0 V4
    isplitr
    · ipureintro; simp; omega
    simp only [List.nil_append, List.length_nil]
    iframe Hqb V8
  icases HQ with ⟨%hrs, Hg, L176, -, HMO, Hps, Hpn, Hpy, Hser, -, %q', %hl', %⟨hq0', -, -, -⟩, Ho, Hinv⟩
  subst hrs
  mcredits (100 * cfg.regularOpCost + R)
  iunfold SerdeStruct.outV at Ho
  icases Ho with ⟨%rst, %⟨hrst, hq'b, -⟩, V0, V4, V8, Hqj⟩
  generalize hL : UInt32.ofNat metaJson.length = Lw
  -- `Ok(vec)` at sp0 + 128
  have hor : (s - 160 + 128) ||| 4 = s - 160 + 128 + 4 := by
    apply UInt32.toNat_inj.1
    simp only [UInt32.toNat_or, UInt32.toNat_add, UInt32.reduceToNat]
    have hx : ((s - 160).toNat + 128) % 2 ^ 32 = (s - 160).toNat + 128 := Nat.mod_eq_of_lt (by omega)
    rw [hx, Nat.mod_eq_of_lt (by omega)]
    have ee := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := 4) (by decide) (((s - 160).toNat + 128) / 8)
    have m : 2 ^ 3 * (((s - 160).toNat + 128) / 8) = (s - 160).toNat + 128 := by omega
    rw [m] at ee
    omega
  repeat mstep
  rw [hor]
  have a132 : (s - 160 + 128 + 4).toNat = (s - 160).toNat + 132 := by simp [UInt32.toNat_add]; omega
  have a140 : (s - 160 + 128 + 4 + 8).toNat = (s - 160).toNat + 140 := by simp [UInt32.toNat_add]; omega
  have a152 : (s - 160 + 144 + 8).toNat = (s - 160).toNat + 152 := by simp [UInt32.toNat_add]; omega
  ihave V0 := memBytes_addr (b := (s - 160).toNat + 144) (by omega) $$ V0
  ihave V4 := memBytes_addr (b := (s - 160).toNat + 144 + 4) (by omega) $$ V4
  ihave V8 := memBytes_addr (b := (s - 160).toNat + 152) (by omega) $$ V8
  ihave V04 := join64' (a := (s - 160).toNat + 144) (b := (s - 160).toNat + 144 + 4) q' 256 rfl $$ [V0 V4]
  · iframe V0 V4
  icases stk_bytes' $$ Q132 with ⟨%qb, %hqb8, Q132⟩
  ihave Q132 := memBytes_addr (b := (s - 160).toNat + 132) (by omega) $$ Q132
  icases stk_bytes' $$ L140 with ⟨%lb, %hlb, L140⟩
  ihave L140 := memBytes_addr (b := (s - 160).toNat + 140) (by omega) $$ L140
  mstep [V04]
  mstep [Q132]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  repeat mstep
  mstep [V8]
  mstep [L140]
  repeat mstep
  ihave Hser := memBytes_addr (b := (s - 160).toNat + 128) (by omega) $$ Hser
  mstep [Hser]
  -- hand over to segment C
  subst hL
  icases stkSp 64 112 rfl $$ L176 with ⟨L64, L112⟩
  ihave L64 := stkA (b := (s - 160).toNat - 592 + 416) (by omega) $$ L64
  ihave Lo := stkJ (a := (s - 160).toNat - 592) (b := (s - 160).toNat - 592 + 416) (k1 := 416) (k2 := 64)
    (k := 480) rfl rfl $$ [Lo416 L64]
  · iframe Lo416 L64
  ihave L112 := stkA (b := (s - 160).toNat - 592 + 480) (by omega) $$ L112
  ihave Lo := stkJ (a := (s - 160).toNat - 592) (b := (s - 160).toNat - 592 + 480) (k1 := 480) (k2 := 112)
    (k := 592) rfl rfl $$ [Lo L112]
  · iframe Lo L112
  ihave Lo := stkA (b := s.toNat - 752) (by omega) $$ Lo
  ihave Hser := memBytes_addr (b := s.toNat - 32) (by omega) $$ Hser
  icases split64' (a := (s - 160).toNat + 132) (b := s.toNat - 24) q' 256 (by omega) $$ Q132 with ⟨R4, R8⟩
  ihave R4 := memBytes_addr (b := s.toNat - 28) (by omega) $$ R4
  ihave L140 := memBytes_addr (b := s.toNat - 20) (by omega) $$ L140
  ihave V04 := stkB (b := s.toNat - 16) (k := 8) _ (by omega) (by simp [bytes32]) $$ V04
  ihave V8 := stkW (b := s.toNat - 16 + 8) _ (by omega) $$ V8
  ihave V := stkJ (a := s.toNat - 16) (b := s.toNat - 16 + 8) (k1 := 8) (k2 := 4) (k := 12) rfl rfl $$ [V04 V8]
  · iframe V04 V8
  icases splitB (a := s.toNat - 128) (b := s.toNat - 124) (bytes32 p) _ (by simp; omega) $$ C24 with ⟨P0, C28⟩
  icases splitB (a := s.toNat - 124) (b := s.toNat - 120) (bytes32 1) _ (by simp; omega) $$ C28 with ⟨P4, C32⟩
  icases splitB (a := s.toNat - 120) (b := s.toNat - 116) (bytes32 1) _ (by simp; omega) $$ C32 with ⟨P8, -⟩
  ihave HMO := (show metaOut (GF := GF) n (s - 160 + 48).toNat ps pn py ⊢ metaOut n (s.toNat - 112) ps pn py by
    rw [a48]) $$ HMO
  mcredits R
  rw [metaJson_length] at hrst ⊢
  iapply W $$ %q' %p %ps %pn %py %rst %hl' %(max 2 1 + 1) %h1 [] Hc Hg HI Lo Hser R4 R8 L140 V P0 P4 P8 HMO Hps Hpn Hpy
    [Hqj] Hp Hinv Hh
  · ipureintro; exact ⟨hq1, by simpa using hrst, hq'b⟩
  · iexact Hqj

end SegM2

end WNear.Binary.FtMetadataBody
