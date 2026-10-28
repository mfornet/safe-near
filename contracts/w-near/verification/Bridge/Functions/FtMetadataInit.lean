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


/-! ## Segment C -/

section SegC

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of segment C (persistent): `ft_total_supply`'s and the drop of a `None` (147). -/
def codeC309 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(codeC e inst mi A n mx ∗ A 147 ↪[wf] FuncInst.wasm types[0]! inst f147)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (codeC309 (GF := GF) e inst mi A n mx) := by
  unfold codeC309; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- Segment C (`bodyC309`): `expect` (158), `deref` (779), `value_return` (545) of the JSON `bs`,
then the drops: the `Vec` `(q, 256)`, the three `String`s, the two `None`s (147), the third `None`
skipped, the prefix's `Vec` `(p, 1)`; the heap's blocks all freed. -/
theorem segC309 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 1024 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (q L p ps pn py : UInt32) (bs rest : List UInt8) (hbs : bs.length = L.toNat) (hpos : 0 < L.toNat)
    (hrest : bs.length + rest.length = 256) (maxP hl F : Nat) (h1 : NearState)
    (hlim : withinLimit h1.config.maxReturnLen L.toNat = true) (loc x1 x2 : UInt32) (Φ : Post NearState GF) :
    codeC309 e inst mi A n mx ∗ credits Cg (3000 * cfg.regularOpCost + valueReturnUse h1 L.toNat + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 160)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 240) 80 ∗ stk n (s.toNat - 160) 8 ∗
      n ↦[i32][ s.toNat - 32 ] 0 ∗ n ↦[i32][ s.toNat - 28 ] q ∗ n ↦[i32][ s.toNat - 24 ] 256 ∗
      n ↦[i32][ s.toNat - 20 ] L ∗ stk n (s.toNat - 16) 12 ∗
      n ↦[i32][ s.toNat - 128 ] p ∗ n ↦[i32][ s.toNat - 124 ] 1 ∗ n ↦[i32][ s.toNat - 120 ] 1 ∗
      metaOut n (s.toNat - 112) ps pn py ∗ n ↦[wms][ ps.toNat ] specStr ∗ n ↦[wms][ pn.toNat ] nameStr ∗
      n ↦[wms][ py.toNat ] symbolStr ∗
      n ↦[wms][ q.toNat ] (bs ++ rest) ∗ n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
      heapInv n maxP hl [(q.toNat, 256), (py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] F ∗
      mhostPt h1 ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ mhostPt (h1.selectReturnValue bs) -∗
        Φ.normal [] ⟨#[.i32 (s - 160), .i32 x1, .i32 x2], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 160), .i32 x1, .i32 x2], inst, mi⟩ [] (bodyC309) Φ := by
  iintro ⟨#Hk, Hc, Hg, HI, L2, F0, R0, R4, R8, R12, F144, V0, V4, V8, HMO, Hps, Hpn, Hpy, Hq, Hp, Hinv, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeC309 at Hk'
  icases Hk' with ⟨#HC, #F147⟩
  iunfold codeC at HC
  icases HC with ⟨#HIC, #Hdr, #F456, #F158, #F779, #F545, #F68⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdr; icases Hdr with ⟨#Hi, -⟩; iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha158 := hm.funcs 158 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha545 := hm.funcs 545 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have ha147 := hm.funcs 147 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  have e0 : (s - 160).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 160 - 16).toNat = s.toNat - 176 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 160 - 16 - 16).toNat = s.toNat - 192 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a144 : (s - 160 + 144).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  have a128 : (s - 160 + 128).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  have a32 : (s - 160 + 8 + 24).toNat = s.toNat - 128 := by simp [UInt32.toNat_add, e0]; omega
  have a48 : (s - 160 + 48).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have a60 : (s - 160 + 60).toNat = s.toNat - 100 := by simp [UInt32.toNat_add, e0]; omega
  have a72 : (s - 160 + 48 + 24).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, e0]; omega
  have a84 : (s - 160 + 84).toNat = s.toNat - 76 := by simp [UInt32.toNat_add, e0]; omega
  have a96 : (s - 160 + 96).toNat = s.toNat - 64 := by simp [UInt32.toNat_add, e0]; omega
  have hLb : L.toNat ≤ 256 := by omega
  have hq := q.toNat_lt
  simp only [bodyC309]
  -- expect(sp0 + 144, sp0 + 128, loc)
  ihave PL := join64' (a := s.toNat - 28) (b := s.toNat - 24) q 256 (by omega) $$ [R4 R8]
  · iframe R4 R8
  ihave PL := joinB (a := s.toNat - 28) (b := s.toNat - 20) (bytes32 q ++ bytes32 256) (bytes32 L)
    (by simp; omega) $$ [PL R12]
  · iframe PL R12
  icases stk_bytes' $$ F144 with ⟨%ob, %hob, F144⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (ResultExpect.f158_spec cfg lim (d + 1) types[31]! rfl inst mi n g hn hg Cg ⟨gt, .i32 (s - 160)⟩
      (s - 160) (s - 160 + 144) (s - 160 + 128) 1051320 rfl (by omega) (by omega) (bytes32 0)
      (bytes32 q ++ bytes32 256 ++ bytes32 L) ob (by simp) (by simp) hob (by simp [decodeLE_bytes32]))
    using [Hg R0 PL F144]
  · iunfold ResultExpect.pre
    ihave R0 := memBytes_addr (b := (s - 160 + 128).toNat) (by omega) $$ R0
    ihave PL := memBytes_addr (b := (s - 160 + 128).toNat + 4) (by omega) $$ PL
    ihave F144 := memBytes_addr (b := (s - 160 + 144).toNat) (by omega) $$ F144
    iframe Hg R0 PL F144
    ipureintro; rfl
  iunfold ResultExpect.post at HQ
  icases HQ with ⟨%hrs, Hg, R0, PL, V144⟩
  subst hrs
  -- deref(sp0, sp0 + 144)
  icases stk_bytes' $$ F0 with ⟨%o0, %ho0, F0⟩
  mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 160) (s - 160 + 144) o0
      (bytes32 q ++ bytes32 256 ++ bytes32 L) ho0 (by simp)) using [F0 V144]
  · iunfold VecDeref.pre
    ihave F0 := memBytes_addr (b := (s - 160).toNat) (by omega) $$ F0
    iframe F0 V144
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, O0, V144⟩
  subst hrs
  have hvb : (bytes32 q ++ (bytes32 256 ++ bytes32 L)).take 4 ++ (bytes32 q ++ (bytes32 256 ++ bytes32 L)).drop 8 =
      bytes32 q ++ bytes32 L := by
    simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  icases split64' (a := (s - 160).toNat) (b := (s - 160).toNat + 4) q L (by omega) $$ O0 with ⟨O0, O4⟩
  mstep; mstep [O0]; mstep; mstep [O4]
  -- value_return(q, L)
  icases stkSp 48 32 rfl $$ L2 with ⟨L48, L2⟩
  icases stkSp 4 28 rfl $$ L2 with ⟨X48, L2⟩
  icases stkSp 4 24 rfl $$ L2 with ⟨X52, L2⟩
  icases stkSp 4 20 rfl $$ L2 with ⟨X56, L2⟩
  icases stkSp 4 16 rfl $$ L2 with ⟨X60, L2⟩
  icases stkSp 8 8 rfl $$ L2 with ⟨Y64, L2⟩
  icases stkSp 4 4 rfl $$ L2 with ⟨X72, X76⟩
  icases stk4_word $$ X48 with ⟨%x48, X48⟩
  icases stk4_word $$ X52 with ⟨%x52, X52⟩
  icases stk4_word $$ X56 with ⟨%x56, X56⟩
  icases stk4_word $$ X60 with ⟨%x60, X60⟩
  icases stk4_word $$ X72 with ⟨%x72, X72⟩
  icases stk4_word $$ X76 with ⟨%x76, X76⟩
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  icases splitB (a := q.toNat) (b := q.toNat + bs.length) bs rest rfl $$ Hq with ⟨Hb, Hr⟩
  ihave #S545 := ValueReturn.f545_spec cfg lim (d + 1) types[14]! rfl inst mi e A n g ta mx hm (by omega) Cg
    ⟨gt, .i32 (s - 160)⟩ (s - 160) rfl (by omega) (by omega) h1 q L bs hbs hlim hpos x72 x76 x48 x52 x56 x60
    $$ []
  · iframe F456 HIC
  mcall S545 using [Hg HI X72 X76 X48 X52 X56 X60 Hb Hh]
  · iunfold ValueReturn.pre, frame4
    ihave X72 := memBytes_addr (b := (s - 160 - 16).toNat + 8) (by omega) $$ X72
    ihave X76 := memBytes_addr (b := (s - 160 - 16).toNat + 12) (by omega) $$ X76
    ihave X48 := memBytes_addr (b := (s - 160 - 16 - 16).toNat) (by omega) $$ X48
    ihave X52 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 4) (by omega) $$ X52
    ihave X56 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 8) (by omega) $$ X56
    ihave X60 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 12) (by omega) $$ X60
    iframe Hg HI X72 X76 X48 X52 X56 X60 Hb Hh
    ipureintro; rfl
  iunfold ValueReturn.post at HQ
  icases HQ with ⟨%hrs, Hg, HI, X72, X76, HF4, Hb, Hh⟩
  subst hrs
  mcredits (1900 * cfg.regularOpCost + R)
  -- drop the JSON `Vec` (q, 256, L)
  ihave V144 := memBytes_addr (b := s.toNat - 16) (by omega) $$ V144
  icases splitB (a := s.toNat - 16) (b := s.toNat - 12) (bytes32 q) (bytes32 256 ++ bytes32 L) (by simp; omega)
    $$ V144 with ⟨V144, V148⟩
  icases split64' (a := s.toNat - 12) (b := s.toNat - 8) 256 L (by omega) $$ V148 with ⟨V148, V152⟩
  mstep; mstep; mstep
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(q.toNat, 256), (py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] F (s - 160 + 144) q 256 L
      (by decide) (by omega))
    using [V144 V148 V152 Hinv Hb Hr]
  · iunfold pre747
    ihave V144 := memBytes_addr (b := (s - 160 + 144).toNat) (by omega) $$ V144
    ihave V148 := memBytes_addr (b := (s - 160 + 144).toNat + 4) (by omega) $$ V148
    ihave V152 := memBytes_addr (b := (s - 160 + 144).toNat + 8) (by omega) $$ V152
    ihave Hq := joinB (a := q.toNat) (b := q.toNat + bs.length) bs rest rfl $$ [Hb Hr]
    · iframe Hb Hr
    iframe V144 V148 V152 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists bs ++ rest
    iframe Hq
    ipureintro; simp; omega
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, -, -, -, Hinv⟩
  subst hrs
  have hl1 : [(q.toNat, 256), (py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)].erase
      (q.toNat, (256 : UInt32).toNat) = [(py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] := by simp
  rw [hl1]
  iunfold metaOut at HMO
  icases HMO with ⟨O0, O4, O8, O12, O16, O20, O24, O28, O32, O36, -, O48, -, O60, -, -, -⟩
  -- drop `spec` (ps, 8, 8)
  mstep; mstep; mstep
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)] (F + 1) (s - 160 + 48) ps 8 8 (by decide)
      (by omega))
    using [O0 O4 O8 Hinv Hps]
  · iunfold pre747
    ihave O0 := memBytes_addr (b := (s - 160 + 48).toNat) (by omega) $$ O0
    ihave O4 := memBytes_addr (b := (s - 160 + 48).toNat + 4) (by omega) $$ O4
    ihave O8 := memBytes_addr (b := (s - 160 + 48).toNat + 8) (by omega) $$ O8
    iframe O0 O4 O8 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists specStr
    iframe Hps
    ipureintro; rfl
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, -, -, -, Hinv⟩
  subst hrs
  have hl2 : [(py.toNat, 5), (pn.toNat, 27), (ps.toNat, 8), (p.toNat, 1)].erase (ps.toNat, (8 : UInt32).toNat) =
      [(py.toNat, 5), (pn.toNat, 27), (p.toNat, 1)] := by simp
  rw [hl2]
  -- drop `name` (pn, 27, 27)
  mstep; mstep; mstep
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(py.toNat, 5), (pn.toNat, 27), (p.toNat, 1)] (F + 1 + 1) (s - 160 + 60) pn 27 27 (by decide)
      (by omega))
    using [O12 O16 O20 Hinv Hpn]
  · iunfold pre747
    ihave O12 := memBytes_addr (b := (s - 160 + 60).toNat) (by omega) $$ O12
    ihave O16 := memBytes_addr (b := (s - 160 + 60).toNat + 4) (by omega) $$ O16
    ihave O20 := memBytes_addr (b := (s - 160 + 60).toNat + 8) (by omega) $$ O20
    iframe O12 O16 O20 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists nameStr
    iframe Hpn
    ipureintro; rfl
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, -, -, -, Hinv⟩
  subst hrs
  have hl3 : [(py.toNat, 5), (pn.toNat, 27), (p.toNat, 1)].erase (pn.toNat, (27 : UInt32).toNat) =
      [(py.toNat, 5), (p.toNat, 1)] := by simp
  rw [hl3]
  -- drop `symbol` (py, 5, 5)
  mstep; mstep; mstep; mstep; mstep
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(py.toNat, 5), (p.toNat, 1)] (F + 1 + 1 + 1) (s - 160 + 48 + 24) py 5 5 (by decide) (by omega))
    using [O24 O28 O32 Hinv Hpy]
  · iunfold pre747
    ihave O24 := memBytes_addr (b := (s - 160 + 48 + 24).toNat) (by omega) $$ O24
    ihave O28 := memBytes_addr (b := (s - 160 + 48 + 24).toNat + 4) (by omega) $$ O28
    ihave O32 := memBytes_addr (b := (s - 160 + 48 + 24).toNat + 8) (by omega) $$ O32
    iframe O24 O28 O32 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists symbolStr
    iframe Hpy
    ipureintro; rfl
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, -, -, -, Hinv⟩
  subst hrs
  have hl4 : [(py.toNat, 5), (p.toNat, 1)].erase (py.toNat, (5 : UInt32).toNat) = [(p.toNat, 1)] := by simp
  rw [hl4]
  -- the two `None`s (147), the third skipped
  mstep; mstep; mstep
  mcall (MetadataFields.f147_none cfg lim (d + 1) types[0]! rfl inst mi n hn Cg (s - 160 + 84)) using [O36]
  · isplitr
    · ipureintro; trivial
    iapply memBytes_addr (by omega) $$ O36
  icases HQ with ⟨%hrs, O36⟩
  subst hrs
  mstep; mstep; mstep
  mcall (MetadataFields.f147_none cfg lim (d + 1) types[0]! rfl inst mi n hn Cg (s - 160 + 96)) using [O48]
  · isplitr
    · ipureintro; trivial
    iapply memBytes_addr (by omega) $$ O48
  icases HQ with ⟨%hrs, O48⟩
  subst hrs
  ihave O60 := memBytes_addr (b := (s - 160).toNat + 108) (by omega) $$ O60
  repeat mstep
  mstep [O60]
  repeat mstep
  -- drop the prefix's `Vec` (p, 1, 1)
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(p.toNat, 1)] (F + 1 + 1 + 1 + 1) (s - 160 + 8 + 24) p 1 1 (by decide) (by omega))
    using [V0 V4 V8 Hinv Hp]
  · iunfold pre747
    ihave V0 := memBytes_addr (b := (s - 160 + 8 + 24).toNat) (by omega) $$ V0
    ihave V4 := memBytes_addr (b := (s - 160 + 8 + 24).toNat + 4) (by omega) $$ V4
    ihave V8 := memBytes_addr (b := (s - 160 + 8 + 24).toNat + 8) (by omega) $$ V8
    iframe V0 V4 V8 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists WNear.accountsPrefix
    iframe Hp
    ipureintro; rw [StateReadModel.accountsPrefix_length]; rfl
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, -⟩
  subst hrs
  -- the epilogue
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 160 + 160 = s by simp]
  mcredits R
  iapply W $$ Hc Hg Hh

end SegC

end WNear.Binary.FtMetadataBody
