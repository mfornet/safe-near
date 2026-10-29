import Bridge.Functions.DepositF232Spec

/-!
# What 232 leaves of the host (M8)

From the chain of host relations of `Post232` (`contains_key`, the registration's write on a new
account, `internal_deposit`'s read and write, the log), what the method needs:

* `post232_out`: the storage is the entry host's with the account's record `key ↦ nv`, the keys
  grow by `key`, the usage grows by the new record on a new account (`du232`), what `keep` holds
  is the entry host's with the log appended, and the accounting is a canonical trie linked to the
  storage, the recorded proof's budget spent by at most `4·lookup + 48`.
-/

namespace WNear.Binary.DepositBody

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open WNear.Binary.NewBody (Keep keep keep_of_erase keep_acc keep_storageReadRegs keep_storageWriteHost)
open WNear.Binary.InternalDeposit (Post406)
open WNear.Binary.StorageWrite (evictedRegister)
open WNear.Binary.StorageBalanceBounds (u128Of)
open WNear.Binary.DepositTail (logText)
open WNear.Binary.EnvGetters (depLo depHi)
open Near.TrieOverlay

/-! ## One step at a time -/

theorem storageReadRegs_keys (x : NearState) (r : UInt64) (v : Option (List UInt8)) :
    (storageReadRegs x r v).storageKeys = x.storageKeys :=
  storageReadRegs_field NearState.storageKeys (fun _ _ _ => rfl) x r v

theorem storageReadRegs_usage (x : NearState) (r : UInt64) (v : Option (List UInt8)) :
    (storageReadRegs x r v).context.storageUsage = x.context.storageUsage :=
  storageReadRegs_field (fun y : NearState => y.context.storageUsage) (fun _ _ _ => rfl) x r v

theorem write_storage {e : Nat} {x h2 : NearState} {k v : List UInt8} {r : UInt64} {s : Near.TrieOverlay.State}
    (he : erase h2 = erase (storageWriteHost e x k v r s)) :
    h2.storage = fun k' => if k' = k then some v else x.storage k' := by
  rw [erase_field he NearState.storage fun _ => rfl, storageWriteHost_storage]

theorem write_keys {e : Nat} {x h2 : NearState} {k v : List UInt8} {r : UInt64} {s : Near.TrieOverlay.State}
    (he : erase h2 = erase (storageWriteHost e x k v r s)) (k' : List UInt8) :
    k' ∈ h2.storageKeys ↔ k' ∈ x.storageKeys ∨ k' = k := by
  rw [erase_field he NearState.storageKeys fun _ => rfl]
  unfold storageWriteHost logWrite
  simp only [NearState.invalidateIterators, NearState.setStorage, storageReadRegs_keys]
  split
  · rename_i hc
    constructor
    · intro hk; exact Or.inl hk
    · rintro (hk | rfl)
      · exact hk
      · simpa using hc
  · simp

theorem write_usage {e : Nat} {x h2 : NearState} {k v : List UInt8} {r : UInt64} {s : Near.TrieOverlay.State}
    (he : erase h2 = erase (storageWriteHost e x k v r s)) :
    h2.context.storageUsage = UInt64.ofNat (writeUsage e k v (x.storage k) x.context.storageUsage.toNat) := by
  rw [erase_field he (fun y : NearState => y.context.storageUsage) fun _ => rfl]
  unfold storageWriteHost logWrite; rfl

theorem keep_logged_congr {x y : NearState} (hk : keep x = keep y) (t : List UInt8) :
    keep (LogStr.logged x t) = keep (LogStr.logged y t) := by
  have hl : x.logs = y.logs := congrArg Keep.logs hk
  simp only [keep, LogStr.logged, hl] at hk ⊢
  simp only [Keep.mk.injEq] at hk ⊢
  tauto

/-- What 406 leaves: the record written, the accounting's next state. -/
theorem post406_out {e : Nat} {h h2 : NearState} {k nv : List UInt8} {st : Near.TrieOverlay.State} {bud : Nat}
    (hp : Post406 e h k nv st bud h2)
    (hb : readProofCost (contractKey h.context.currentAccountId k) (h.storage k) +
      writeProofCost (contractKey h.context.currentAccountId k) (h.storage k) ≤ bud) :
    h2.storage = (fun k' => if k' = k then some nv else h.storage k') ∧
    (∀ k', k' ∈ h2.storageKeys ↔ k' ∈ h.storageKeys ∨ k' = k) ∧
    h2.context.storageUsage = UInt64.ofNat (writeUsage e k nv (h.storage k) h.context.storageUsage.toNat) ∧
    keep h2 = keep h ∧
    ∃ s', h2.storageAccounting = some s' ∧ Canon s' ∧ StorageLink h2 s' ∧
      ProofBudget h2 s' (bud - readProofCost (contractKey h.context.currentAccountId k) (h.storage k) -
        writeProofCost (contractKey h.context.currentAccountId k) (h.storage k)) := by
  obtain ⟨h1, s1, -, hacc1, hc1, hl1, hp1, he1, hw⟩ := hp
  have hst1 : h1.storage = h.storage :=
    (erase_field he1 NearState.storage fun _ => rfl).trans (storageReadRegs_field NearState.storage (fun _ _ _ => rfl) _ _ _)
  have hkp1 : keep h1 = keep h := by rw [keep_of_erase he1, keep_storageReadRegs, keep_acc]
  have hid1 : h1.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hkp1
  have hk1 : h1.storageKeys = h.storageKeys :=
    (erase_field he1 NearState.storageKeys fun _ => rfl).trans (storageReadRegs_keys _ _ _)
  have hu1 : h1.context.storageUsage = h.context.storageUsage :=
    (erase_field he1 (fun y : NearState => y.context.storageUsage) fun _ => rfl).trans (storageReadRegs_usage _ _ _)
  obtain ⟨s2, hacc2, hc2, hl2, hp2, he2⟩ := StorageWritePost.next hw hc1 hl1 hp1
    (by rw [hid1, hst1]; omega)
  refine ⟨?_, ?_, ?_, ?_, s2, hacc2, hc2, hl2, ?_⟩
  · rw [write_storage he2, hst1]
  · intro k'; rw [write_keys he2, hk1]
  · rw [write_usage he2, hst1, hu1]
  · rw [keep_of_erase he2, keep_storageWriteHost, hkp1]
  · rw [hid1, hst1] at hp2; exact hp2

theorem predecessorHost_fields (h : NearState) :
    (predecessorHost h 0).storage = h.storage ∧ (predecessorHost h 0).storageKeys = h.storageKeys ∧
      (predecessorHost h 0).context = h.context := by
  simp [predecessorHost, u64Max, NearState.setRegister]

/-! ## The cost of 232 on hosts that differ in registers and accounting -/

theorem cost526_congr (cfg : WasmConfig) (F : Nat) {x y : NearState} (hk : keep x = keep y)
    (hc : x.context = y.context) : PredecessorId.cost526 cfg F x = PredecessorId.cost526 cfg F y := by
  have hs := NewBody.sameCost_of_keep hk
  have e : ∀ z : NearState, predecessorHost z 0 = z.setRegister (0 : UInt64).toNat z.context.predecessorAccountId := by
    intro z; simp [predecessorHost, u64Max]
  have hp := hs.setRegister (0 : UInt64).toNat y.context.predecessorAccountId
  have hr : ∀ (z : NearState) (v : List UInt8), (z.setRegister (0 : UInt64).toNat v).registers (0 : UInt64).toNat =
      some v := by intro z v; simp [NearState.setRegister]
  simp only [PredecessorId.cost526, predecessorUse, NewBody.chargesUse_congr hs, ReadRegisterF.cost523F, e, hr,
    registerLenUse, ReadRegisterF.costRestF, readRegisterUse, hc]
  rw [NewBody.chargesUse_congr hp, NewBody.chargesUse_congr hp]

theorem keep_predecessorHost_congr {x y : NearState} (hk : keep x = keep y) :
    keep (predecessorHost x 0) = keep (predecessorHost y 0) := by
  rw [keep_predecessorHost, keep_predecessorHost, hk]

theorem cost232_congr (cfg : WasmConfig) (F : Nat) (pl : UInt32) {x y : NearState} (hk : keep x = keep y)
    (hc : x.context = y.context) (hs : x.storage = y.storage) (key : List UInt8) (reg : Option (UInt64 × UInt64))
    (xb : List UInt8) (t0 t1 : UInt64) (K879 K664s K664p : Nat → Keep → Nat) :
    cost232 cfg F pl x key reg xb t0 t1 K879 K664s K664p = cost232 cfg F pl y key reg xb t0 t1 K879 K664s K664p := by
  have hsc := NewBody.sameCost_of_keep hk
  have hdep : x.context.attachedDeposit = y.context.attachedDeposit := by rw [hc]
  have hpred : x.context.predecessorAccountId = y.context.predecessorAccountId := by rw [hc]
  have h1 : attachedDepositUse x = attachedDepositUse y := NewBody.chargesUse_congr hsc _
  have h2 := cost526_congr cfg F hk hc
  have h3 : ∀ F' pl' L' k', LookupMapContains.cost394 cfg F' pl' L' (predecessorHost x 0) k' =
      LookupMapContains.cost394 cfg F' pl' L' (predecessorHost y 0) k' :=
    fun F' pl' L' k' => DepositCosts.cost394_congr cfg F' pl' L' (keep_predecessorHost_congr hk) k'
  have h4 : ∀ F' pl' L' k' x0 x1 t0 t1 lo hi ab, DepositSegAll.costSegAll cfg F' pl' L' x k' x0 x1 t0 t1 lo hi ab K879 =
      DepositSegAll.costSegAll cfg F' pl' L' y k' x0 x1 t0 t1 lo hi ab K879 :=
    fun F' pl' L' k' x0 x1 t0 t1 lo hi ab => DepositCosts.costSegAll_congr cfg F' pl' L' hk (by rw [hs]) _ _ _ _ _ _ _ _
  have h5 : ∀ F' pl' L' k' v, DepositSegAll.costSegAll cfg F' pl' L' (withVal x key v) k' 0 0 t0 t1 =
      DepositSegAll.costSegAll cfg F' pl' L' (withVal y key v) k' 0 0 t0 t1 := by
    intro F' pl' L' k' v; funext lo hi ab K
    exact DepositCosts.costSegAll_congr cfg F' pl' L' (by rw [keep_withVal, keep_withVal, hk])
      (by simp [withVal, hs]) _ _ _ _ _ _ _ _
  have h6 : ∀ F' pl' L' k', LookupMapOps.cost401 cfg F' pl' L' x k' = LookupMapOps.cost401 cfg F' pl' L' y k' := by
    intro F' pl' L' k'
    simp only [LookupMapOps.cost401, NewBody.storageWriteUse_congr hsc (by rw [hs])]
  unfold cost232 costPos costReg costUnreg aloOf ahiOf depOf depLo depHi
  simp only [hdep, hpred, h1, h2, h3, h4, h5, h6, hk]

/-! ## The whole of 232 -/

/-- The account's new record. -/
def nv232 (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) : List UInt8 :=
  match reg with
  | some (x0, x1) => u128Of (x0.toNat + 2 ^ 64 * x1.toNat + depOf h)
  | none => u128Of (0 + 2 ^ 64 * 0 + ((aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat))

/-- The log's bytes. -/
def text232 (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) : List UInt8 :=
  match reg with
  | some _ => logText (depLo h) (depHi h) h.context.predecessorAccountId
  | none => logText (aloOf h xb) (ahiOf h xb) h.context.predecessorAccountId

/-- The usage 232 leaves. -/
def usage232 (e : Nat) (h : NearState) (key : List UInt8) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) :
    UInt64 :=
  match reg with
  | some _ => h.context.storageUsage
  | none => UInt64.ofNat (writeUsage e key (nv232 h none xb) (some zeros)
      (UInt64.ofNat (writeUsage e key zeros none h.context.storageUsage.toNat)).toNat)

open EnvGetters in
theorem post232_out {e : Nat} {h h' : NearState} {key : List UInt8} {reg : Option (UInt64 × UInt64)}
    {xb : List UInt8} {st : Near.TrieOverlay.State} {bud : Nat}
    (hp : Post232 e h key reg xb st bud h')
    (hbud : 4 * lookupProofBound (contractKey h.context.currentAccountId key) + 48 ≤ bud)
    (hstore : h.storage key = reg.map fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8) :
    (∀ k, h'.storage k = if k = key then some (nv232 h reg xb) else h.storage k) ∧
    (∀ k, k ∈ h'.storageKeys ↔ k ∈ h.storageKeys ∨ k = key) ∧
    h'.context.storageUsage = usage232 e h key reg xb ∧
    keep h' = keep (LogStr.logged h (text232 h reg xb)) ∧
    ∃ s', h'.storageAccounting = some s' ∧ Canon s' ∧ StorageLink h' s' ∧
      ProofBudget h' s' (bud - (4 * lookupProofBound (contractKey h.context.currentAccountId key) + 48)) := by
  obtain ⟨f1s, f1k, f1x⟩ := predecessorHost_fields h
  have hk1 : keep (predecessorHost h 0) = keep h := keep_predecessorHost h
  cases reg with
  | some p =>
    obtain ⟨x0, x1⟩ := p
    obtain ⟨h2, s2, h3, -, -, -, -, -, he2, hp406, rfl⟩ := hp
    have hs2 : h2.storage = h.storage := by rw [erase_field he2 NearState.storage fun _ => rfl]; exact f1s
    have hkk2 : h2.storageKeys = h.storageKeys := by rw [erase_field he2 NearState.storageKeys fun _ => rfl]; exact f1k
    have hu2 : h2.context.storageUsage = h.context.storageUsage := by
      rw [erase_field he2 (fun y : NearState => y.context.storageUsage) fun _ => rfl]; rw [f1x]
    have hkp2 : keep h2 = keep h := by rw [keep_of_erase he2, keep_acc, hk1]
    have hid2 : h2.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hkp2
    obtain ⟨o1, o2, o3, o4, s', o5, o6, o7, o8⟩ := post406_out hp406
      (by rw [hid2, hs2, hstore]; simp [readProofCost, writeProofCost]; omega)
    refine ⟨?_, ?_, ?_, ?_, s', o5, o6, (fun k => o7 k), ?_⟩
    · intro k; show (LogStr.logged h3 _).storage k = _; simp only [LogStr.logged]; rw [o1, hs2]; rfl
    · intro k; show k ∈ (LogStr.logged h3 _).storageKeys ↔ _; simp only [LogStr.logged]; rw [o2, hkk2]
    · show (LogStr.logged h3 _).context.storageUsage = _
      simp only [LogStr.logged, usage232]
      rw [o3, hs2, hstore, hu2]
      simp [writeUsage, nv232]
    · exact keep_logged_congr (o4.trans hkp2) _
    · refine (o8.congr rfl rfl).mono ?_
      rw [hid2, hs2, hstore]; simp [readProofCost, writeProofCost]; omega
  | none =>
    obtain ⟨h2, s2, h3, s3, h4, -, -, hc2, hl2, hp2, he2, -, -, -, -, -, he3, hp406, rfl⟩ := hp
    have hs2 : h2.storage = h.storage := by rw [erase_field he2 NearState.storage fun _ => rfl]; exact f1s
    have hkk2 : h2.storageKeys = h.storageKeys := by rw [erase_field he2 NearState.storageKeys fun _ => rfl]; exact f1k
    have hu2 : h2.context.storageUsage = h.context.storageUsage := by
      rw [erase_field he2 (fun y : NearState => y.context.storageUsage) fun _ => rfl]; rw [f1x]
    have hkp2 : keep h2 = keep h := by rw [keep_of_erase he2, keep_acc, hk1]
    have hkp3 : keep h3 = keep h := by rw [keep_of_erase he3, keep_storageWriteHost, hkp2]
    have hid3 : h3.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hkp3
    have hs3 := write_storage he3
    have hs3k : h3.storage key = some zeros := by rw [hs3]; simp
    obtain ⟨o1, o2, o3, o4, s', o5, o6, o7, o8⟩ := post406_out hp406
      (by rw [hid3, hs3k]; simp [readProofCost, writeProofCost]; omega)
    refine ⟨?_, ?_, ?_, ?_, s', o5, o6, (fun k => o7 k), ?_⟩
    · intro k; show (LogStr.logged h4 _).storage k = _; simp only [LogStr.logged]; rw [o1, hs3, hs2]
      by_cases hk : k = key <;> simp [hk, nv232]
    · intro k; show k ∈ (LogStr.logged h4 _).storageKeys ↔ _; simp only [LogStr.logged]
      rw [o2, write_keys he3, hkk2]; tauto
    · show (LogStr.logged h4 _).context.storageUsage = _
      simp only [LogStr.logged, usage232]
      rw [o3, hs3k, write_usage he3, hs2, hstore, hu2]
      rfl
    · exact keep_logged_congr (o4.trans hkp3) _
    · refine (o8.congr rfl rfl).mono ?_
      rw [hid3, hs3k]; simp [readProofCost, writeProofCost]; omega

end WNear.Binary.DepositBody
