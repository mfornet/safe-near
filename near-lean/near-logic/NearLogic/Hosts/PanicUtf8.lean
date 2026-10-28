import NearLogic.Hosts.StorageRead
import NearLogic.CallTrap

/-!
# `panic_utf8`, metered

The host contract of `panic_utf8(len, ptr)` with the message in memory: when
the message fits the remaining log length, its per-byte read cost fits a
`u64`, and it is valid UTF-8, the call traps with the guest panic carrying the
message, leaves memory alone, sets `lastError`, and uses exactly its charges
(`panicUtf8Charges`).
-/

namespace NearLogic

open Wasm Wasm.Near

open private viewCharges baseCharge from NearVM.LogRead

/-- The charges of `panic_utf8` of an `n`-byte message in memory. -/
def panicUtf8Charges (n : Nat) : List Charge :=
  [.ext "base", .ext "utf8_decoding_base", .ext "read_memory_base", .ext "read_memory_byte" n,
    .ext "utf8_decoding_byte" n]

/-- The gas `panic_utf8` uses for a message of `n` bytes. -/
def panicUtf8Use (h : NearState) (n : Nat) : Nat := chargesUse h (panicUtf8Charges n)

/-- The trap reason of a panic with the message `bs`. -/
def panicUtf8Reason (bs : List UInt8) : Trap := .host (HostError.guestPanic (utf8String bs)).message

/-- A message of `n` bytes fits the remaining total log length. -/
def LogFits (h : NearState) (n : Nat) : Prop :=
  ∀ limit, h.config.maxLogLen = some limit → (h.logs.map List.length).sum + n ≤ limit

theorem panicUtf8Read_mem (st : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max)
    (hfit : LogFits st.host len.toNat)
    (hov : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize st)
    (hutf : validUtf8 (st.mem.readList ptr.toNat len.toNat) = true) :
    panicUtf8Read st len ptr =
      ⟨[ext1 "base", ext1 "utf8_decoding_base", ext1 "read_memory_base",
        ext1 "read_memory_byte" len.toNat, ext1 "utf8_decoding_byte" len.toNat],
        .ok (st.mem.readList ptr.toNat len.toNat)⟩ := by
  have hsp : ¬ len.toNat > logSpace st := by
    unfold logSpace totalLogLength
    cases hm : st.host.config.maxLogLen with
    | none => have := len.toNat_lt; simp only; omega
    | some l => have := hfit l hm; simp only; omega
  have hpo : payPerOverflows st "read_memory_byte" len.toNat = false := by
    simp [payPerOverflows]; omega
  have hin' : ¬ ptr.toNat + len.toNat > memorySize st := by omega
  simp [panicUtf8Read, readUtf8String, hlen, hsp, viewCharges, hpo, hin', hutf, Memory.readList_length,
    baseCharge]

theorem chargesBefore_panicUtf8 (st : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max)
    (hfit : LogFits st.host len.toNat)
    (hov : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize st)
    (hutf : validUtf8 (st.mem.readList ptr.toNat len.toNat) = true) :
    chargesBefore "panic_utf8" st [.i64 len, .i64 ptr] = panicUtf8Charges len.toNat := by
  have hs : storageMutationPlan? "panic_utf8" st [.i64 len, .i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hpre : "panic_utf8".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, stringHostRead?,
    panicUtf8Read_mem st len ptr hlen hfit hov hin hutf, extCharges, ext1, panicUtf8Charges]

theorem preInvokeError_panicUtf8 (st : HostStore NearState) (args : List Value) :
    preInvokeError "panic_utf8" st args = none := by
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
    creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
    functionCallInputError, functionCallInputs?]

theorem panicUtf8_ok (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) {C : Nat}
    (hlen : len ≠ u64Max) (hfit : LogFits st.host len.toNat)
    (hov : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize st)
    (hutf : validUtf8 (st.mem.readList ptr.toNat len.toNat) = true)
    (h1 : st.host.gas.used + panicUtf8Use st.host len.toNat ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "panic_utf8" panicUtf8Metered).invoke st [.i64 len, .i64 ptr] =
        .Trap { mem := st.mem, host := host' }
          (HostError.guestPanic (utf8String (st.mem.readList ptr.toNat len.toNat))).message ∧
      erase host' = erase { st.host with
        lastError := some (.guestPanic (utf8String (st.mem.readList ptr.toNat len.toNat))) } ∧
      host'.gas.used = st.host.gas.used + panicUtf8Use st.host len.toNat ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hdep : deprecatedRuntimeHost "panic_utf8" = false := by decide
  have hview : viewRestrictedHost "panic_utf8" = false := by decide
  have hother : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "panic_utf8" = false := by decide
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (panicUtf8Charges len.toNat) h1 h2 h3
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [chargesBefore_panicUtf8 st len ptr hlen hfit hov hin hutf]
  generalize hac : applyCharges st.host (panicUtf8Charges len.toNat) = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  rw [preInvokeError_panicUtf8]
  simp only
  show ∃ host', invokeStorageCall extra "panic_utf8" panicUtf8Metered
    { mem := st.mem, host := afterCharges ns } [.i64 len, .i64 ptr] = _ ∧ _
  have he1 : erase (afterCharges ns) = erase st.host := by rw [erase_afterCharges, hch.erase]
  have fcfg : (afterCharges ns).config = st.host.config := erase_field he1 NearState.config fun _ => rfl
  have flogs : (afterCharges ns).logs = st.host.logs := erase_field he1 NearState.logs fun _ => rfl
  have fext : (afterCharges ns).extCosts = st.host.extCosts :=
    erase_field he1 NearState.extCosts fun _ => rfl
  have hread := panicUtf8Read_mem { mem := st.mem, host := afterCharges ns } len ptr hlen
    (by unfold LogFits; rw [fcfg, flogs]; exact hfit) (by rw [fext]; exact hov) hin hutf
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother, panicUtf8Metered, hread,
    finishMeteredCall, trapWith]
  refine ⟨_, rfl, ?_, hch.used, hch.maxBurnt, hch.prepaid⟩
  exact congrArg (fun x : NearState => { x with
    lastError := some (.guestPanic (utf8String (st.mem.readList ptr.toNat len.toNat))) }) he1

theorem panicUtf8Use_erase {h h' : NearState} (he : erase h = erase h') (n : Nat) :
    panicUtf8Use h n = panicUtf8Use h' n :=
  chargesUse_erase he _

/-- `panic_utf8` of the `len` bytes `bs` at `ptr`, as a trap contract. -/
theorem panicUtf8_trapContract (extra : Nat) (h : NearState) (len ptr : UInt64) (bs : List UInt8)
    {C : Nat} (hlen : len ≠ u64Max) (hkl : bs.length = len.toNat) (hpos : 0 < len.toNat)
    (hutf : validUtf8 bs = true) (hfit : LogFits h len.toNat)
    (hov : h.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64) :
    TrapContractP (metered extra "panic_utf8" panicUtf8Metered).toHostFn h
      (fun h' => erase h' = erase { h with lastError := some (.guestPanic (utf8String bs)) })
      [.i64 len, .i64 ptr] (panicUtf8Reason bs) ptr.toNat bs (panicUtf8Use h len.toNat) C := by
  intro host mem hwf he hrd hu hmb hpp
  have fcfg : host.config = h.config := erase_field he NearState.config fun _ => rfl
  have flogs : host.logs = h.logs := erase_field he NearState.logs fun _ => rfl
  have fext : host.extCosts = h.extCosts := erase_field he NearState.extCosts fun _ => rfl
  have hin : ptr.toNat + len.toNat ≤ memorySize { mem, host } := by
    have := (hrd (len.toNat - 1) (by omega)).1
    unfold Memory.byteSize at this
    show _ ≤ mem.pages.size * 65536
    unfold pageSize at this
    omega
  have hread : mem.readList ptr.toNat len.toNat = bs := by
    rw [← hkl]; exact readList_eq fun k hk => (hrd k hk).2
  rw [← panicUtf8Use_erase he] at hu ⊢
  obtain ⟨host', hinv, her, hused, hmb', hpp'⟩ := panicUtf8_ok extra { mem, host } len ptr (C := C) hlen
    (by unfold LogFits; rw [fcfg, flogs]; exact hfit) (by rw [fext]; exact hov) hin
    (by simp only; rw [hread]; exact hutf) hu hmb hpp
  simp only [hread] at hinv her
  refine ⟨host', ?_, ?_, Nat.le_of_eq hused, hmb', hpp'⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv, panicUtf8Reason]
  · show erase host' = _
    rw [her]
    exact congrArg (fun x : NearState => { x with lastError := some (.guestPanic (utf8String bs)) }) he

end NearLogic
