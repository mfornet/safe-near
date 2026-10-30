import NearLogic.Hosts.PanicUtf8

/-!
# `log_utf8`, metered

The host contract of `log_utf8(len, ptr)` with the message in memory: when the log count has
room (`LogRoom`), the message fits the remaining log length (`LogFits`), its per-byte read cost
fits a `u64`, and it is valid UTF-8, the call returns with no values, leaves memory alone,
appends the message to the logs, and uses exactly its charges (`logUtf8Charges`: those of
`panic_utf8`, then `log_base` and `log_byte`).

* `logUtf8_ok`: the metered call on a store.
* `logUtf8_readContract`: the call as a `ReadContract`, the host `h` with the message logged.
-/

namespace NearLogic

open Wasm Wasm.Near

open private viewCharges baseCharge from NearVM.LogRead

/-- The charges of `log_utf8` of an `n`-byte message in memory. -/
def logUtf8Charges (n : Nat) : List Charge :=
  [.ext "base", .ext "utf8_decoding_base", .ext "read_memory_base", .ext "read_memory_byte" n,
    .ext "utf8_decoding_byte" n, .ext "log_base", .ext "log_byte" n]

/-- The gas `log_utf8` uses for a message of `n` bytes. -/
def logUtf8Use (h : NearState) (n : Nat) : Nat := chargesUse h (logUtf8Charges n)

/-- One more message fits the number of logs. -/
def LogRoom (h : NearState) : Prop :=
  ∀ limit, h.config.maxNumberLogs = some limit → h.logs.length < limit

theorem logCountError_none (st : HostStore NearState) (hroom : LogRoom st.host) : logCountError st = none := by
  unfold logCountError
  cases hm : st.host.config.maxNumberLogs with
  | none => rfl
  | some l =>
    have := hroom l hm
    simp only
    rw [if_neg (by omega)]

theorem logUtf8Read_mem (st : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max)
    (hroom : LogRoom st.host) (hfit : LogFits st.host len.toNat)
    (hov : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize st)
    (hutf : validUtf8 (st.mem.readList ptr.toNat len.toNat) = true) :
    logUtf8Read st len ptr =
      ⟨[ext1 "base", ext1 "utf8_decoding_base", ext1 "read_memory_base",
        ext1 "read_memory_byte" len.toNat, ext1 "utf8_decoding_byte" len.toNat, ext1 "log_base",
        ext1 "log_byte" len.toNat], .ok (st.mem.readList ptr.toNat len.toNat)⟩ := by
  have hsp : ¬ len.toNat > logSpace st := by
    unfold logSpace totalLogLength
    cases hm : st.host.config.maxLogLen with
    | none => have := len.toNat_lt; simp only; omega
    | some l => have := hfit l hm; simp only; omega
  have hpo : payPerOverflows st "read_memory_byte" len.toNat = false := by
    simp [payPerOverflows]; omega
  have hin' : ¬ ptr.toNat + len.toNat > memorySize st := by omega
  have hrd : readUtf8String st len ptr =
      ⟨[ext1 "utf8_decoding_base", ext1 "read_memory_base", ext1 "read_memory_byte" len.toNat,
        ext1 "utf8_decoding_byte" len.toNat], .ok (st.mem.readList ptr.toNat len.toNat)⟩ := by
    simp [readUtf8String, hlen, hsp, viewCharges, hpo, hin', hutf, Memory.readList_length]
  have hfin : ∀ limit, st.host.config.maxLogLen = some limit → ¬ totalLogLength st + len.toNat > limit := by
    intro l hl; have := hfit l hl; unfold totalLogLength; omega
  unfold logUtf8Read
  rw [logCountError_none st hroom]
  simp only [hrd, finishLog, Memory.readList_length, baseCharge]
  cases hm : st.host.config.maxLogLen with
  | none => rfl
  | some l => simp only; rw [if_neg (hfin l hm)]; rfl

theorem chargesBefore_logUtf8 (st : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max)
    (hroom : LogRoom st.host) (hfit : LogFits st.host len.toNat)
    (hov : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize st)
    (hutf : validUtf8 (st.mem.readList ptr.toNat len.toNat) = true) :
    chargesBefore "log_utf8" st [.i64 len, .i64 ptr] = logUtf8Charges len.toNat := by
  have hs : storageMutationPlan? "log_utf8" st [.i64 len, .i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hpre : "log_utf8".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, stringHostRead?,
    logUtf8Read_mem st len ptr hlen hroom hfit hov hin hutf, extCharges, ext1, logUtf8Charges]

theorem preInvokeError_logUtf8 (st : HostStore NearState) (args : List Value) :
    preInvokeError "log_utf8" st args = none := by
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
    creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
    functionCallInputError, functionCallInputs?]

/-- After the charges, `log_utf8` itself and its post-call metering. -/
theorem logUtf8_after (extra : Nat) (s : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max)
    (hroom : LogRoom s.host) (hfit : LogFits s.host len.toNat)
    (hov : s.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize s)
    (hutf : validUtf8 (s.mem.readList ptr.toNat len.toNat) = true) :
    invokeStorageCall extra "log_utf8" logUtf8Fn s [.i64 len, .i64 ptr] =
      .Return [] { s with host := { s.host with logs := s.host.logs ++ [s.mem.readList ptr.toNat len.toNat] } } := by
  have hother : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "log_utf8" = false := by decide
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother]
  simp only [logUtf8Fn, logUtf8Read_mem s len ptr hlen hroom hfit hov hin hutf, appendLogResult,
    finishMeteredCall]
  have hc : ¬ "log_utf8" ∈ cryptoHostNames := by decide
  simp [chargesAfter, hc, applyCharges, deductDeposit, promiseDeposit?, actionMethodEncodingError,
    actionMethodBytes?, usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

theorem erase_withLogs (x : NearState) (l : List (List UInt8)) :
    erase { x with logs := l } = { erase x with logs := l } := rfl

theorem logUtf8_ok (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) {C : Nat}
    (hlen : len ≠ u64Max) (hroom : LogRoom st.host) (hfit : LogFits st.host len.toNat)
    (hov : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hin : ptr.toNat + len.toNat ≤ memorySize st)
    (hutf : validUtf8 (st.mem.readList ptr.toNat len.toNat) = true)
    (h1 : st.host.gas.used + logUtf8Use st.host len.toNat ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 len, .i64 ptr] =
        .Return [] { mem := st.mem, host := host' } ∧
      erase host' = erase { st.host with logs := st.host.logs ++ [st.mem.readList ptr.toNat len.toNat] } ∧
      host'.gas.used = st.host.gas.used + logUtf8Use st.host len.toNat ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hdep : deprecatedRuntimeHost "log_utf8" = false := by decide
  have hview : viewRestrictedHost "log_utf8" = false := by decide
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (logUtf8Charges len.toNat) h1 h2 h3
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [chargesBefore_logUtf8 st len ptr hlen hroom hfit hov hin hutf]
  generalize hac : applyCharges st.host (logUtf8Charges len.toNat) = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  rw [preInvokeError_logUtf8]
  simp only
  show ∃ host', invokeStorageCall extra "log_utf8" logUtf8Fn
    { mem := st.mem, host := afterCharges ns } [.i64 len, .i64 ptr] = _ ∧ _
  have he1 : erase (afterCharges ns) = erase st.host := by rw [erase_afterCharges, hch.erase]
  have fcfg : (afterCharges ns).config = st.host.config := erase_field he1 NearState.config fun _ => rfl
  have flogs : (afterCharges ns).logs = st.host.logs := erase_field he1 NearState.logs fun _ => rfl
  have fext : (afterCharges ns).extCosts = st.host.extCosts :=
    erase_field he1 NearState.extCosts fun _ => rfl
  rw [logUtf8_after extra { mem := st.mem, host := afterCharges ns } len ptr hlen
    (by unfold LogRoom; rw [fcfg, flogs]; exact hroom) (by unfold LogFits; rw [fcfg, flogs]; exact hfit)
    (by rw [fext]; exact hov) hin hutf]
  refine ⟨_, rfl, ?_, hch.used, hch.maxBurnt, hch.prepaid⟩
  show erase { afterCharges ns with logs := (afterCharges ns).logs ++ [st.mem.readList ptr.toNat len.toNat] } = _
  rw [erase_withLogs, flogs, he1]
  rfl

theorem logUtf8Use_erase {h h' : NearState} (he : erase h = erase h') (n : Nat) :
    logUtf8Use h n = logUtf8Use h' n :=
  chargesUse_erase he _

/-- **`log_utf8`, metered**, of the `len` bytes `bs` at `ptr`, as a read contract: the host `h` with
`bs` appended to its logs, the gas `logUtf8Use`. -/
theorem logUtf8_readContract (extra : Nat) (h : NearState) (len ptr : UInt64) (bs : List UInt8)
    {C : Nat} (hlen : len ≠ u64Max) (hkl : bs.length = len.toNat) (hpos : 0 < len.toNat)
    (hutf : validUtf8 bs = true) (hroom : LogRoom h) (hfit : LogFits h len.toNat)
    (hov : h.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64) :
    ReadContract (metered extra "log_utf8" logUtf8Fn).toHostFn h { h with logs := h.logs ++ [bs] }
      [.i64 len, .i64 ptr] [] ptr.toNat bs (logUtf8Use h len.toNat) C := by
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
  rw [← logUtf8Use_erase he] at hu ⊢
  obtain ⟨host', hinv, her, hused, hmb', hpp'⟩ := logUtf8_ok extra { mem, host } len ptr (C := C) hlen
    (by unfold LogRoom; rw [fcfg, flogs]; exact hroom) (by unfold LogFits; rw [fcfg, flogs]; exact hfit)
    (by rw [fext]; exact hov) hin (by simp only; rw [hread]; exact hutf) hu hmb hpp
  simp only [hread] at hinv her
  refine ⟨host', ?_, ?_, Nat.le_of_eq hused, hmb', hpp'⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  · rw [her]
    show { erase host with logs := host.logs ++ [bs] } = { erase h with logs := h.logs ++ [bs] }
    rw [he, flogs]

end NearLogic
