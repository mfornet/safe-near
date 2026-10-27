import Skeleton.Memory
import NearVM.MeteredHosts.Output

/-!
# Decoding the walking module's fixed log message

This connects the symbolic initialized memory to the actual UTF-8 reader.
The hypotheses state exactly the log space and checked-cost room required by
the host, before any metered call contract is used.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near

/-- The actual fixed-length UTF-8 reader reads `saved` at address one. -/
theorem read_saved (st : HostStore NearState) (pages : Nat) (max : Option Nat)
    (hpages : 0 < pages) (hmemory : st.mem = dataMemory pages max)
    (hspace : 5 ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64) :
    (readUtf8String st 5 1).result = .ok "saved".toUTF8.toList := by
  have hbytes : st.mem.readList 1 5 = "saved".toUTF8.toList := by
    rw [hmemory]
    exact dataMemory_saved pages max hpages
  have hsize : 6 ≤ memorySize st := by
    change 6 ≤ st.mem.byteSize
    rw [hmemory, (dataMemory_spec pages max hpages).2.1]
    unfold pageSize
    omega
  have hutf : validUtf8 "saved".toUTF8.toList = true := by decide +kernel
  exact readUtf8String_fixed_ok st 5 1 "saved".toUTF8.toList (by decide)
    hspace hcost hsize hbytes hutf

/-- Log count, cumulative byte room and cost room suffice for appending the
fixed message. This is a decoder fact, not a hypothesis about a VM run. -/
theorem log_saved (st : HostStore NearState) (pages : Nat) (max : Option Nat)
    (hpages : 0 < pages) (hmemory : st.mem = dataMemory pages max)
    (hcount : logCountError st = none)
    (hspace : 5 ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, st.host.config.maxLogLen = some limit → totalLogLength st + 5 ≤ limit) :
    logUtf8Fn.invoke st [.i64 5, .i64 1] =
      .Return [] { st with host := { st.host with logs := st.host.logs ++ ["saved".toUTF8.toList] } } := by
  apply MeteredHosts.Output.logUtf8_of_read st 5 1 "saved".toUTF8.toList hcount
    (read_saved st pages max hpages hmemory hspace hcost)
  intro limit hlimit
  have hlength : "saved".toUTF8.toList.length = 5 := by decide +kernel
  rw [hlength]
  exact hpush limit hlimit

/-- The complete ordered plan for logging the fixed five-byte message. -/
def savedReadCharges : List (String × Nat) :=
  [ext1 "base", ext1 "utf8_decoding_base", ext1 "read_memory_base",
    ext1 "read_memory_byte" 5, ext1 "utf8_decoding_byte" 5,
    ext1 "log_base", ext1 "log_byte" 5]

/-- Concrete bytes determine the exact reader result and its entire cost plan. -/
theorem log_saved_spec (st : HostStore NearState) (pages : Nat) (max : Option Nat)
    (hpages : 0 < pages) (hmemory : st.mem = dataMemory pages max)
    (hcount : logCountError st = none) (hspace : 5 ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, st.host.config.maxLogLen = some limit → totalLogLength st + 5 ≤ limit) :
    logUtf8Read st 5 1 = ⟨savedReadCharges, .ok "saved".toUTF8.toList⟩ := by
  have hbytes : st.mem.readList 1 5 = "saved".toUTF8.toList := by
    rw [hmemory]; exact dataMemory_saved pages max hpages
  have hsize : 6 ≤ memorySize st := by
    change 6 ≤ st.mem.byteSize
    rw [hmemory, (dataMemory_spec pages max hpages).2.1]
    unfold pageSize
    omega
  have hr := readUtf8String_fixed st 5 1 "saved".toUTF8.toList (by decide)
    hspace hcost hsize hbytes (by decide +kernel)
  have hlength : "saved".toUTF8.toList.length = 5 := by decide +kernel
  simp only [logUtf8Read, hcount, hr, finishLog, hlength]
  cases hlimit : st.host.config.maxLogLen with
  | none => rfl
  | some limit =>
    simp only [Nat.not_lt_of_ge (hpush limit hlimit), ↓reduceIte]
    rfl

/-- The actual metered host charges this fixed list, independent of trie,
input length, and the gas budget. -/
def savedCharges : List Charge := extCharges savedReadCharges

theorem saved_charges (st : HostStore NearState) (pages : Nat) (max : Option Nat)
    (hpages : 0 < pages) (hmemory : st.mem = dataMemory pages max)
    (hcount : logCountError st = none) (hspace : 5 ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, st.host.config.maxLogLen = some limit → totalLogLength st + 5 ≤ limit) :
    chargesBefore "log_utf8" st [.i64 5, .i64 1] = savedCharges := by
  rw [MeteredHosts.Output.chargesBefore_logUtf8,
    log_saved_spec st pages max hpages hmemory hcount hspace hcost hpush]
  rfl

private theorem saved_burnsOnly : ∀ charge ∈ savedCharges, MeteredHosts.BurnsOnly charge := by
  simp only [savedCharges, extCharges, List.mem_map]
  rintro _ ⟨_, _, rfl⟩
  trivial

/-- The store after the actual billing, used-gas synchronization and log append. -/
def savedAfter (st : HostStore NearState) : HostStore NearState :=
  let paid := MeteredHosts.Output.paidStore st (applyCharges st.host savedCharges).1
  { paid with host := { paid.host with logs := paid.host.logs ++ ["saved".toUTF8.toList] } }

/-- All premises refer to the original store. The fixed log contract includes
its actual gas payment and retains an arbitrary caller-owned credit frame. -/
theorem metered_saved (extra : Nat) (st : HostStore NearState)
    (pages : Nat) (max : Option Nat) (rest : Nat)
    (hpages : 0 < pages) (hmemory : st.mem = dataMemory pages max)
    (hcount : logCountError st = none) (hspace : 5 ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, st.host.config.maxLogLen = some limit → totalLogLength st + 5 ≤ limit)
    (hcredits : st.host.gas.Credits (MeteredHosts.burnSum st.host.extCosts savedCharges + rest)) :
    (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 5, .i64 1] = .Return [] (savedAfter st) ∧
      (savedAfter st).host.gas.burnt = st.host.gas.burnt +
        MeteredHosts.burnSum st.host.extCosts savedCharges ∧
      (savedAfter st).host.gas.promises = st.host.gas.promises ∧
      (savedAfter st).host.gas.Credits rest := by
  let paid := (applyCharges st.host savedCharges).1
  let after := MeteredHosts.Output.paidStore st paid
  have hframe := MeteredHosts.applyCharges_frame st.host savedCharges saved_burnsOnly
  have hcfg := congrArg NearState.config hframe
  change paid.config = st.host.config at hcfg
  have hlogs := congrArg NearState.logs hframe
  change paid.logs = st.host.logs at hlogs
  have hext := congrArg NearState.extCosts hframe
  change paid.extCosts = st.host.extCosts at hext
  have hc := MeteredHosts.applyCharges_credits st.host savedCharges rest saved_burnsOnly hcredits
  have hread : (logUtf8Read after 5 1).result = .ok "saved".toUTF8.toList := by
    have hs := log_saved_spec after pages max hpages hmemory
      (by simpa only [logCountError, after, MeteredHosts.Output.paidStore, hcfg, hlogs] using hcount)
      (by simpa only [logSpace, totalLogLength, after, MeteredHosts.Output.paidStore,
        hcfg, hlogs] using hspace)
      (by simpa only [after, MeteredHosts.Output.paidStore, hext] using hcost)
      (by simpa only [totalLogLength, after, MeteredHosts.Output.paidStore, hcfg, hlogs] using hpush)
    exact congrArg StringRead.result hs
  have hcharge : applyCharges st.host (chargesBefore "log_utf8" st [.i64 5, .i64 1]) = (paid, none) := by
    rw [saved_charges st pages max hpages hmemory hcount hspace hcost hpush]
    exact Prod.ext rfl hc.1
  exact ⟨MeteredHosts.Output.metered_logUtf8_ok extra st 5 1 paid _ hcharge hread,
    hc.2.1, hc.2.2.1, hc.2.2.2.2⟩

@[simp] theorem savedAfter_memory (st : HostStore NearState) : (savedAfter st).mem = st.mem := rfl

end WNear.Skeleton
