-- Ported from Talos GcdStdio/HostProof.lean at 80644390de3ad4db3055445259a034413ae41577 (AGPL-3.0).
import Programs.GcdStdio.CallKernelProof
import Programs.ProofSupport.StreamHost

namespace Programs.GcdStdio.HostProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Programs.GcdStdio.Contracts
open scoped Wasm.SmallStep.Outcome

-- Unfold the definitionally equal generic/outcome Iris instances when matching WPs.
set_option backward.isDefEq.respectTransparency false

private abbrev readImport : ImportDecl :=
  { module := "stdio", name := "read", params := [.i32, .i32], results := [.i32] }
private abbrev writeImport : ImportDecl :=
  { module := "stdio", name := "write", params := [.i32, .i32], results := [] }

private theorem readImport_index : Programs.GcdStdio.module.imports[0] = readImport := by rfl
private theorem writeImport_index : Programs.GcdStdio.module.imports[1] = writeImport := by rfl

private theorem readHost_resolves :
    (Universal.envFor Programs.GcdStdio.module).funcs[0]? =
      some Programs.ProofSupport.StreamHost.readHost := by rfl
private theorem writeHost_resolves :
    (Universal.envFor Programs.GcdStdio.module).funcs[1]? =
      some Programs.ProofSupport.StreamHost.writeHost := by rfl

private theorem func7_index : Programs.GcdStdio.module.funcs[7]? = some Programs.GcdStdio.func7Def := by rfl
private theorem func8_index : Programs.GcdStdio.module.funcs[8]? = some Programs.GcdStdio.func8Def := by rfl

theorem import0_correct [WasmSmallStepGS hlc Universal.State] :
    Import0Spec (hlc := hlc) := by
  unfold Import0Spec readContractAt CallContract
    callExpr Programs.ProofSupport.StreamMemory.callExpr
  intro ptr requested buffer input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  dsimp only
  let count := min requested.toNat input.length
  let Cont : HeapIProp := iprop(
    RuntimeContext -∗
    Streams (input.drop count) output raised -∗
    ByteSlice ptr (input.take count ++ buffer.drop count) -∗
    ⌜count ≤ requested.toNat⌝ -∗
    ResumeWP [.i32 (UInt32.ofNat count)] callerLocals stack code arity
      remainder controls calls s E Φ)
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  isimp only [Streams, Programs.ProofSupport.StreamMemory.Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  isimp only [Programs.GcdStdio.Contracts.ByteSlice,
    Programs.ProofSupport.StreamMemory.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  let host : Universal.State :=
    { stdio := { input := input, output := output }
      random := random
      oom := { raised := raised } }
  simp only [List.cons_append, List.nil_append]
  iapply twp_callHost Programs.GcdStdio.module 0 readImport
      Programs.ProofSupport.StreamHost.readHost (by decide) readImport_index
      (Universal.envFor Programs.GcdStdio.module)
      readHost_resolves
      (iprop(hostStateOwn host ∗ pointsToBytes 0 ptr buffer ∗ Cont))
      (fun results => iprop(
        ⌜results = [.i32 (UInt32.ofNat
          (host.stdio.input.take requested.toNat).length)]⌝ ∗
        hostStateOwn (Programs.ProofSupport.StreamHost.afterRead host
          (host.stdio.input.take requested.toNat).length) ∗
        pointsToBytes 0 ptr
          (host.stdio.input.take requested.toNat ++
            buffer.drop (host.stdio.input.take requested.toNat).length) ∗
        Cont))
      iprop(False) iprop(False) ⟨0⟩
      (fun store ns obs nt hmodule results postWasm hinvoke => by
        have hinvoke' : Programs.ProofSupport.StreamHost.readHost.invoke
            store.wasm [.i32 requested, .i32 ptr] =
              .Return results postWasm := by
          simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
            List.take_succ_cons, List.take_zero, List.reverse_cons,
            List.reverse_nil, List.cons_append, List.nil_append] using hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, Hcont⟩⟩, Hstate⟩
        imod Programs.ProofSupport.StreamHost.readTransfer host ptr requested
            buffer hfacts.1.symm (by omega) hnowrap store ns obs nt
            results postWasm hinvoke' $$ [Hhost Hbytes Hstate] with
            ⟨Hresult, Hstate⟩
        · iframe
        icases Hresult with ⟨Hpure, Hhost, Hbytes⟩
        imodintro
        isplitl [Hpure Hhost Hbytes Hcont]
        · iframe
        · iexact Hstate)
      (fun store ns obs nt _hmodule postWasm msg hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
        · iapply stateInterp_host_agree store ns obs nt host
          iframe Hstate Hhost
        ihave %hmem :
            ⌜∀ i b, buffer[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr buffer
              $$ [$Hstate $Hbytes] with %hmem
          ipureintro
          exact hmem
        have hbufferBound : ptr.toNat + buffer.length ≤
            store.wasm.mem.pages * 65536 :=
          pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hincomingBound : ptr.toNat +
            (store.wasm.host.stdio.input.take requested.toNat).length ≤
              store.wasm.mem.pages * 65536 := by
          rw [hhostEq]
          change ptr.toNat + (input.take requested.toNat).length ≤ _
          have := List.length_take_le requested.toNat input
          omega
        have hreturn :=
          Programs.ProofSupport.StreamHost.readHost_invoke_of_bound
            store.wasm requested ptr hincomingBound
        rw [hreturn] at hinvoke
        contradiction)
      (fun store ns obs nt _hmodule postWasm tag xs hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
        · iapply stateInterp_host_agree store ns obs nt host
          iframe Hstate Hhost
        ihave %hmem :
            ⌜∀ i b, buffer[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr buffer
              $$ [$Hstate $Hbytes] with %hmem
          ipureintro
          exact hmem
        have hbufferBound : ptr.toNat + buffer.length ≤
            store.wasm.mem.pages * 65536 :=
          pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hincomingBound : ptr.toNat +
            (store.wasm.host.stdio.input.take requested.toNat).length ≤
              store.wasm.mem.pages * 65536 := by
          rw [hhostEq]
          change ptr.toNat + (input.take requested.toNat).length ≤ _
          have := List.length_take_le requested.toNat input
          omega
        have hreturn :=
          Programs.ProofSupport.StreamHost.readHost_invoke_of_bound
            store.wasm requested ptr hincomingBound
        rw [hreturn] at hinvoke
        contradiction)
      (params := callerLocals.params) (localValues := callerLocals.locals)
      (values := .i32 ptr :: .i32 requested :: stack)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls)
      $$ [$Hhost $Hbytes $Hcont] Hmodule Henv
  · iintro %preWasm %results %postWasm %hinvoke Hresult
    icases Hresult with ⟨⟨%hresults, Hhost, Hbytes, Hcont⟩, Hmodule⟩
    have hcount :
        (host.stdio.input.take requested.toNat).length = count := by
      simp [host, count]
    subst results
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero]
    rw [hcount]
    have htake : input.take requested.toNat = input.take count := by
      simp [count]
    have hnewLength :
        (input.take count ++ buffer.drop count).length = buffer.length := by
      simp [count, hfacts.1]
    ihave Hstreams : Streams (input.drop count) output raised $$ [Hhost]
    · unfold Streams Programs.ProofSupport.StreamMemory.Streams
      iexists random
      isimp only [Programs.ProofSupport.StreamHost.afterRead, host, hcount]
        at Hhost
      iexact Hhost
    ihave Hslice : Programs.GcdStdio.Contracts.ByteSlice ptr
        (input.take count ++ buffer.drop count) $$ [Hbytes]
    · unfold Programs.GcdStdio.Contracts.ByteSlice
        Programs.ProofSupport.StreamMemory.ByteSlice
      isplitl []
      · ipureintro
        rw [hnewLength]
        exact hnowrap
      · rw [← htake, ← hcount]
        isimp only [host] at Hbytes
        iexact Hbytes
    isimp only [Cont, RuntimeContext, ResumeWP, resumeExpr,
      Programs.ProofSupport.StreamMemory.resumeExpr, List.nil_append]
      at Hcont
    iapply Hcont $$ [Hmodule Henv] Hstreams Hslice
    · isplitl [Hmodule]
      · iexact Hmodule
      · iexact Henv
    · ipureintro
      exact Nat.min_le_left _ _
  · iintro %preWasm %postWasm %msg %hinvoke Hfalse
    iexfalso
    iexact Hfalse
  · iintro %preWasm %postWasm %tag %xs %hinvoke Hfalse
    iexfalso
    iexact Hfalse

/-- The authoritative `stdio.write` import contract. -/
theorem import1_correct [WasmSmallStepGS hlc Universal.State] :
    Import1Spec (hlc := hlc) := by
  unfold Import1Spec writeContractAt CallContract
    callExpr Programs.ProofSupport.StreamMemory.callExpr
  intro ptr requested bytes input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  let Cont : HeapIProp := iprop(
    RuntimeContext -∗
    Streams input (output ++ bytes) raised -∗
    ByteSlice ptr bytes -∗
    ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  isimp only [Streams, Programs.ProofSupport.StreamMemory.Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  isimp only [Programs.GcdStdio.Contracts.ByteSlice,
    Programs.ProofSupport.StreamMemory.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  let host : Universal.State :=
    { stdio := { input := input, output := output }
      random := random
      oom := { raised := raised } }
  simp only [List.cons_append, List.nil_append]
  iapply twp_callHost Programs.GcdStdio.module 1 writeImport
      Programs.ProofSupport.StreamHost.writeHost (by decide) writeImport_index
      (Universal.envFor Programs.GcdStdio.module)
      writeHost_resolves
      (iprop(hostStateOwn host ∗ pointsToBytes 0 ptr bytes ∗ Cont))
      (fun results => iprop(
        ⌜results = []⌝ ∗
        hostStateOwn (Programs.ProofSupport.StreamHost.afterWrite host bytes) ∗
        pointsToBytes 0 ptr bytes ∗ Cont))
      iprop(False) iprop(False) ⟨0⟩
      (fun store ns obs nt hmodule results postWasm hinvoke => by
        have hinvoke' : Programs.ProofSupport.StreamHost.writeHost.invoke
            store.wasm [.i32 requested, .i32 ptr] =
              .Return results postWasm := by
          simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
            List.take_succ_cons, List.take_zero, List.reverse_cons,
            List.reverse_nil, List.cons_append, List.nil_append] using hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, Hcont⟩⟩, Hstate⟩
        imod Programs.ProofSupport.StreamHost.writeTransfer host ptr requested
            bytes hfacts.1 (by omega) hnowrap store ns obs nt results
            postWasm hinvoke' $$ [Hhost Hbytes Hstate] with
            ⟨Hresult, Hstate⟩
        · iframe
        icases Hresult with ⟨Hpure, Hhost, Hbytes⟩
        imodintro
        isplitl [Hpure Hhost Hbytes Hcont]
        · iframe
        · iexact Hstate)
      (fun store ns obs nt _hmodule postWasm msg hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨_Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hmem :
            ⌜∀ i b, bytes[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr bytes
              $$ [$Hstate $Hbytes] with %hmem
          ipureintro
          exact hmem
        have hbound : ptr.toNat + requested.toNat ≤
            store.wasm.mem.pages * 65536 := by
          rw [hfacts.1]
          exact pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hreturn :=
          Programs.ProofSupport.StreamHost.writeHost_invoke_of_bound
            store.wasm requested ptr hbound
        rw [hreturn] at hinvoke
        contradiction)
      (fun store ns obs nt _hmodule postWasm tag xs hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨_Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hmem :
            ⌜∀ i b, bytes[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr bytes
              $$ [$Hstate $Hbytes] with %hmem
          ipureintro
          exact hmem
        have hbound : ptr.toNat + requested.toNat ≤
            store.wasm.mem.pages * 65536 := by
          rw [hfacts.1]
          exact pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hreturn :=
          Programs.ProofSupport.StreamHost.writeHost_invoke_of_bound
            store.wasm requested ptr hbound
        rw [hreturn] at hinvoke
        contradiction)
      (params := callerLocals.params) (localValues := callerLocals.locals)
      (values := .i32 ptr :: .i32 requested :: stack)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls)
      $$ [$Hhost $Hbytes $Hcont] Hmodule Henv
  · iintro %preWasm %results %postWasm %hinvoke Hresult
    icases Hresult with ⟨⟨%hresults, Hhost, Hbytes, Hcont⟩, Hmodule⟩
    subst results
    simp only [List.length_nil, List.take_zero, List.length_cons,
      Nat.reduceAdd, List.drop_succ_cons, List.drop_zero,
      List.nil_append]
    ihave Hstreams : Streams input (output ++ bytes) raised $$ [Hhost]
    · unfold Streams Programs.ProofSupport.StreamMemory.Streams
      iexists random
      isimp only [Programs.ProofSupport.StreamHost.afterWrite, host] at Hhost
      iexact Hhost
    ihave Hslice : Programs.GcdStdio.Contracts.ByteSlice ptr bytes $$ [Hbytes]
    · unfold Programs.GcdStdio.Contracts.ByteSlice
        Programs.ProofSupport.StreamMemory.ByteSlice
      isplitl []
      · ipureintro
        exact hnowrap
      · iexact Hbytes
    isimp only [Cont, RuntimeContext, ResumeWP, resumeExpr,
      Programs.ProofSupport.StreamMemory.resumeExpr, List.nil_append]
      at Hcont
    iapply Hcont $$ [Hmodule Henv] Hstreams Hslice
    · isplitl [Hmodule]
      · iexact Hmodule
      · iexact Henv
  · iintro %preWasm %postWasm %msg %hinvoke Hfalse
    iexfalso
    iexact Hfalse
  · iintro %preWasm %postWasm %tag %xs %hinvoke Hfalse
    iexfalso
    iexact Hfalse

/-- The generated read shim delegates to the authoritative import-0 contract. -/
theorem func7_correct [WasmSmallStepGS hlc Universal.State] :
    Func7Spec (hlc := hlc) := by
  unfold Func7Spec readContractAt CallContract
    callExpr
  intro ptr requested buffer input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  dsimp only
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  simp only [Programs.ProofSupport.StreamMemory.callExpr]
  iapply Wasm.SmallStep.twp_call Programs.GcdStdio.module 10
      Programs.GcdStdio.func7Def (by decide)
      func7_index $$ Hmodule
  iintro Hmodule
  simp [Programs.GcdStdio.func7Def, Programs.GcdStdio.func7,
    Function.toLocals, Function.numParams]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  let shimLocals : Locals := ⟨[.i32 ptr, .i32 requested], [], []⟩
  let callerFrame : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := ⟨0⟩ }
  have Hread := import0_correct (hlc := hlc)
      (ptr := ptr) (requested := requested) (buffer := buffer)
      (input := input) (output := output) (raised := raised)
      (callerLocals := shimLocals) (stack := []) (code := [])
      (arity := 1) (remainder := []) (controls := [])
      (calls := callerFrame :: calls) (s := s) (E := E) (Phi := Φ)
  unfold Import0Spec CallContract callExpr Programs.ProofSupport.StreamMemory.callExpr at Hread
  simp only [List.cons_append, List.nil_append] at Hread
  iapply Hread
  isplitl [Hmodule]
  · unfold RuntimeContext
    isplitl [Hmodule]
    · iexact Hmodule
    · iexact Henv
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hslice]
  · iexact Hslice
  isplitl []
  · ipureintro
    exact hfacts
  iintro Hruntime Hstreams Hslice %hcount
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, HenvInner⟩
  unfold ResumeWP resumeExpr Programs.ProofSupport.StreamMemory.resumeExpr
  iapply Wasm.SmallStep.twp_returnFromCallFallthrough $$ Hmodule
  iintro Hmodule
  simp only [List.append_nil, List.take_succ_cons, List.take_zero,
    List.cons_append, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr,
    Programs.ProofSupport.StreamMemory.resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule HenvInner] Hstreams Hslice
  · iframe
  · itrivial

/-- The generated write shim changes only the machine-stack operand order and
delegates to the authoritative import-1 contract. -/
theorem func8_correct [WasmSmallStepGS hlc Universal.State] :
    Func8Spec (hlc := hlc) := by
  unfold Func8Spec writeContractAt CallContract
    callExpr
  intro ptr requested bytes input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  simp only [Programs.ProofSupport.StreamMemory.callExpr]
  iapply Wasm.SmallStep.twp_call Programs.GcdStdio.module 11
      Programs.GcdStdio.func8Def (by decide)
      func8_index $$ Hmodule
  iintro Hmodule
  simp [Programs.GcdStdio.func8Def, Programs.GcdStdio.func8,
    Function.toLocals, Function.numParams]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  let shimLocals : Locals := ⟨[.i32 ptr, .i32 requested], [], []⟩
  let callerFrame : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := ⟨0⟩ }
  have Hwrite := import1_correct (hlc := hlc)
      (ptr := ptr) (requested := requested) (bytes := bytes)
      (input := input) (output := output) (raised := raised)
      (callerLocals := shimLocals) (stack := []) (code := [])
      (arity := 0) (remainder := []) (controls := [])
      (calls := callerFrame :: calls) (s := s) (E := E) (Phi := Φ)
  unfold Import1Spec CallContract callExpr Programs.ProofSupport.StreamMemory.callExpr at Hwrite
  simp only [List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl [Hmodule]
  · unfold RuntimeContext
    isplitl [Hmodule]
    · iexact Hmodule
    · iexact Henv
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hslice]
  · iexact Hslice
  isplitl []
  · ipureintro
    exact hfacts
  iintro Hruntime Hstreams Hslice
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, HenvInner⟩
  unfold ResumeWP resumeExpr Programs.ProofSupport.StreamMemory.resumeExpr
  iapply Wasm.SmallStep.twp_returnFromCallFallthrough $$ Hmodule
  iintro Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr,
    Programs.ProofSupport.StreamMemory.resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule HenvInner] Hstreams Hslice
  · iframe

end Programs.GcdStdio.HostProof
