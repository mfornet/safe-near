import Programs.ProofSupport.StreamMemory

/-!
Adapted from Talos at 80644390de3ad4db3055445259a034413ae41577 (AGPL-3.0).
Only the shared byte ownership, call framing and stdio transfers needed by
compiled stream drivers are retained here.
-/

namespace Programs.ProofSupport.StreamHost
open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

def stdioLens : HostLens Universal.State StdIO.State :=
  { get := Universal.State.stdio
    set := fun whole part => { whole with stdio := part } }

def readHost : HostFn Universal.State := StdIO.readHost.lift stdioLens
def writeHost : HostFn Universal.State := StdIO.writeHost.lift stdioLens

theorem readHost_eq : readHost = StdIO.readHost.lift stdioLens := rfl
theorem writeHost_eq : writeHost = StdIO.writeHost.lift stdioLens := rfl

theorem readHost_invoke_of_bound
    (store : Store Universal.State) (length pointer : UInt32)
    (hbound : pointer.toNat +
      (store.host.stdio.input.take length.toNat).length ≤
        store.mem.pages * 65536) :
    readHost.invoke store [.i32 length, .i32 pointer] =
      .Return [.i32 (UInt32.ofNat
        (store.host.stdio.input.take length.toNat).length)]
        { store with
          mem := store.mem.writeBytes pointer.toNat
            (store.host.stdio.input.take length.toNat)
          host := { store.host with
            stdio :=
              { input := store.host.stdio.input.drop
                  (store.host.stdio.input.take length.toNat).length
                output := store.host.stdio.output } } } := by
  rw [readHost_eq]
  simp only [HostFn.lift, StdIO.readHost, StdIO.readResult, Store.focus,
    Store.mapHost, stdioLens]
  rw [ite_eq_left]
  · rfl
  · exact decide_eq_true hbound

theorem writeHost_invoke_of_bound
    (store : Store Universal.State) (length pointer : UInt32)
    (hbound : pointer.toNat + length.toNat ≤
      store.mem.pages * 65536) :
    writeHost.invoke store [.i32 length, .i32 pointer] =
      .Return []
        { store with
          host := { store.host with
            stdio :=
              { input := store.host.stdio.input
                output := store.host.stdio.output ++
                  store.mem.readBytes pointer.toNat length.toNat } } } := by
  rw [writeHost_eq]
  simp only [HostFn.lift, StdIO.writeHost, StdIO.writeResult, Store.focus,
    Store.mapHost, stdioLens]
  rw [ite_eq_left]
  · rfl
  · exact decide_eq_true hbound

def afterWrite (host : Universal.State) (bytes : List UInt8) :
    Universal.State :=
  { host with
    stdio :=
      { input := host.stdio.input
        output := host.stdio.output ++ bytes } }

theorem writeTransfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State) (pointer length : UInt32)
    (bytes : List UInt8)
    (hlength : length.toNat = bytes.length)
    (hpos : 0 < bytes.length)
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (store : MachineStore Universal.State) (ns : Nat)
    (obs : List StepKind) (nt : Nat)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : writeHost.invoke store.wasm [.i32 length, .i32 pointer] =
      .Return results postWasm) :
    (hostStateOwn host ∗ pointsToBytes 0 pointer bytes) ∗
      stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
    (⌜results = []⌝ ∗ hostStateOwn (afterWrite host bytes) ∗
      pointsToBytes 0 pointer bytes) ∗
      stateInterp (GF := WasmHeapGF Universal.State)
        { store with wasm := postWasm } ns obs nt := by
  iintro ⟨⟨Hhost, Hbytes⟩, Hstate⟩
  ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply_frame stateInterp_host_agree store ns obs nt host using [Hstate Hhost]
  ihave %hfacts :
      ⌜∀ i b, bytes[i]? = some b →
        store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
        (pointer + UInt32.ofNat i).toNat <
          store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
  · imod stateInterp_pointsToBytes_agree store ns obs nt pointer bytes $$
        [$Hstate $Hbytes] with %hfacts
    ipureexact hfacts
  have hbound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [hlength]; exact pointsToBytes_facts_bound hfacts hpos hnowrap
  have hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes := by
    rw [hlength]
    apply pointsToBytes_facts_readBytes
    · intro i b hb
      exact (hfacts i b hb).1
    · exact hnowrap
  have hconcrete := writeHost_invoke_of_bound store.wasm length pointer hbound
  rw [hconcrete] at hinvoke
  have hresults := HostResult.Return.inj hinvoke
  have hresultValues : results = [] := hresults.1.symm
  have hpost : postWasm =
      { store.wasm with
        host := { store.wasm.host with
          stdio :=
            { input := store.wasm.host.stdio.input
              output := store.wasm.host.stdio.output ++ bytes } } } := by
    rw [← hresults.2]
    simp only [hread]
  subst results
  subst postWasm
  ihave HhostActual : hostStateOwn store.wasm.host $$ [Hhost]
  · irw_exact [hhostEq] with Hhost
  imod stateInterp_host_set store ns obs nt (afterWrite host bytes) $$
      [$Hstate $HhostActual] with ⟨Hstate, Hhost⟩
  imodintro
  isplitl [Hhost Hbytes]
  · isplitl_pureexact rfl
    · isplitl_exact Hhost
      · iexact Hbytes
  · isimp only [afterWrite] at Hstate
    irw_exact [hhostEq] with Hstate

def afterRead (host : Universal.State) (count : Nat) : Universal.State :=
  { host with
    stdio :=
      { input := host.stdio.input.drop count
        output := host.stdio.output } }

theorem readTransfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State) (pointer length : UInt32)
    (buffer : List UInt8)
    (hlength : buffer.length = length.toNat)
    (hpos : 0 < buffer.length)
    (hnowrap : pointer.toNat + buffer.length < UInt32.size)
    (store : MachineStore Universal.State) (ns : Nat)
    (obs : List StepKind) (nt : Nat)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : readHost.invoke store.wasm [.i32 length, .i32 pointer] =
      .Return results postWasm) :
    (hostStateOwn host ∗ pointsToBytes 0 pointer buffer) ∗
      stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
    (⌜results = [.i32 (UInt32.ofNat
        (host.stdio.input.take length.toNat).length)]⌝ ∗
      hostStateOwn
        (afterRead host (host.stdio.input.take length.toNat).length) ∗
      pointsToBytes 0 pointer
        (host.stdio.input.take length.toNat ++
          buffer.drop (host.stdio.input.take length.toNat).length)) ∗
      stateInterp (GF := WasmHeapGF Universal.State)
        { store with wasm := postWasm } ns obs nt := by
  let incoming := host.stdio.input.take length.toNat
  iintro ⟨⟨Hhost, Hbuffer⟩, Hstate⟩
  ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply_frame stateInterp_host_agree store ns obs nt host using [Hstate Hhost]
  ihave %hfacts :
      ⌜∀ i b, buffer[i]? = some b →
        store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
        (pointer + UInt32.ofNat i).toNat <
          store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbuffer]
  · imod stateInterp_pointsToBytes_agree store ns obs nt pointer buffer $$
        [$Hstate $Hbuffer] with %hfacts
    ipureexact hfacts
  have hbufferBound : pointer.toNat + buffer.length ≤
      store.wasm.mem.pages * 65536 :=
    pointsToBytes_facts_bound hfacts hpos hnowrap
  have hincomingLength : incoming.length ≤ buffer.length := by
    dsimp only [incoming]
    rw [hlength]; exact List.length_take_le _ _
  have hincomingBound : pointer.toNat + incoming.length ≤
      store.wasm.mem.pages * 65536 := by omega
  have hincomingNoWrap : pointer.toNat + incoming.length < UInt32.size := by omega
  have hphysicalIncoming :
      store.wasm.host.stdio.input.take length.toNat = incoming := by
    rw [hhostEq]
  have hconcrete := readHost_invoke_of_bound store.wasm length pointer (by
    rw [hphysicalIncoming]; exact hincomingBound)
  rw [hconcrete] at hinvoke
  have hresults := HostResult.Return.inj hinvoke
  have hresultValues : results =
      [.i32 (UInt32.ofNat incoming.length)] := by
    rw [← hresults.1]
    rw [hphysicalIncoming]
  have hpost : postWasm =
      { store.wasm with
        mem := store.wasm.mem.writeBytes pointer.toNat incoming
        host := { store.wasm.host with
          stdio :=
            { input := store.wasm.host.stdio.input.drop incoming.length
              output := store.wasm.host.stdio.output } } } := by
    rw [← hresults.2]
    simp only [hphysicalIncoming]
  subst results
  subst postWasm
  have hprefixLength : (buffer.take incoming.length).length = incoming.length := by
    rw [List.length_take_of_le hincomingLength]
  ihave Hparts :
      pointsToBytes 0 pointer (buffer.take incoming.length) ∗
      pointsToBytes 0
        (pointer + UInt32.ofNat (buffer.take incoming.length).length)
        (buffer.drop incoming.length) $$ [Hbuffer]
  · iapply (pointsToBytes_append 0 pointer
      (buffer.take incoming.length) (buffer.drop incoming.length)).mp
    irw_exact [List.take_append_drop] with Hbuffer
  icases Hparts with ⟨Hprefix, Hsuffix⟩
  isimp only [hprefixLength] at Hsuffix
  imod stateInterp_write_bytes store ns obs nt pointer
      (buffer.take incoming.length) incoming hprefixLength
      hincomingBound hincomingNoWrap $$ [$Hstate $Hprefix] with
      ⟨Hstate, Hprefix⟩
  let memoryStore : MachineStore Universal.State :=
    { store with wasm :=
        { store.wasm with mem :=
            store.wasm.mem.writeBytes pointer.toNat incoming } }
  have hmemoryHost : memoryStore.wasm.host = host := by
    dsimp only [memoryStore]; exact hhostEq
  ihave HhostActual : hostStateOwn memoryStore.wasm.host $$ [Hhost]
  · irw_exact [hmemoryHost] with Hhost
  imod stateInterp_host_set memoryStore ns obs nt
      (afterRead host incoming.length) $$ [$Hstate $HhostActual] with
      ⟨Hstate, Hhost⟩
  ihave Hbuffer :
      pointsToBytes 0 pointer
        (incoming ++ buffer.drop incoming.length) $$ [Hprefix Hsuffix]
  · iapply (pointsToBytes_append 0 pointer incoming
      (buffer.drop incoming.length)).mpr
    isplitl_exact Hprefix
    · iexact Hsuffix
  imodintro
  isplitl [Hhost Hbuffer]
  · isplitl_pureexact rfl
    · isplitl_exact Hhost
      · iexact Hbuffer
  · isimp only [memoryStore, afterRead] at Hstate
    irw_exact [hhostEq] with Hstate


end Programs.ProofSupport.StreamHost
