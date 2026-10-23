import WasmLogic.Rules.Control

/-!
# Rules for calls

`wpInvoke` is the weakest precondition of a Wasm function from the moment
its frame is pushed: for any operands and frames below it, and any
continuation that knows what to do with its results, the thread satisfies
`WP`. Iris-Wasm's `wp_invoke_native` corresponds to `wpInvoke_intro`, which
turns a proof about the body into one about the function; `wpi_call` and
`wpi_call_indirect` call such a function from a fragment.

Calls are bounded by `ExecLimits.maxCallDepth`, which Iris-Wasm's semantics
does not have: a call at depth `d` needs `d + 1 < maxCallDepth`, or it traps
(`wpi_call_exhausted`).

Host functions are described by contracts (`wpi_call_host`): the host state
and the caller's whole memory are owned, and the rule holds for any host
function whose result on memories with those cells is known.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic

/-- What a function returns, or that it trapped. -/
structure FunPost (GF : BundledGFunctors) where
  ret : List Value → IProp GF
  trap : IProp GF := iprop(False)

/-- The locals a Wasm function starts with. -/
def entryLocals (code : Func) (args : List Value) : Array Value :=
  args.toArray ++ (code.locals.map ValType.default).toArray

/-- The thread just after a Wasm function's frame is pushed: the caller's
operands `bs` below, frames `fs` below. -/
def calleeThread (bs : List Value) (fs : List CallFrame) (type : FuncType) (inst : Nat)
    (code : Func) (args : List Value) : Thread :=
  { stack := bs.toArray,
    frames := { locals := entryLocals code args, inst := inst, arity := type.results.length,
                height := bs.length, labels := [], code := code.body } :: fs }

/-- What the machine does once a function returns `rs`. -/
def retCode (H : Type) (lim : ExecLimits) (bs rs : List Value) : List CallFrame → Code H
  | [] => .finished (.values rs)
  | f :: fs => .running lim { stack := (bs ++ rs).toArray, frames := f :: fs }

section Defs

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]

/-- The weakest precondition of a Wasm function with `args`, called at depth
`d`, from the moment its frame is pushed. -/
def wpInvoke (lim : ExecLimits) (d : Nat) (type : FuncType) (inst : Nat) (mi : ModuleInst)
    (code : Func) (args : List Value) (Φf : FunPost GF) : IProp GF :=
  iprop(∀ (Ψ : Outcome → IProp GF) (bs : List Value) (fs : List CallFrame), ⌜fs.length = d⌝ -∗
    instPt (H := H) inst mi -∗
    ((∀ rs, Φf.ret rs -∗ WP (retCode H lim bs rs fs) @ Stuckness.MaybeStuck; ⊤ {{ Ψ }}) ∧
      (Φf.trap -∗ ∀ r, Ψ (.trap r))) -∗
    wpT (H := H) lim (calleeThread bs fs type inst code args) Ψ)

/-- How a function body ending translates to the function returning: the
top `r` operands are its results. -/
def Post.func (r : Nat) (Φf : FunPost GF) : Post H GF where
  normal vs _ := iprop(⌜r ≤ vs.length⌝ ∗ Φf.ret (vs.drop (vs.length - r)))
  br _ vs _ := iprop(⌜r ≤ vs.length⌝ ∗ Φf.ret (vs.drop (vs.length - r)))
  ret vs _ := iprop(⌜r ≤ vs.length⌝ ∗ Φf.ret (vs.drop (vs.length - r)))
  trap := Φf.trap

end Defs

section Step

variable {H : Type}

theorem popN_snd (A X : List Value) (r : Nat) (hr : r ≤ X.length) :
    (Exec.popN (A ++ X).toArray r).2 = X.drop (X.length - r) := by
  simp only [Exec.popN, List.size_toArray, List.length_append]
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp [List.getElem_append_right (show A.length ≤ A.length + X.length - r + k by omega)]
    congr 1; omega

/-- The context of a function body: its operands `bs` and frames `fs` below. -/
def bodyCtx (bs : List Value) (fs : List CallFrame) (r : Nat) : Ctx :=
  { base := bs, labels := [], rest := [], arity := r, height := bs.length, below := fs }

theorem calleeThread_eq (bs : List Value) (fs : List CallFrame) (type : FuncType) (inst : Nat)
    (mi : ModuleInst) (code : Func) (args : List Value) :
    calleeThread bs fs type inst code args =
      (bodyCtx bs fs type.results.length).thread ⟨entryLocals code args, inst, mi⟩ []
        (bodyCtx bs fs type.results.length).labels (code.body ++ (bodyCtx bs fs type.results.length).rest) := by
  simp [calleeThread, bodyCtx, Ctx.thread, Ctx.threadA]

@[simp] theorem bodyCtx_labels (bs : List Value) (fs : List CallFrame) (r : Nat) :
    (bodyCtx bs fs r).labels = [] := rfl
@[simp] theorem bodyCtx_rest (bs : List Value) (fs : List CallFrame) (r : Nat) :
    (bodyCtx bs fs r).rest = [] := rfl

/-- Leaving a function: its top `r` operands are its results. -/
theorem next_leave (σ : Store H) (lim : ExecLimits) (bs : List Value) (fs : List CallFrame)
    (r : Nat) (g : Frame) (vs : List Value) (hr : r ≤ vs.length) (code : List Instr)
    (hcode : code = [] ∨ (∃ n, code = [.br n]) ∨ code = [.return]) :
    next σ lim ((bodyCtx bs fs r).thread g vs [] code) =
      (retCode H lim bs (vs.drop (vs.length - r)) fs, σ) := by
  have hs := branch_stack bs vs r hr
  have hv := popN_snd bs vs r hr
  have hs1 : List.take bs.length (Exec.popN (bs ++ vs).toArray r).fst.toList = bs := by
    have := congrArg Array.toList hs
    simpa [hv] using this
  rcases hcode with rfl | ⟨n, rfl⟩ | rfl <;>
  · cases fs <;>
      simp [next, Code.config, Exec.step, Exec.instr, Exec.branch, Exec.leave, bodyCtx, Ctx.thread,
        Ctx.threadA, retCode, hv, hs1]

/-- The caller's frame while a callee runs. -/
def callerFrame (C : Ctx) (f : Frame) : CallFrame :=
  { locals := f.locals, inst := f.inst, arity := C.arity, height := C.height, labels := C.labels,
    code := C.rest }

theorem retCode_caller (lim : ExecLimits) (C : Ctx) (f : Frame) (vs₀ rs : List Value) :
    retCode H lim (C.base ++ vs₀) rs (callerFrame C f :: C.below) =
      .running lim (C.thread f (vs₀ ++ rs) C.labels C.rest) := by
  simp [retCode, Ctx.thread, Ctx.threadA, callerFrame]

theorem popN_args (A args : List Value) :
    Exec.popN (A ++ args).toArray args.length = (A.toArray, args) := by
  have h1 := popN_snd A args args.length (Nat.le_refl _)
  simp only [Nat.sub_self, List.drop_zero] at h1
  simp only [Exec.popN, Prod.mk.injEq] at h1 ⊢
  refine ⟨?_, h1⟩
  apply Array.toList_inj.mp
  simp

/-- A call to a Wasm function pushes its frame. -/
theorem next_call_wasm (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs₀ args : List Value) (t : Thread) (a : Nat) (type : FuncType) (inst : Nat) (code : Func)
    (hfn : σ.funcs[a]? = some (.wasm type inst code)) (hlen : args.length = type.params.length)
    (hd : C.below.length + 1 < lim.maxCallDepth) :
    Exec.enter { store := σ, thread := t, limits := lim }
        (C.base ++ (vs₀ ++ args)).toArray (callerFrame C f :: C.below) a =
      .next { store := σ,
              thread := calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args,
              limits := lim } := by
  have hp := popN_args (C.base ++ vs₀) args
  rw [hlen] at hp
  simp only [List.append_assoc] at hp
  simp [Exec.enter, hfn, show ¬(lim.maxCallDepth ≤ C.below.length + 1) by omega, hp, calleeThread,
    entryLocals]

/-- A step of an instruction that calls. -/
theorem next_instr_call (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs : List Value)
    (L : List Label) (i : Instr) (R : List Instr) (hmi : σ.modules[f.inst]? = some f.mi)
    {σ' : Store H} {stack : Array Value} {addr : Nat} {R' : List Instr}
    (h : Exec.instr σ f.mi f.locals (C.base ++ vs).toArray L i R = ⟨σ', .call stack addr R'⟩) :
    next σ lim (C.thread f vs L (i :: R)) =
      (match Exec.enter { store := σ', thread := C.thread f vs L (i :: R), limits := lim } stack
          ({ locals := f.locals, inst := f.inst, arity := C.arity, height := C.height, labels := L,
             code := R' } :: C.below) addr with
        | .next c => (.running lim c.thread, c.store)
        | .done vs s => (.finished (.values vs), s)
        | .trap r s => (.finished (.trap r), s)) := by
  simp only [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA, modules_get! hmi, h]
  rfl

end Step

section Rules

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post H GF}

/-- A step that only moves the thread, to any expression. -/
theorem wpC_step {t : Thread} {e' : Code H} {Ψ : Outcome → IProp GF} (Rd : List (Loc × Cell H))
    (h : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) → next σ lim t = (e', σ)) :
    seeList Rd ∗ ▷ WP e' @ Stuckness.MaybeStuck; ⊤ {{ Ψ }} ⊢ wpT (H := H) lim t Ψ := by
  iintro ⟨HRd, Hwp⟩
  iapply wp_lift lim t Rd [] [] e' List.nodup_nil List.nodup_nil
  · intro σ hRd _
    rw [h σ hRd]
    exact ⟨rfl, fun l => by simp⟩
  · intro σ _ _ l hl _
    simp at hl
  isplitl [HRd]
  · iexact HRd
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro _
    iexact Hwp

/-- Iris-Wasm's `wp_invoke_native`: a function is its body run in its entry
frame, ending by falling off, returning, or branching past every label. -/
theorem wpInvoke_intro (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (args : List Value) (Φf : FunPost GF) :
    wpi lim d ⟨entryLocals code args, inst, mi⟩ [] code.body
        (Post.func (H := H) type.results.length Φf)
      ⊢ wpInvoke lim d type inst mi code args Φf := by
  unfold wpInvoke
  iintro Hwp %Ψ %bs %fs %hfs #Hi HK
  rw [calleeThread_eq bs fs type inst mi]
  unfold wpi
  iapply Hwp $$ %Ψ %(bodyCtx bs fs type.results.length) %hfs Hi
  unfold Kont Post.func
  simp only [bodyCtx_labels, bodyCtx_rest]
  isplit
  · iintro %vs %l ⟨%hr, HΦ⟩
    iapply wpC_step [] (fun σ _ => next_leave σ lim bs fs _ _ vs hr [] (.inl rfl))
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    icases HK with ⟨HK, -⟩
    iapply HK $$ HΦ
  isplit
  · iintro %n %vs %l ⟨%hr, HΦ⟩
    iapply wpC_step [] (fun σ _ => next_leave σ lim bs fs _ _ vs hr [.br n] (.inr (.inl ⟨n, rfl⟩)))
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    icases HK with ⟨HK, -⟩
    iapply HK $$ HΦ
  isplit
  · iintro %vs %l ⟨%hr, HΦ⟩
    iapply wpC_step [] (fun σ _ => next_leave σ lim bs fs _ _ vs hr [.return] (.inr (.inr rfl)))
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    icases HK with ⟨HK, -⟩
    iapply HK $$ HΦ
  · icases HK with ⟨-, HK⟩
    iexact HK

/-- Iris-Wasm's `wp_call`: call the module's function `i`, a Wasm function. -/
theorem wpi_call (i a : Nat) (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (vs₀ args : List Value) (ha : f.mi.funcAddrs[i]? = some a)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      ▷ wpInvoke lim (d + 1) type inst mi code args
          { ret := fun rs => Φ.normal (vs₀ ++ rs) f, trap := Φ.trap }
      ⊢ wpi lim d f (vs₀ ++ args) [.call i] Φ := by
  unfold wpi
  iintro ⟨#Hf, #Hi', Hwp⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wpT_step [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.wasm type inst code))]
    (t' := calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args)
  · intro σ hRd
    have hmi := hmi_of_see hRd
    have hfn : σ.funcs[a]? = some (.wasm type inst code) := by
      have := hRd _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    have he := next_call_wasm σ lim C f vs₀ args
      (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest)) a type inst code hfn hlen (by omega)
    simp only [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA]
    simp only [Exec.instr, modules_get! hmi, ha, Exec.Effect.call]
    simp only [Ctx.thread, Ctx.threadA, callerFrame] at he
    rw [he]
    rfl
  isplitr
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    iunfold funcPt at Hf
    isplitr
    · iexact Hi
    · iapply (seeList_cons _ _).2
      isplitr
      · iexact Hf
      · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  unfold wpInvoke
  iapply Hwp $$ %Ψ %(C.base ++ vs₀) %(callerFrame C f :: C.below) %(by simp; omega) Hi'
  unfold Kont
  isplit
  · iintro %rs HΦ
    rw [retCode_caller]
    icases HK with ⟨HK, -⟩
    ispecialize HK $$ %(vs₀ ++ rs) %f.locals
    simp only [Frame.withLocals_self]
    iapply HK $$ HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-- A call beyond the depth limit traps. -/
theorem wpi_call_exhausted (i a : Nat) (type : FuncType) (inst : Nat) (code : Func)
    (vs : List Value) (ha : f.mi.funcAddrs[i]? = some a) (hd : lim.maxCallDepth ≤ d + 1) :
    a ↪[wf] FuncInst.wasm type inst code ∗ ▷ Φ.trap ⊢ wpi lim d f vs [.call i] Φ := by
  unfold wpi
  iintro ⟨#Hf, HΦ⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wpC_step [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.wasm type inst code))]
    (e' := .finished (.trap .callStackExhausted))
  · intro σ hRd
    have hmi := hmi_of_see hRd
    have hfn : σ.funcs[a]? = some (.wasm type inst code) := by
      have := hRd _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    simp [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA, Exec.instr, modules_get! hmi, ha,
      Exec.enter, hfn, show lim.maxCallDepth ≤ C.below.length + 1 by omega]
  isplitr
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    iunfold funcPt at Hf
    isplitr
    · iexact Hi
    · iapply (seeList_cons _ _).2
      isplitr
      · iexact Hf
      · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iapply wp_finished
  unfold Kont
  icases HK with ⟨-, -, -, HK⟩
  ispecialize HK $$ HΦ
  ispecialize HK $$ %Trap.callStackExhausted
  iexact HK

/-- Iris-Wasm's `wp_call_indirect_success`: the table entry names a Wasm
function of the expected type. -/
theorem wpi_call_indirect (ty t ta : Nat) (idx : UInt32) (a : Nat) (type : FuncType) (inst : Nat)
    (mi : ModuleInst) (code : Func) (vs₀ args : List Value)
    (hta : f.mi.tableAddrs[t]? = some ta) (hty : type = f.mi.types[ty]!)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    ta ↦[wt][ idx.toNat ] Ref.func a ∗ a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      ▷ (ta ↦[wt][ idx.toNat ] Ref.func a -∗ wpInvoke lim (d + 1) type inst mi code args
          { ret := fun rs => Φ.normal (vs₀ ++ rs) f, trap := Φ.trap })
      ⊢ wpi lim d f (vs₀ ++ args ++ [.i32 idx]) [.call_indirect ty t] Φ := by
  unfold wpi
  iintro ⟨Ht, #Hf, #Hi', Hwp⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wp_lift lim _ [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.wasm type inst code))]
    [(Loc.tableElem ta idx.toNat, .ref (.func a))] [(Loc.tableElem ta idx.toNat, .ref (.func a))]
    (.running lim (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args))
    (by simp) (by simp)
  · intro σ hRd hP
    have hmi := hmi_of_see hRd
    have hfn : σ.funcs[a]? = some (.wasm type inst code) := by
      have := hRd _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    have htab := hP _ List.mem_cons_self
    simp only [lookup_tableElem, Option.bind_eq_some_iff, Option.map_eq_some_iff] at htab
    obtain ⟨table, htable, r, hr, hre⟩ := htab
    cases hre
    have hinstr : Exec.instr σ f.mi f.locals (C.base ++ (vs₀ ++ args ++ [Value.i32 idx])).toArray C.labels
        (.call_indirect ty t) C.rest = ⟨σ, .call (C.base ++ (vs₀ ++ args)).toArray a C.rest⟩ := by
      simp [Exec.instr, Exec.tableOf, hta, htable, Exec.i32, hr, hfn, ← hty, FuncInst.type]
    have he := next_call_wasm σ lim C f vs₀ args
      (C.thread f (vs₀ ++ args ++ [.i32 idx]) C.labels (.call_indirect ty t :: C.rest)) a type inst
      code hfn hlen (by omega)
    have hnext : next σ lim (C.thread f (vs₀ ++ args ++ [.i32 idx]) C.labels
        (.call_indirect ty t :: C.rest)) =
        (.running lim (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args),
          σ) := by
      rw [next_instr_call σ lim C f _ C.labels _ C.rest hmi hinstr]
      simp only [callerFrame] at he
      rw [he]
      rfl
    rw [hnext]
    exact ⟨rfl, replaces_same hP⟩
  · intro σ _ _ l hq hp
    simp_all
  isplitr
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    iunfold funcPt at Hf
    isplitr
    · iexact Hi
    · iapply (seeList_cons _ _).2
      isplitr
      · iexact Hf
      · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Ht]
  · iunfold tablePt at Ht
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ht]
    · iexact Ht
    · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro HQ
  icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
  iunfold tablePt at Hwp
  ispecialize Hwp $$ HQ
  unfold wpInvoke
  iapply Hwp $$ %Ψ %(C.base ++ vs₀) %(callerFrame C f :: C.below) %(by simp; omega) Hi'
  unfold Kont
  isplit
  · iintro %rs HΦ
    rw [retCode_caller]
    icases HK with ⟨HK, -⟩
    ispecialize HK $$ %(vs₀ ++ rs) %f.locals
    simp only [Frame.withLocals_self]
    iapply HK $$ HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-- A host function's behaviour on any well-formed memory with the given
length, limit and bytes: it returns `rs`, the new host state and a memory
with the new length, the same limit and the new bytes. -/
def HostContract (fn : HostFn H) (h : H) (args : List Value) (mx : Option Nat) (bs : List UInt8)
    (rs : List Value) (h' : H) (bs' : List UInt8) : Prop :=
  ∀ mem : Memory, mem.wf → mem.byteSize = bs.length → mem.max = mx →
    (∀ k, k < bs.length → mem.read8 k = bs[k]!) →
    ∃ mem', fn.call h (some mem) args = .return rs h' (some mem') ∧ mem'.wf ∧
      mem'.byteSize = bs'.length ∧ mem'.max = mx ∧ ∀ k, k < bs'.length → mem'.read8 k = bs'[k]!

theorem lookup_setHostMem (σ : Store H) (h' : H) (n : Nat) (mem' : Memory) (hn : n < σ.mems.size)
    (k a i : Nat) :
    lookup { σ with host := h', mems := σ.mems.set! n mem' } (k, a, i) =
      if k = 9 ∧ a = 0 ∧ i = 0 then some (.host h')
      else if (k = 0 ∨ k = 1) ∧ a = n then memCell mem' (k, i) else lookup σ (k, a, i) := by
  have := lookup_setMem { σ with host := h' } n mem' (by simpa using hn) k a i
  simp only at this
  rw [this]
  by_cases h9 : k = 9 ∧ a = 0 ∧ i = 0
  · obtain ⟨rfl, rfl, rfl⟩ := h9
    simp [lookup]
  · rw [ite_eq_right h9]
    split
    · rfl
    · by_cases hk : k = 9
      · subst hk
        rcases a with _ | a <;> rcases i with _ | i <;> simp_all [lookup]
      · exact lookup_with_host σ h' _ (by simpa using hk)

/-- Iris-Wasm's host-call rule: call the module's function `i`, a host
function, owning the host state and the caller's whole memory. -/
theorem wpi_call_host (i a n : Nat) (fn : HostFn H) (h h' : H) (mx : Option Nat)
    (bs bs' : List UInt8) (vs₀ args rs : List Value) (ha : f.mi.funcAddrs[i]? = some a)
    (hn : f.mi.memAddrs[0]? = some n) (hlen : args.length = fn.type.params.length)
    (hc : HostContract fn h args mx bs rs h' bs') :
    a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗ ↦[host] h ∗ n ↦[wmlength] bs.length ∗
      n ↦[wms][ 0 ] bs ∗
      ▷ (↦[host] h' ∗ n ↦[wmlength] bs'.length ∗ n ↦[wms][ 0 ] bs' -∗ Φ.normal (vs₀ ++ rs) f)
      ⊢ wpi lim d f (vs₀ ++ args) [.call i] Φ := by
  unfold wpi
  iintro ⟨#Hf, #Hm, Hh, Hl, Hb, HΦ⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wp_lift lim _
    [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.host fn)), (Loc.memLimit n, .memLimit mx)]
    ((Loc.host, .host h) :: (Loc.memLength n, .memLength bs.length) :: byteCells n 0 bs)
    ((Loc.host, .host h') :: (Loc.memLength n, .memLength bs'.length) :: byteCells n 0 bs')
    (.running lim (C.thread f (vs₀ ++ rs) C.labels C.rest))
  · simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map]
    refine ⟨?_, ?_, byteCells_nodup _ _ _⟩
    · rintro (h1 | ⟨p, hp, hp1⟩)
      · simp [Loc.host, Loc.memLength] at h1
      · have := lookup_byteCells (H := H) n 0 bs p.1
        rw [lookup_of_mem (byteCells_nodup _ _ _) hp, hp1] at this
        simp [] at this
    · rintro ⟨p, hp, hp1⟩
      have := lookup_byteCells (H := H) n 0 bs p.1
      rw [lookup_of_mem (byteCells_nodup _ _ _) hp, hp1] at this
      simp [] at this
  · simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map]
    refine ⟨?_, ?_, byteCells_nodup _ _ _⟩
    · rintro (h1 | ⟨p, hp, hp1⟩)
      · simp [Loc.host, Loc.memLength] at h1
      · have := lookup_byteCells (H := H) n 0 bs' p.1
        rw [lookup_of_mem (byteCells_nodup _ _ _) hp, hp1] at this
        simp [] at this
    · rintro ⟨p, hp, hp1⟩
      have := lookup_byteCells (H := H) n 0 bs' p.1
      rw [lookup_of_mem (byteCells_nodup _ _ _) hp, hp1] at this
      simp [] at this
  · intro σ hRd hP
    have hmi := hmi_of_see hRd
    have hfn : σ.funcs[a]? = some (.host fn) := by
      have := hRd _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    obtain ⟨mem, hmem, hwf, hlenm⟩ := memLength_facts (hP _ (List.mem_cons_of_mem _ List.mem_cons_self))
    obtain ⟨mem2, hmem2, hmax⟩ := memLimit_facts
      (hRd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [hmem] at hmem2; cases hmem2
    have hhost : σ.host = h := by
      have := hP _ List.mem_cons_self
      simpa [Loc.host] using this
    have hrd : ∀ k, k < bs.length → mem.read8 k = bs[k]! := by
      intro k hk
      have := hP _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_byteCells n 0 bs hk)))
      simp only [Nat.zero_add, lookup_byte, hmem, Option.bind_some] at this
      split at this
      · simpa using this
      · cases this
    obtain ⟨mem', hcall, hwf', hsz', hmax', hrd'⟩ := hc mem hwf hlenm hmax hrd
    have hnlt : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
    have hp := popN_args (C.base ++ vs₀) args
    rw [hlen] at hp
    simp only [List.append_assoc] at hp
    have hnext : next σ lim (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest)) =
        (.running lim (C.thread f (vs₀ ++ rs) C.labels C.rest),
          { σ with host := h', mems := σ.mems.set! n mem' }) := by
      simp only [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA]
      simp [Exec.instr, modules_get! hmi, ha, Exec.enter, hfn, hp, hmi, Store.memOf, hn, hmem, hhost,
        hcall, Exec.commitHost, Store.setMemOf]
    rw [hnext]
    refine ⟨rfl, ?_⟩
    intro ⟨k, b, j⟩
    rw [lookup_setHostMem σ h' n mem' hnlt, lookup_cons_pair, lookup_cons_pair, lookup_byteCells,
      lookup_cons_pair, lookup_cons_pair, lookup_byteCells]
    simp only [Loc.host, Loc.memLength, Prod.mk.injEq, Nat.zero_add]
    by_cases h9 : k = 9 ∧ b = 0 ∧ j = 0
    · obtain ⟨rfl, rfl, rfl⟩ := h9; simp
    · rw [ite_eq_right h9, ite_eq_right h9]
      simp only [show ¬(k = 9 ∧ b = 0 ∧ j = 0) from h9, ite_false]
      by_cases hk : (k = 0 ∨ k = 1) ∧ b = n
      · rw [ite_eq_left hk]
        obtain ⟨hk, rfl⟩ := hk
        rw [lookup_mem _ _ _ _ hk, hmem, Option.bind_some]
        rcases hk with rfl | rfl
        · by_cases hj' : j < bs'.length
          · simp [memCell, hwf', hsz', hrd' j hj', hj']
          · by_cases hj : j < bs.length
            · simp [memCell, hwf', hsz', hj', hj]
            · simp [memCell, hwf, hwf', hsz', hlenm, hj', hj]
        · rcases j with _ | _ | j <;> simp [memCell, hwf, hwf', hsz', hmax, hmax']
      · rw [ite_eq_right hk]
        have h1 : ¬(k = 1 ∧ b = n ∧ j = 0) := fun e => hk ⟨.inr e.1, e.2.1⟩
        have h2 : ∀ len, ¬(k = 0 ∧ b = n ∧ j < len) := fun _ e => hk ⟨.inl e.1, e.2.1⟩
        simp [h1, h2]
  · intro σ _ hP l hq hp
    obtain ⟨mem, hmem, hwf, hlenm⟩ := memLength_facts (hP _ (List.mem_cons_of_mem _ List.mem_cons_self))
    obtain ⟨k, b, j⟩ := l
    rw [lookup_cons_pair, lookup_cons_pair, lookup_byteCells] at hq hp
    simp only [Loc.host, Loc.memLength, Prod.mk.injEq, Nat.zero_add] at hq hp
    split at hq
    · rename_i e; rw [ite_eq_left e] at hp; cases hp
    · rename_i e9; rw [ite_eq_right e9] at hp
      split at hq
      · rename_i e; rw [ite_eq_left e] at hp; cases hp
      · rename_i e1; rw [ite_eq_right e1] at hp
        split at hq
        · rename_i e
          obtain ⟨rfl, rfl, _, hj⟩ := e
          split at hp
          · cases hp
          · rename_i e'
            have : ¬ j < bs.length := fun h => e' ⟨rfl, rfl, Nat.zero_le _, h⟩
            simp [lookup_byte, hmem, hwf, hlenm, this]
        · cases hq
  isplitr
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    iapply (seeList_cons _ _).2
    iunfold funcPt at Hf
    isplitr
    · iexact Hf
    iapply (seeList_cons _ _).2
    iunfold memLimit at Hm
    isplitr
    · iexact Hm
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hh Hl Hb]
  · iapply BigSepL.bigSepL_cons.2
    iunfold hostPt at Hh
    isplitl [Hh]
    · iexact Hh
    iapply BigSepL.bigSepL_cons.2
    iunfold memLength at Hl
    isplitl [Hl]
    · iexact Hl
    iunfold memBytes at Hb
    iexact Hb
  inext
  iintro HQ
  icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ1, HQ⟩
  icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ2, HQ3⟩
  unfold Kont
  icases HK with ⟨HK, -⟩
  ispecialize HK $$ %(vs₀ ++ rs) %f.locals
  simp only [Frame.withLocals_self]
  iapply HK
  iapply HΦ
  iunfold hostPt, memLength, memBytes
  isplitl [HQ1]
  · iexact HQ1
  isplitl [HQ2]
  · iexact HQ2
  · iexact HQ3

end Rules

end WasmLogic
