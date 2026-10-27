import Proofs.ValueReturnWrapperBody
import Proofs.ValueReturnOuterCall

/-! The actual returning f545 call, assembled from its checked scalar wrapper
and the complete checked f456 path. -/
namespace WNear.Proofs.ValueReturnWrapperCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.ValueReturnWrapperBody
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- The original caller pays its opcode and the actual three-i32 activation. -/
theorem entry_credits (cfg : WasmConfig) (s : Store NearState) (rest : Nat)
    (sp pointer length : UInt32) (memory : Memory) (p : ValueReturnOuterBody.Layout)
    (hc : s.host.gas.Credits (278 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + rest)) :
    (entered545 s cfg.regularOpCost).host.gas.Credits
      (bodyBudget cfg (entered545 s cfg.regularOpCost) sp pointer length p.globalIndex p.memoryIndex memory p + rest) := by
  let op := cfg.regularOpCost
  let price := ValueReturnHost.cost s.host p.len.toNat
  have hop := GasCounter.burn_credits s.host.gas op (277 * op + price + rest) (hc.mono (by dsimp [op, price]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (267 * op + price + rest)
    (hop.2.2.2.mono (by omega))
  have c : (entered545 s op).host.gas.Credits (267 * op + price + rest) := ha.2.2.2
  have hf := callFee_eq cfg s sp pointer length memory p
  change fee cfg (entered545 s cfg.regularOpCost) sp pointer length p.globalIndex p.memoryIndex memory p = _ at hf
  simpa only [bodyBudget, hf, op, price] using c

/-- The canonical resource record is independent of both saved code suffixes.
Actual call execution still constructs and restores those saved frames. -/
theorem outer_ready_for_call (cfg : WasmConfig) (extra : Nat) (s : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (sp pointer length : UInt32) (memory : Memory)
    (p : ValueReturnOuterBody.Layout) (hr : ValueReturnWrapperBody.Resources cfg extra s limits frame sp pointer length memory p)
    (savedWrapper savedCaller : CallFrame) :
    ValueReturnOuterBody.Ready cfg extra
      (outerEntry (entered545 s cfg.regularOpCost) cfg.regularOpCost p.globalIndex p.memoryIndex sp pointer length memory)
      limits (outerLeaf (leaf545 frame.inst pointer length) [] sp) [savedWrapper, savedCaller] p :=
  outerReady_callers cfg extra _ limits _ _ _ p (by simp) hr.outer

def entered456 (s : Store NearState) (op : Nat) : Store NearState := chargedStore (chargedStore s op) (10 * op)
def leaf456 (frame : CallFrame) (base : List Value) (p : ValueReturnOuterBody.Layout) : CallFrame :=
  {locals := #[.i32 p.interface, .i32 p.slice, .i32 0, .i32 0]
   inst := frame.inst
   arity := 0
   height := base.length
   labels := []
   code := []}

/-- A real direct456 call, including its ten-unit activation and free leave.
The only path conditions are the primitive resource record on its actual entry. -/
theorem wp_call_outer (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : ValueReturnOuterBody.Layout) (post : Post)
    (hindex : p.mi.funcAddrs[456]? = some 456)
    (hfunction : s.funcs[456]? = some (.wasm WNear.Binary.ValueReturnOuter.signature frame.inst WNear.Binary.ValueReturnOuter.function))
    (hr : ValueReturnOuterBody.Ready cfg extra (entered456 s cfg.regularOpCost) limits
      (leaf456 frame base p) ({frame with code} :: callers) p)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + ValueReturnOuterBody.budget cfg (entered456 s cfg.regularOpCost) p + rest))
    (hnext : WP cfg fuel (.next (atCode (ValueReturnOuterBody.finalStore cfg (entered456 s cfg.regularOpCost) p)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 161) (.next (atCode s limits (base ++ [Value.i32 p.interface, .i32 p.slice]).toArray
      frame callers (.call 456 :: code)))
      (11 * cfg.regularOpCost + ValueReturnOuterBody.budget cfg (entered456 s cfg.regularOpCost) p + rest) post := by
  let op := cfg.regularOpCost
  let active := entered456 s op
  let leaf := leaf456 frame base p
  let saved := {frame with code}
  let b := ValueReturnOuterBody.budget cfg active p
  have hop := GasCounter.burn_credits s.host.gas op (10 * op + (b + rest)) (hc.mono (by dsimp [op, b, active]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (b + rest) hop.2.2.2
  have ca : active.host.gas.Credits (b + rest) := ha.2.2.2
  have cf := ValueReturnOuterBody.final_credits cfg extra rest active limits leaf (saved :: callers) p hr ca
  have hleave := wp_leave_wasm cfg fuel rest (ValueReturnOuterBody.finalStore cfg active p) limits base []
    (ValueReturnOuterBody.finalFrame leaf p) saved callers post rfl rfl rfl cf
  simp only [List.append_nil] at hleave
  have hn : WP cfg fuel (.next (atCode (ValueReturnOuterBody.finalStore cfg active p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have hleft := hleave hn
  have hb := ValueReturnOuterBody.wp_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] p post hr ca
  have hbody := hb hleft
  rw [show fuel + 1 + 159 = fuel + 160 by omega] at hbody
  have hm : s.modules[frame.inst]? = some p.mi := by
    simpa only [entered456, chargedStore, leaf, leaf456] using hr.code.module
  have he := wp_call_wasm cfg (fuel + 160) (b + rest) s limits base [.i32 p.interface, .i32 p.slice] frame callers code
    456 456 p.mi WNear.Binary.ValueReturnOuter.signature frame.inst WNear.Binary.ValueReturnOuter.function post
    hm hindex hfunction rfl (by have hd := hr.depth; simp only [List.length_cons] at hd; omega)
  have hact : activationGas op (wasmLocals WNear.Binary.ValueReturnOuter.function [.i32 p.interface, .i32 p.slice]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.ValueReturnOuter.function, activationGas, ValType.default]
  rw [hact] at he
  have he' := he (hc.mono (by dsimp [op, b, active]; omega))
  have hbody' : WP cfg (fuel + 160) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnOuter.signature frame.inst WNear.Binary.ValueReturnOuter.function [.i32 p.interface, .i32 p.slice]))
      (b + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.ValueReturnOuter.signature, WNear.Binary.ValueReturnOuter.function,
      leaf, leaf456, saved, atCode, ValType.default, b] using hbody
  have hall := he' hbody'
  rw [show fuel + 160 + 1 = fuel + 161 by omega,
    show cfg.regularOpCost + (10 * op + (b + rest)) = 11 * cfg.regularOpCost + ValueReturnOuterBody.budget cfg (entered456 s cfg.regularOpCost) p + rest by dsimp [op, b, active]; omega] at hall
  exact hall

/-- The concrete final545 store retains the caller's reserved credits. -/
theorem calledStore_credits (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (sp pointer length : UInt32) (memory : Memory) (p : ValueReturnOuterBody.Layout)
    (hr : ValueReturnWrapperBody.Resources cfg extra s limits frame sp pointer length memory p)
    (hc : s.host.gas.Credits (278 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + rest)) :
    (calledStore cfg s sp pointer length memory p).host.gas.Credits rest := by
  let initial := entered545 s cfg.regularOpCost
  let active := outerEntry initial cfg.regularOpCost p.globalIndex p.memoryIndex sp pointer length memory
  have ci := entry_credits cfg s rest sp pointer length memory p hc
  have co := outerEntry_credits cfg initial rest sp pointer length p.globalIndex p.memoryIndex memory p ci
  have co' : active.host.gas.Credits (ValueReturnOuterBody.budget cfg active p + (4 * cfg.regularOpCost + rest)) := by
    simpa only [ValueReturnOuterBody.budget, ValueReturnOuterBody.fee, ValueReturnWrapperBody.fee, active] using co
  have cf := ValueReturnOuterBody.final_credits cfg extra (4 * cfg.regularOpCost + rest) active limits
    (outerLeaf (leaf545 frame.inst pointer length) [] sp) [preparedFrame (leaf545 frame.inst pointer length) sp, frame] p hr.outer co'
  exact (finalStore_gas (ValueReturnOuterBody.finalStore cfg active p) cfg.regularOpCost p.globalIndex rest sp cf).2.2

/-- Actual545 normal-return contract, including its caller opcode, ten-unit
activation, complete456 call, nested borrowing/dispatch/cleanup, and free leave.
Every semantic premise is a primitive member of Resources. -/
theorem calleeContract (cfg : WasmConfig) (extra : Nat) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (sp pointer length : UInt32) (memory : Memory) (p : ValueReturnOuterBody.Layout)
    (hr : ValueReturnWrapperBody.Resources cfg extra s limits frame sp pointer length memory p) :
    WNear.Proofs.TotalSupply.CalleeContract cfg limits frame 545 [.i32 pointer, .i32 length] s
      (calledStore cfg s sp pointer length memory p)
      (278 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat) 182 := by
  constructor
  · intro rest hc
    exact calledStore_credits cfg extra rest s limits frame sp pointer length memory p hr hc
  · intro fuel rest code post hc hnext
    let op := cfg.regularOpCost
    let price := ValueReturnHost.cost s.host p.len.toNat
    let initial := entered545 s op
    let leaf := leaf545 frame.inst pointer length
    let saved := {frame with code}
    let frame' := preparedFrame leaf sp
    let prepared := preparedStore initial op p.globalIndex p.memoryIndex sp pointer length memory
    let active := outerEntry initial op p.globalIndex p.memoryIndex sp pointer length memory
    let after := afterOuter cfg initial sp pointer length p.globalIndex p.memoryIndex memory p
    have ci := entry_credits cfg s rest sp pointer length memory p hc
    have co := outerEntry_credits cfg initial rest sp pointer length p.globalIndex p.memoryIndex memory p ci
    have co' : active.host.gas.Credits (ValueReturnOuterBody.budget cfg active p + (4 * op + rest)) := by
      simpa only [ValueReturnOuterBody.budget, ValueReturnOuterBody.fee, ValueReturnWrapperBody.fee, active, op] using co
    have cf := ValueReturnOuterBody.final_credits cfg extra (4 * op + rest) active limits
      (outerLeaf leaf [] sp) [frame', frame] p hr.outer co'
    have cp := (preparedStore_gas initial op p.globalIndex p.memoryIndex
      (252 * op + price + rest) sp pointer length memory (ci.mono (by
        have hf := callFee_eq cfg s sp pointer length memory p
        change fee cfg initial sp pointer length p.globalIndex p.memoryIndex memory p = price at hf
        dsimp [bodyBudget]; rw [hf]; dsimp [op]; omega))).2.2
    have cfinal := calledStore_credits cfg extra rest s limits frame sp pointer length memory p hr hc
    have hleave := wp_leave_wasm cfg fuel rest (calledStore cfg s sp pointer length memory p) limits [] [] frame' saved [] post
      rfl rfl rfl cfinal
    simp only [List.append_nil] at hleave
    have hleft := hleave hnext
    have hrestore := wp_epilogue cfg (fuel + 1) rest after limits #[] frame' [saved] [] sp p.mi p.globalIndex p.global post
      (by simp [frame', preparedFrame, leaf, leaf545, WNear.Proofs.StorePair.voidFrame])
      (Resources.afterModule cfg extra s limits frame sp pointer length memory p hr) hr.globalIndex
      (Resources.afterGlobal cfg extra s limits frame sp pointer length memory p hr) cf
    have hleft' : WP cfg (fuel + 1) (.next (atCode (finalStore after op p.globalIndex sp) limits #[] frame' [saved] [])) rest post := hleft
    have restored := hrestore hleft'
    rw [show fuel + 1 + 4 = fuel + 5 by omega] at restored
    have hready := outer_ready_for_call cfg extra s limits frame sp pointer length memory p hr
      {frame' with code := WNear.Binary.ValueReturnWrapper.epilogue} saved
    have ready' : ValueReturnOuterBody.Ready cfg extra (entered456 prepared op) limits
        (leaf456 frame' [] p) ({frame' with code := WNear.Binary.ValueReturnWrapper.epilogue} :: [saved]) p := by
      simpa only [leaf456, outerLeaf, leaf, frame', preparedFrame, leaf545, WNear.Proofs.StorePair.voidFrame,
        hr.outerInterface, hr.outerSlice, entered456, outerEntry, prepared, active] using hready
    have hres := preparedStore_resources initial op p.globalIndex p.memoryIndex sp pointer length memory
    have hf : prepared.funcs[456]? = some (.wasm WNear.Binary.ValueReturnOuter.signature frame'.inst WNear.Binary.ValueReturnOuter.function) := by
      have h := congrArg (fun t : Store NearState => t.funcs[456]?) hres
      simpa only [prepared, initial, entered545, chargedStore, frame', preparedFrame, leaf, leaf545, WNear.Proofs.StorePair.voidFrame] using h.trans hr.outerFunction
    have hcall := wp_call_outer cfg extra (fuel + 5) (4 * op + rest) prepared limits [] frame' [saved]
      WNear.Binary.ValueReturnWrapper.epilogue p post hr.outerIndex hf ready'
      (cp.mono (by
        have hp := callFee_eq cfg s sp pointer length memory p
        change fee cfg initial sp pointer length p.globalIndex p.memoryIndex memory p = price at hp
        change 11 * cfg.regularOpCost + (237 * cfg.regularOpCost + fee cfg initial sp pointer length p.globalIndex p.memoryIndex memory p) + (4 * op + rest) ≤ _
        rw [hp]; dsimp [op]; omega))
    have restored' : WP cfg (fuel + 5) (.next (atCode (ValueReturnOuterBody.finalStore cfg (entered456 prepared op) p)
        limits #[] frame' [saved] WNear.Binary.ValueReturnWrapper.epilogue)) (4 * op + rest) post := by
      simpa only [after, afterOuter, active, entered456, outerEntry, prepared, List.append_nil, op] using restored
    have called := hcall restored'
    have hcFee : fee cfg initial sp pointer length p.globalIndex p.memoryIndex memory p = price := by
      exact callFee_eq cfg s sp pointer length memory p
    have hbudget : ValueReturnOuterBody.budget cfg (entered456 prepared op) p = 237 * op + price := by
      simpa only [ValueReturnOuterBody.budget, ValueReturnOuterBody.fee, entered456, prepared,
        ValueReturnWrapperBody.fee, outerEntry, op] using congrArg (fun f => 237 * cfg.regularOpCost + f) hcFee
    rw [hbudget] at called
    rw [show 11 * cfg.regularOpCost + (237 * op + price) + (4 * op + rest) = 252 * op + price + rest by dsimp [op]; omega] at called
    have called' : WP cfg (fuel + 166) (.next (atCode prepared limits
        ((#[].push (.i32 1055020)).push (.i32 (sp - 16 + 8))) frame' [saved]
        (.call 456 :: WNear.Binary.ValueReturnWrapper.epilogue))) (252 * op + price + rest) post := by
      rw [show fuel + 5 + 161 = fuel + 166 by omega] at called
      simpa [hr.outerInterface, hr.outerSlice] using called
    have hprefix := wp_prefix cfg (fuel + 166) (252 * op + price + rest) initial limits #[] leaf [saved]
      (.call 456 :: WNear.Binary.ValueReturnWrapper.epilogue) sp pointer length p.mi p.globalIndex p.memoryIndex
      {p.global with value := .i32 sp} memory post rfl rfl (by simp [leaf, leaf545, WNear.Proofs.StorePair.voidFrame])
      hr.module hr.globalIndex hr.global rfl hr.memoryIndex hr.memoryLookup hr.memoryWf hr.scratchBound
      (ci.mono (by dsimp [bodyBudget]; rw [hcFee]; dsimp [op]; omega))
    have prefixed := hprefix called'
    rw [show fuel + 166 + 15 = fuel + 181 by omega,
      show 15 * cfg.regularOpCost + (252 * op + price + rest) = 267 * op + price + rest by dsimp [op]; omega] at prefixed
    have body : WP cfg (fuel + 181) (.next (atCode initial limits #[] leaf [saved] WNear.Binary.ValueReturnWrapper.body))
        (267 * op + price + rest) post := by
      simpa only [WNear.Binary.ValueReturnWrapper.body, List.append_assoc, List.cons_append, List.nil_append] using prefixed
    have hentry := wp_call_wasm cfg (fuel + 181) (267 * op + price + rest) s limits [] [.i32 pointer, .i32 length]
      frame [] code 545 545 p.mi WNear.Binary.ValueReturnWrapper.signature frame.inst WNear.Binary.ValueReturnWrapper.function post
      hr.module hr.functionIndex hr.function rfl (by have hd := hr.outer.depth; simp only [List.length_cons, List.length_nil] at hd ⊢; omega)
    rw [activation] at hentry
    have hentry' := hentry (hc.mono (by dsimp [op, price]; omega))
    have body' : WP cfg (fuel + 181) (.next (wasmCallee initial limits [] frame [] code
        WNear.Binary.ValueReturnWrapper.signature frame.inst WNear.Binary.ValueReturnWrapper.function [.i32 pointer, .i32 length]))
        (267 * op + price + rest) post := by
      simpa [wasmCallee, wasmLocals, WNear.Binary.ValueReturnWrapper.signature, WNear.Binary.ValueReturnWrapper.function,
        initial, leaf, leaf545, WNear.Proofs.StorePair.voidFrame, saved, atCode, ValType.default] using body
    have hall := hentry' body'
    rw [show fuel + 181 + 1 = fuel + 182 by omega,
      show cfg.regularOpCost + (10 * cfg.regularOpCost + (267 * op + price + rest)) = 278 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + rest by dsimp [op, price]; omega] at hall
    exact hall

end WNear.Proofs.ValueReturnWrapperCall
