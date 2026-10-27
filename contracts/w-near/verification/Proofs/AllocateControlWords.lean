import Proofs.AllocateLinks

/-! Exact remaining scalar writes in f580's low-flags-zero split path. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def maskStore (s : Store NearState) (op index readOffset writeOffset : Nat) (memory : Memory) (address mask : UInt32) :=
  storeI32 (paid s op 6) index (address.toNat+writeOffset) memory (readI32 memory (address.toNat+readOffset) &&& mask)

theorem wp_mask_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (slot readOffset writeOffset : Nat) (address mask : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 address)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : address.toNat+readOffset+4 ≤ memory.byteSize) (hw : address.toNat+writeOffset+4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (maskStore s cfg.regularOpCost index readOffset writeOffset memory address mask)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      ([.local_get slot,.local_get slot,.load .i32 none {align:=2,offset:=readOffset},.i32_const mask,
        .i32_binop .and,.store .i32 none {align:=2,offset:=writeOffset}]++code))) (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hm5 : (paid s op 5).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hmem5 : (paid s op 5).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ s limits stack frame callers _ slot (.i32 address) post hl (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s op 1) limits _ frame callers _ slot (.i32 address) post hl
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+3) _ (paid s op 2) limits (stack.push (.i32 address)) frame callers _
    {align:=2,offset:=readOffset} address mi index memory post hm2 hi hmem2 hr
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 3) limits _ frame callers _ mask post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+1) _ (paid s op 4) limits (stack.push (.i32 address)) frame callers _
    (readI32 memory (address.toNat+readOffset)) mask post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 5) limits stack frame callers code {align:=2,offset:=writeOffset}
    address (readI32 memory (address.toNat+readOffset) &&& mask) mi index memory post hm5 hi hmem5 hw
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

def taggedTeeStore (s : Store NearState) (op index readOffset writeOffset : Nat)
    (memory : Memory) (target source value : UInt32) :=
  storeI32 (paid s op 9) index (target.toNat+writeOffset) memory (Allocate.taggedValue memory source readOffset value)

/-- The actual head-link write also saves the tagged pointer in a local. -/
theorem wp_tagged_tee_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (targetSlot sourceSlot valueSlot outputSlot readOffset writeOffset : Nat) (target source value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ht : frame.locals[targetSlot]? = some (.i32 target)) (hs : frame.locals[sourceSlot]? = some (.i32 source))
    (hv : frame.locals[valueSlot]? = some (.i32 value)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : source.toNat+readOffset+4 ≤ memory.byteSize) (hw : target.toNat+writeOffset+4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (taggedTeeStore s cfg.regularOpCost index readOffset writeOffset memory target source value)
      limits stack {frame with locals:=frame.locals.set! outputSlot (.i32 (Allocate.taggedValue memory source readOffset value))} callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers
      (Allocate.taggedPrefix targetSlot sourceSlot valueSlot readOffset ++
        [.local_tee outputSlot,.store .i32 none {align:=2,offset:=writeOffset}] ++ code))) (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let updated : CallFrame := {frame with locals:=frame.locals.set! outputSlot (.i32 (Allocate.taggedValue memory source readOffset value))}
  have hm8 : (paid s op 8).modules[updated.inst]? = some mi := by simpa only [paid,chargedStore,updated] using hm
  have hmem8 : (paid s op 8).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have last := wp_i32_store cfg fuel rest (paid s op 8) limits stack updated callers code
    {align:=2,offset:=writeOffset} target (Allocate.taggedValue memory source readOffset value) mi index memory post hm8 hi hmem8 hw
    (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) hnext
  have tee := wp_local_tee cfg (fuel+1) (op+rest) (paid s op 7) limits (stack.push (.i32 target)) frame callers
    (.store .i32 none {align:=2,offset:=writeOffset}::code) outputSlot (.i32 (Allocate.taggedValue memory source readOffset value)) post
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) last
  have result := Allocate.wp_tagged_value cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.local_tee outputSlot::.store .i32 none {align:=2,offset:=writeOffset}::code)
    targetSlot sourceSlot valueSlot readOffset target source value mi index memory post ht hs hv hm hi hmem hr
    (hc.mono (by dsimp [op]; omega)) tee
  have cost : 7*cfg.regularOpCost+(op+(op+rest))=9*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,List.append_assoc] using result
end WNear.Proofs.AllocateSearch
