import Binary.StateDispatchRegisterOuter
import Proofs.StateDispatchReadCleanup
import Proofs.InterfaceStack

/-! Actual f523 post-read high-four-byte copy precedes the low-eight-byte load. -/
namespace WNear.Proofs.StateDispatchRegisterOuterTail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64
set_option maxRecDepth 16384

def highMemory (memory : Memory) (out scratch : UInt32) :=
  writeI32 memory (out+8).toNat (readI32 memory ((scratch+32)+8).toNat)
def finalMemory (memory : Memory) (out scratch : UInt32) :=
  writeI64 (highMemory memory out scratch) out.toNat (readI64 (highMemory memory out scratch) (scratch.toNat+32))
def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (out scratch : UInt32) :=
  storeI32 (paid s op 10) index (out+8).toNat memory (readI32 memory ((scratch+32)+8).toNat)
def copyStore (s : Store NearState) (op index : Nat) (memory : Memory) (out scratch : UInt32) :=
  storeI64 (paid (highStore s op index memory out scratch) op 4) index out.toNat (highMemory memory out scratch)
    (readI64 (highMemory memory out scratch) (scratch.toNat+32))
def after (s : Store NearState) (op index globalIndex : Nat) (memory : Memory) (out scratch : UInt32) :=
  setGlobal (paid (paid (copyStore s op index memory out scratch) op 1) op 4) globalIndex (.i32 (scratch+48))

attribute [local irreducible] highStore copyStore after

private theorem wp_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]? = some  (.i32 out)) (h2 : frame.locals[2]? = some  (.i32 scratch))
    (hm : s.modules[frame.inst]? = some  mi) (hi : mi.memAddrs[0]? = some  index) (hmem : s.mems[index]? = some  memory)
    (hs : ((scratch+32)+8).toNat+4≤memory.byteSize) (hd : (out+8).toNat+4≤memory.byteSize)
    (hc : s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers
      ([.local_get 0,.i32_const 8,.i32_binop .add,.local_get 2,.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,
        .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]++code))) (10*cfg.regularOpCost+rest) post := by
  have hm8 : (paid s cfg.regularOpCost 8).modules[frame.inst]? = some  mi := by simpa only [paid,chargedStore] using hm
  have hm9 : (paid s cfg.regularOpCost 9).modules[frame.inst]? = some  mi := by simpa only [paid,chargedStore] using hm
  have mem8 : (paid s cfg.regularOpCost 8).mems[index]? = some  memory := by simpa only [paid,chargedStore] using hmem
  have mem9 : (paid s cfg.regularOpCost 9).mems[index]? = some  memory := by simpa only [paid,chargedStore] using hmem
  rw [show 10*cfg.regularOpCost+rest=cfg.regularOpCost+(9*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+9) _ s limits stack frame callers _ 0 (.i32 out) post h0 (hc.mono (by omega))
  rw [show 9*cfg.regularOpCost+rest=cfg.regularOpCost+(8*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+8) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 8*cfg.regularOpCost+rest=cfg.regularOpCost+(7*cfg.regularOpCost+rest) by omega]
  apply wp_i32_add cfg (fuel+7) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ out 8 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+6) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 2 (.i32 scratch) post h2
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+5) _ (paid s cfg.regularOpCost 4) limits _ frame callers _ 32 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_i32_add cfg (fuel+4) _ (paid s cfg.regularOpCost 5) limits _ frame callers _ scratch 32 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s cfg.regularOpCost 6) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_i32_add cfg (fuel+2) _ (paid s cfg.regularOpCost 7) limits _ frame callers _ (scratch+32) 8 post
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_i32_load cfg (fuel+1) _ (paid s cfg.regularOpCost 8) limits _ frame callers _ {align:=2,offset:=0} ((scratch+32)+8) mi index memory post hm8 hi mem8 (by simpa using hs)
  · exact paid_credits s cfg.regularOpCost 8 _ (hc.mono (by omega))
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 9) limits stack frame callers code {align:=2,offset:=0} (out+8)
    (readI32 memory ((scratch+32)+8).toNat) mi index memory post hm9 hi mem9 (by simpa using hd)
  · exact paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))
  · simpa only [highStore,paid,Nat.add_zero] using hnext

private theorem wp_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]? = some  (.i32 out)) (h2 : frame.locals[2]? = some  (.i32 scratch))
    (hm : s.modules[frame.inst]? = some  mi) (hi : mi.memAddrs[0]? = some  index) (hmem : s.mems[index]? = some  memory)
    (hs : scratch.toNat+40≤memory.byteSize) (hd : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (storeI64 (paid s cfg.regularOpCost 4) index out.toNat memory (readI64 memory (scratch.toNat+32))) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      ([.local_get 0,.local_get 2,.load .i64 none {align:=3,offset:=32},.store .i64 none {align:=2,offset:=0}]++code))) (4*cfg.regularOpCost+rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some  mi := by simpa only [paid,chargedStore] using hm
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some  mi := by simpa only [paid,chargedStore] using hm
  have mem2 : (paid s cfg.regularOpCost 2).mems[index]? = some  memory := by simpa only [paid,chargedStore] using hmem
  have mem3 : (paid s cfg.regularOpCost 3).mems[index]? = some  memory := by simpa only [paid,chargedStore] using hmem
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 0 (.i32 out) post h0 (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 2 (.i32 scratch) post h2
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_i64_load cfg (fuel+1) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ {align:=3,offset:=32} scratch mi index memory post hm2 hi mem2 (by dsimp only;omega)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code {align:=2,offset:=0} out (readI64 memory (scratch.toNat+32)) mi index memory post hm3 hi mem3 (by simpa using hd)
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  · simpa only [paid,Nat.add_zero] using hnext
/-- The four-byte output store occurs before the eight-byte source load.
Bounds refer to the exact wrapping i32 address calculations. -/
theorem wp_copy (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 out)) (h2 : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hw : memory.wf) (hhs : ((scratch+32)+8).toNat+4≤memory.byteSize) (hhd : (out+8).toNat+4≤memory.byteSize)
    (hls : scratch.toNat+40≤memory.byteSize) (hld : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (14*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copyStore s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+14) (.next (atCode s limits stack frame callers (WNear.Binary.StateDispatchRegisterOuter.copyCode++code))) (14*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have cut : 10*op+(4*op+rest)≤14*cfg.regularOpCost+rest := by dsimp [op];omega
  have ch : (highStore s op index memory out scratch).host.gas.Credits (4*op+rest) := by
    unfold highStore;rw [storeI32_host];exact paid_credits s op 10 _ (hc.mono cut)
  have mh : (highStore s op index memory out scratch).mems[index]? = some (highMemory memory out scratch) := by
    unfold highStore
    exact storeI32_memory (paid s op 10) index (out+8).toNat memory (readI32 memory ((scratch+32)+8).toNat) (by simpa only [paid,chargedStore] using hmem)
  have moduleH : (highStore s op index memory out scratch).modules[frame.inst]? = some mi := by
    simpa only [highStore,storeI32_modules,paid,chargedStore] using hm
  have shape := writeI32_spec memory (out+8).toNat (readI32 memory ((scratch+32)+8).toNat) hw hhd
  have ls : scratch.toNat+40≤(highMemory memory out scratch).byteSize := by rw [highMemory,shape.2.1];exact hls
  have ld : out.toNat+8≤(highMemory memory out scratch).byteSize := by rw [highMemory,shape.2.1];exact hld
  have ln : WP cfg fuel (.next (atCode (storeI64 (paid (highStore s op index memory out scratch) op 4) index out.toNat (highMemory memory out scratch)
      (readI64 (highMemory memory out scratch) (scratch.toNat+32))) limits stack frame callers code)) rest post := by
    simpa only [copyStore,op] using hnext
  have low := wp_low cfg fuel rest (highStore s op index memory out scratch) limits stack frame callers code out scratch mi index (highMemory memory out scratch) post h0 h2 moduleH hi mh ls ld ch ln
  have first := wp_high cfg (fuel+4) (4*op+rest) s limits stack frame callers
    ([.local_get 0,.local_get 2,.load .i64 none {align:=3,offset:=32},.store .i64 none {align:=2,offset:=0}]++code)
    out scratch mi index memory post h0 h2 hm hi hmem hhs hhd (hc.mono cut) low
  simpa only [WNear.Binary.StateDispatchRegisterOuter.copyCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 10*cfg.regularOpCost+(4*op+rest)=14*cfg.regularOpCost+rest by dsimp [op];omega] using first

/-- The complete post-f435 scalar suffix: fourteen copy operations, the
actual branch out of two blocks, and four stack-restoration operations. -/
theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix fallback : Expr) (out scratch : UInt32) (mi : ModuleInst) (index globalIndex : Nat)
    (memory : Memory) (global : GlobalInst) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 out)) (h2 : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hg : s.globals[globalIndex]? = some global)
    (hw : memory.wf) (hhs : ((scratch+32)+8).toNat+4≤memory.byteSize) (hhd : (out+8).toNat+4≤memory.byteSize)
    (hls : scratch.toNat+40≤memory.byteSize) (hld : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (19*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index globalIndex memory out scratch) limits stack frame callers suffix)) rest post) :
    WP cfg (fuel+19) (.next (atCode s limits stack
      (StateDispatchReadCleanup.nested frame stack.size (WNear.Binary.StateDispatchRegisterOuter.epilogue++suffix) fallback)
      callers WNear.Binary.StateDispatchRegisterOuter.afterRead)) (19*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have cut : 14*op+(5*op+rest)≤19*cfg.regularOpCost+rest := by dsimp [op];omega
  let copied := copyStore s op index memory out scratch
  have highCredit : (highStore s op index memory out scratch).host.gas.Credits (9*op+rest) := by
    unfold highStore;rw [storeI32_host];exact paid_credits s op 10 _ (hc.mono (by dsimp [op];omega))
  have copyCredit : copied.host.gas.Credits (5*op+rest) := by
    unfold copied copyStore;rw [storeI64_host];exact paid_credits _ op 4 _ (highCredit.mono (by omega))
  have branchCredit : (paid copied op 1).host.gas.Credits (4*op+rest) := paid_credits copied op 1 _ (copyCredit.mono (by omega))
  have moduleC : (paid copied op 1).modules[frame.inst]? = some mi := by
    simpa only [paid,chargedStore,copied,copyStore,storeI64_modules,highStore,storeI32_modules] using hm
  have globalC : (paid copied op 1).globals[globalIndex]? = some global := by
    simpa only [paid,chargedStore,copied,copyStore,storeI64_globals,highStore,storeI32_globals] using hg
  have restore := InterfaceStack.wp_restore cfg fuel rest (paid copied op 1) limits stack frame callers suffix mi globalIndex global scratch 2 48 post h2 moduleC hgi globalC branchCredit
    (by simpa only [after,copied,op] using hnext)
  have rn : WP cfg (fuel+4) (.next (atCode (paid copied op 1) limits stack frame callers (WNear.Binary.StateDispatchRegisterOuter.epilogue++suffix))) (4*op+rest) post := by
    simpa only [WNear.Binary.StateDispatchRegisterOuter.epilogue,op] using restore
  have branch := wp_br_two_blocks cfg (fuel+4) (4*op+rest) copied limits stack frame callers (WNear.Binary.StateDispatchRegisterOuter.epilogue++suffix) fallback [] post
    (copyCredit.mono (by dsimp [op];omega)) (by simpa only [paid,op] using rn)
  have cn : WP cfg (fuel+5) (.next (atCode copied limits stack
      (StateDispatchReadCleanup.nested frame stack.size (WNear.Binary.StateDispatchRegisterOuter.epilogue++suffix) fallback) callers [.br 1])) (5*op+rest) post := by
    simpa only [StateDispatchReadCleanup.nested,StateDispatchStorageCleanup.nested,op,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(4*op+rest)=5*op+rest by dsimp [op];omega] using branch
  have copyProof := wp_copy cfg (fuel+5) (5*op+rest) s limits stack
    (StateDispatchReadCleanup.nested frame stack.size (WNear.Binary.StateDispatchRegisterOuter.epilogue++suffix) fallback) callers [.br 1] out scratch mi index memory post
    h0 h2 hm hi hmem hw hhs hhd hls hld (hc.mono cut) cn
  simpa only [WNear.Binary.StateDispatchRegisterOuter.afterRead,Nat.add_assoc,Nat.reduceAdd,
    show 14*cfg.regularOpCost+(5*op+rest)=19*cfg.regularOpCost+rest by dsimp [op];omega] using copyProof
theorem after_credits (s : Store NearState) (op index globalIndex rest : Nat) (memory : Memory) (out scratch : UInt32)
    (hc : s.host.gas.Credits (19*op+rest)) : (after s op index globalIndex memory out scratch).host.gas.Credits rest := by
  have b0 : 10*op+(9*op+rest)≤19*op+rest := by omega
  have b1 : 4*op+(5*op+rest)≤9*op+rest := by omega
  have b2 : 1*op+(4*op+rest)≤5*op+rest := by omega
  have ch : (highStore s op index memory out scratch).host.gas.Credits (9*op+rest) := by
    unfold highStore;rw [storeI32_host];exact paid_credits s op 10 _ (hc.mono b0)
  have cl : (copyStore s op index memory out scratch).host.gas.Credits (5*op+rest) := by
    unfold copyStore;rw [storeI64_host];exact paid_credits _ op 4 _ (ch.mono b1)
  have cb := paid_credits (copyStore s op index memory out scratch) op 1 (4*op+rest) (cl.mono b2)
  unfold after
  exact paid_credits _ op 4 rest cb

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem after_memory (s : Store NearState) (op index globalIndex : Nat) (memory : Memory) (out scratch : UInt32)
    (hm : s.mems[index]? = some memory) :
    (after s op index globalIndex memory out scratch).mems[index]? = some (finalMemory memory out scratch) := by
  have mh : (highStore s op index memory out scratch).mems[index]? = some (highMemory memory out scratch) := by
    unfold highStore
    exact storeI32_memory _ index (out+8).toNat memory (readI32 memory ((scratch+32)+8).toNat) (by simpa only [mems_paid] using hm)
  have ml : (copyStore s op index memory out scratch).mems[index]? = some (finalMemory memory out scratch) := by
    unfold copyStore
    exact storeI64_memory _ index out.toNat (highMemory memory out scratch) (readI64 (highMemory memory out scratch) (scratch.toNat+32))
      (by simpa only [mems_paid] using mh)
  simpa only [after,setGlobal,mems_paid] using ml
end WNear.Proofs.StateDispatchRegisterOuterTail


