import Bridge.Functions.Interface

/-!
# The functions around every call through the blockchain interface

On an installed interface (`Interface.iface`), every `LocalKey::with` of an
`env::*` wrapper runs:

* `Key::get` (468) on the key's state 1: `key + 4`, without initialising
  (`f468_spec`, 8); `__getit` (565) through it: the `RefCell` 1074904
  (`f565_spec`, 20);
* `BorrowRef::new` (494) on the flag 0: the flag 1 (`f494_spec`, 30);
  `RefCell::borrow` (429) through it: the `Ref` (`cell + 4`, `cell`) at
  `out` (`f429_spec`, 60);
* `Option::expect` (430) on a `Some` (`f430_spec`, 3);
* `drop_in_place<BorrowRef>` (431): the flag decremented (`f431_spec`, 26);
* `Result::expect` (432) on an `Ok` (`f432_spec`, 14).

Also the flexible rules `mwpi_select_true'` and `mwpi_call_indirect'` (the
credits any amount covering the cost, for use with `mstep`).

The costs are in `regular_op_cost`s, each callee's activation included in
its caller's.
-/

namespace WNear.Binary.Borrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Flexible rules for `select` and `call_indirect` -/

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- `select` on a nonzero condition, the stack `[a, b, c]`. -/
theorem mwpi_select_true' {t : Option (List ValType)} {a b : Value} {c : UInt32} :
    credits Cg K ∗ ⌜cfg.regularOpCost ≤ K ∧ c ≠ 0⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal [a] f)
      ⊢ mwpi cfg lim d f [a, b, .i32 c] [.select t] Φ := by
  iintro ⟨Hc, %⟨hK, hc⟩, H⟩
  have h := mwpi_select_true (vs := []) (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f)
    (Cg := Cg) (R := K - cfg.regularOpCost) t a b c hc
  simp only [List.nil_append] at h
  iapply h
  rw [Nat.add_sub_cancel' hK]
  iframe Hc H

/-- `call_indirect` to a function with a specification, the stack the
arguments `args` and the index `idx`; the credits any `K` covering the call,
the activation and the callee's cost. -/
theorem mwpi_call_indirect' {ty t ta : Nat} {idx : UInt32} {a : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {P : List Value → IProp GF} {Kf : List Value → Nat}
    {Q : List Value → List Value → IProp GF} (args : List Value) :
    MFunSpec cfg lim (d + 1) type inst mi code Cg P Kf Q ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗
      ⌜vs = args ++ [.i32 idx] ∧ f.mi.tableAddrs[t]? = some ta ∧ type = f.mi.types[ty]! ∧
        args.length = type.params.length ∧ d + 1 < lim.maxCallDepth⌝ ∗
      credits Cg K ∗
      ⌜cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) + Kf args ≤ K⌝ ∗
      P args ∗
      ▷ (∀ rs, ta ↦[wt][ idx.toNat ] Ref.func a -∗
          credits Cg (K - (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
            Kf args)) -∗ Q args rs -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f vs [.call_indirect ty t] Φ := by
  iintro ⟨Hs, Hf, Hi, Ht, %⟨hvs, hta, hty, hlen, hd⟩, Hc, %hK, HP, H⟩
  subst hvs
  iapply mwpi_call_indirect_spec_args (R := K - (cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals code args) + Kf args)) ty t ta idx a type inst mi
    code args P Kf Q hta hty hlen hd
  have e : cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
      (Kf args + (K - (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        Kf args))) = K := by omega
  rw [e]
  iframe Hc Ht Hf Hi Hs HP
  iexact H

end Flex

section Specs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `Key::get` (468), the state 1 -/

def keyPre (n : Nat) (key init : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 key, .i32 init]⌝ ∗ n ↦[i32][ key.toNat ] 1)

def keyPost (n : Nat) (key : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 (key + 4)]⌝ ∗ n ↦[i32][ key.toNat ] 1)

/-- `Key::get(key, init)` (468) on an initialised key: `key + 4`. -/
theorem f468_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (key init : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f468 Cg (keyPre n key init)
      (fun _ => 8 * cfg.regularOpCost) (keyPost n key) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold keyPre at HP
  icases HP with ⟨%hargs, Hs⟩
  subst hargs
  simp only [f468]
  mstep
  mstep; mstep [Hs]; mstep; mstep
  mstep
  mstep; mstep; mstep
  iframe Hc
  iunfold keyPost
  iframe Hs
  ipureintro; simp [htype]

/-! ## `__getit` (565), the key initialised -/

def getItPre (n : Nat) (args : List Value) : IProp GF :=
  iprop(⌜args = []⌝ ∗ n ↦[i32][ 1074900 ] 1)

def getItPost (n : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 1074904]⌝ ∗ n ↦[i32][ 1074900 ] 1)

/-- `BLOCKCHAIN_INTERFACE::__getit()` (565) on later accesses: the
`RefCell` at 1074904. -/
theorem f565_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n a468 : Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[468]? = some a468) (ty468 : FuncType)
    (hty1 : ty468.params.length = 2) (hty2 : ty468.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) :
    a468 ↪[wf] FuncInst.wasm ty468 inst f468 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f565 Cg (getItPre n)
        (fun _ => 20 * cfg.regularOpCost) (getItPost n) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold getItPre at HP
  icases HP with ⟨%hargs, Hs⟩
  subst hargs
  simp only [f565]
  mstep; mstep
  mcall (f468_spec cfg lim (d + 1) ty468 hty2 inst mi n hn Cg 1074900 106) using [Hs]
  · iunfold keyPre
    simp only [UInt32.reduceToNat]
    iframe Hs
  iunfold keyPost at HQ
  simp only [UInt32.reduceToNat, UInt32.reduceAdd]
  icases HQ with ⟨%hrs, Hs⟩
  subst hrs
  mpay with simp [htype]
  iframe Hc
  iunfold getItPost
  iframe Hs
  ipureintro; simp [htype]

/-! ## `BorrowRef::new` (494), the flag 0 -/

def newPre (n : Nat) (p : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p]⌝ ∗ n ↦[i32][ p.toNat ] 0)

/-- The flag 1 (one shared borrow), `Some(p)` returned. -/
def newPost (n : Nat) (p : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 p]⌝ ∗ n ↦[i32][ p.toNat ] 1)

/-- `BorrowRef::new(flag)` (494) on a free flag. -/
theorem f494_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n a672 : Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[672]? = some a672) (ty672 : FuncType)
    (hty1 : ty672.params.length = 2) (hty2 : ty672.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (p : UInt32) :
    a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f494 Cg (newPre n p)
        (fun _ => 30 * cfg.regularOpCost) (newPost n p) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold newPre at HP
  icases HP with ⟨%hargs, Hp⟩
  subst hargs
  simp only [f494]
  mstep
  mstep; mstep [Hp]; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep; mstep
  mcall (BorrowMut.f672_spec cfg lim (d + 1) ty672 hty2 inst mi n hn Cg p 1 0) using [Hp]
  · iunfold BorrowMut.replacePre
    iframe Hp
    ipureintro; rfl
  iunfold BorrowMut.replacePost at HQ
  icases HQ with ⟨%hrs, Hp⟩
  subst hrs
  mstep; mstep
  iframe Hc
  iunfold newPost
  iframe Hp
  ipureintro; simp [htype]

/-! ## `RefCell::borrow` (429), the cell free -/

/-- The stack pointer, the cell's flag (free) and the two words at `out`. -/
def borrowPre (n g : Nat) (gi : GlobalInst) (out cell loc o0 o4 : UInt32) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 cell, .i32 loc]⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ cell.toNat ] 0 ∗
    n ↦[i32][ out.toNat ] o0 ∗ n ↦[i32][ out.toNat + 4 ] o4)

/-- The flag 1; the `Ref` (the value at `cell + 4`, the flag `cell`) at `out`. -/
def borrowPost (n g : Nat) (gi : GlobalInst) (out cell : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ cell.toNat ] 1 ∗
    n ↦[i32][ out.toNat ] (cell + 4) ∗ n ↦[i32][ out.toNat + 4 ] cell)

/-- `RefCell::borrow(out, cell, loc)` (429) on a free cell. -/
theorem f429_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a494 a672 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha494 : mi.funcAddrs[494]? = some a494) (ha672 : mi.funcAddrs[672]? = some a672)
    (ty494 ty672 : FuncType) (hty494a : ty494.params.length = 1)
    (hty494b : ty494.results.length = 1) (hty672a : ty672.params.length = 2)
    (hty672b : ty672.results.length = 1) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp)
    (out cell loc o0 o4 : UInt32) (hcell : cell ≠ 0) :
    a494 ↪[wf] FuncInst.wasm ty494 inst f494 ∗ a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f429 Cg (borrowPre n g gi out cell loc o0 o4)
        (fun _ => 60 * cfg.regularOpCost) (borrowPost n g gi out cell) := by
  iintro ⟨#Hf494, #Hf672, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold borrowPre at HP
  icases HP with ⟨%hargs, Hg, Hf, Ho0, Ho4⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  simp only [f429]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mstep
  mcall (f494_spec cfg lim (d + 1) ty494 hty494b inst mi n a672 hn ha672 ty672 hty672a hty672b
    (by omega) Cg cell) using [Hf]
  · iunfold newPre
    iframe Hf
    ipureintro; rfl
  iunfold newPost at HQ
  icases HQ with ⟨%hrs, Hf⟩
  subst hrs
  mstep
  mstep_taken
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  iframe Hc
  iunfold borrowPost
  iframe Hg Hf Ho0 Ho4
  ipureintro; rfl

/-! ## `Option::expect` (430) on a `Some` -/

def expectSomePre (a loc : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 a, .i32 loc]⌝)

def expectSomePost (a : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 a]⌝)

/-- `Option::expect(p, loc)` (430) on a `Some` (`p` not null). -/
theorem f430_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (a loc : UInt32)
    (ha : a ≠ 0) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f430 Cg (expectSomePre a loc)
      (fun _ => 3 * cfg.regularOpCost) (expectSomePost a) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold expectSomePre at HP
  icases HP with %hargs
  subst hargs
  simp only [f430]
  mstep
  mstep
  mstep_taken
  mstep
  iframe Hc
  iunfold expectSomePost
  ipureintro; simp [htype]

/-! ## `drop_in_place<BorrowRef>` (431) -/

/-- The guard at `p` points to the flag `q`, holding `fl`. -/
def dropPre (n : Nat) (p q fl : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p]⌝ ∗ n ↦[i32][ p.toNat ] q ∗ n ↦[i32][ q.toNat ] fl)

/-- The flag decremented. -/
def dropPost (n : Nat) (p q fl : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ p.toNat ] q ∗ n ↦[i32][ q.toNat ] (fl + 4294967295))

/-- `drop_in_place<BorrowRef>(p)` (431): the flag decremented. -/
theorem f431_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n a672 : Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[672]? = some a672) (ty672 : FuncType)
    (hty1 : ty672.params.length = 2) (hty2 : ty672.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (p q fl : UInt32) :
    a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f431 Cg (dropPre n p q fl)
        (fun _ => 26 * cfg.regularOpCost) (dropPost n p q fl) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold dropPre at HP
  icases HP with ⟨%hargs, Hp, Hq⟩
  subst hargs
  simp only [f431]
  mstep; mstep [Hp]; mstep; mstep; mstep [Hq]; mstep; mstep
  mcall (BorrowMut.f672_spec cfg lim (d + 1) ty672 hty2 inst mi n hn Cg q (fl + 4294967295) fl)
    using [Hq]
  · iunfold BorrowMut.replacePre
    iframe Hq
    ipureintro; rfl
  iunfold BorrowMut.replacePost at HQ
  icases HQ with ⟨%hrs, Hq⟩
  subst hrs
  mstep
  iframe Hc
  iunfold dropPost
  iframe Hp Hq
  ipureintro; rfl

/-! ## `Result::expect` (432) on an `Ok` -/

def resultPre (g : Nat) (gi : GlobalInst) (b : UInt64) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i64 0, .i64 b]⌝ ∗ g ↦[wg] gi)

def resultPost (g : Nat) (gi : GlobalInst) (b : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 b]⌝ ∗ g ↦[wg] gi)

/-- `Result<u64, AccessError>::expect(tag, value)` (432) on an `Ok` (the tag
0): the value. -/
theorem f432_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (g : Nat)
    (hg : mi.globalAddrs[0]? = some g) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (b : UInt64) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f432 Cg (resultPre g gi b)
      (fun _ => 14 * cfg.regularOpCost) (resultPost g gi b) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold resultPre at HP
  icases HP with ⟨%hargs, Hg⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  simp only [f432]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mstep; mstep; mstep
  mstep_taken
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  mstep
  iframe Hc
  iunfold resultPost
  iframe Hg
  ipureintro; simp [htype]

end Specs

end WNear.Binary.Borrow
