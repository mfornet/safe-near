import Binary.Link
import NearVM.Interp

/-!
# `contract.wasm` instantiated

`instantiate_wPrepared`: linked with its host functions, `contract.wasm`
instantiates to `wStore`: the 48 host functions, then the 907 defined
functions (each with instance 0), the function table filled by the element
segment, the memory with the data segment written at 1048576 (`wDataMem`,
never evaluated), the three globals and the instance `wInst`.

The equation is checked by the kernel alone (`kernel_rfl_all`), with the
config and the host symbolic: instantiation never looks at either beyond
the host functions' types.
-/

namespace WNear.Binary

open Wasm Wasm.Near Lean Elab Meta

/-- `kernel_rfl` for a closed goal `∀ xs, a = b`: `fun xs => Eq.refl a`,
checked by the kernel alone. -/
elab "kernel_rfl_all" : tactic => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let pf ← forallTelescope tgt fun xs body => do
    let some (ty, lhs, _) := body.eq? | throwError "kernel_rfl_all: the goal is not an equation"
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [← getLevel ty]) ty lhs)
  let name ← withOptions (Elab.async.set · false) do mkAuxLemma [] tgt pf
  goal.assign (mkConst name [])

/-- The functions the element segment puts in the table, from slot 1. -/
def wTableFuncs : List Nat :=
  [
    699, 129, 870, 593, 901, 179, 145, 877, 148, 849, 92, 641, 143, 812, 142, 944, 149, 116, 140,
    119, 137, 121, 135, 125, 138, 123, 132, 110, 134, 117, 139, 114, 133, 127, 136, 112, 150, 240,
    241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259,
    260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278,
    279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 218, 217, 141, 732, 352, 353, 351, 667, 386,
    909, 658, 355, 341, 359, 935, 360, 350, 469, 692, 564, 482, 481, 876, 480, 488, 802, 487, 489,
    950, 565, 490, 473, 475, 476, 571, 577, 578, 579, 731, 591, 619, 594, 603, 616, 612, 615, 600,
    602, 671, 680, 679, 670, 661, 682, 702, 919, 931, 943, 937, 925, 724, 748, 741, 742, 743, 808,
    740, 809, 810, 750, 759, 756, 758, 749, 789, 942, 801, 820, 791, 799, 797, 798, 784, 793, 807,
    805, 806, 788, 790, 800, 794, 825, 826, 827, 828, 785, 783, 829, 830, 787, 786, 836, 840, 837,
    839, 834, 833, 835, 880, 873, 924, 858, 850, 882, 886, 887, 851, 875, 889, 904, 905, 946, 906,
    907, 908, 945, 948, 947
  ]

/-- The function table after instantiation: slot 0 is null. -/
def wTable : TableInst :=
  { elemType := .funcref, elems := (Ref.null .funcref :: wTableFuncs.map Ref.func).toArray, max := some 215 }

/-- The data segment's bytes, built by structural recursion so that the kernel
can count them (`Array.ofFn` recurses on a well-founded measure, which the
kernel cannot unfold at this size). -/
noncomputable def dataInitK : ByteArray :=
  ⟨((List.range 26319).map fun i => wNearSource.read (159306 + i)).toArray⟩

theorem dataInit_eq : dataInit = dataInitK := by
  unfold dataInit dataInitK
  apply congrArg ByteArray.mk
  apply Array.ext
  · rw [Array.size_ofFn, List.size_toArray, List.length_map, List.length_range]
  · intro i h1 h2
    rw [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- The prepared module with `dataInitK` for its data segment. -/
noncomputable def wPreparedK : Wasm.Module :=
  { wPrepared with datas := #[{ init := dataInitK, mode := .active 0 [.i32_const 1048576] }] }

theorem wPrepared_eq : wPrepared = wPreparedK := by
  simp only [wPrepared, wPreparedK, wNearModule, datas, dataInit_eq]

/-- The memory after instantiation: the data segment written at 1048576 in
1024 empty pages. -/
noncomputable def wDataMem : Memory :=
  ((Memory.new 1024 (some 2048)).writeBytes 1048576 dataInitK).get!

/-- The exports, with their addresses. -/
def wExports : Array (String × ExternVal) :=
  #[("memory", .mem 0), ("storage_minimum_balance", .func 231), ("near_deposit", .func 234),
    ("near_withdraw", .func 235), ("new", .func 290), ("ft_transfer", .func 294),
    ("ft_transfer_call", .func 295), ("ft_total_supply", .func 296), ("ft_balance_of", .func 297),
    ("ft_resolve_transfer", .func 299), ("storage_deposit", .func 303), ("storage_withdraw", .func 304),
    ("storage_unregister", .func 305), ("storage_balance_bounds", .func 306),
    ("storage_balance_of", .func 307), ("ft_metadata", .func 309), ("__data_end", .global 1),
    ("__heap_base", .global 2)]

/-- The instance: function addresses are function indices. -/
noncomputable def wInst : ModuleInst :=
  { types, funcAddrs := (List.range 955).toArray, tableAddrs := #[0], memAddrs := #[0],
    globalAddrs := #[0, 1, 2], elemAddrs := #[0], dataAddrs := #[0], exports := wExports }

/-- The store after instantiation, from the host `h`. -/
noncomputable def wStore (cfg : RuntimeConfig) (h : NearState) : Store NearState :=
  { funcs := ((wHosts cfg).map fun fn => FuncInst.host fn.toHostFn).toArray ++
      (funcs.toList.map fun f => FuncInst.wasm types[f.type]! 0 f).toArray
    tables := #[wTable]
    mems := #[wDataMem]
    globals := #[{ type := { type := .num .i32, mutable := true }, value := .i32 1048576 },
      { type := { type := .num .i32, mutable := false }, value := .i32 1074944 },
      { type := { type := .num .i32, mutable := false }, value := .i32 1074944 }]
    elems := #[{ elems := #[] }]
    datas := #[{ bytes := .empty }]
    modules := #[wInst]
    host := h }

set_option maxRecDepth 1000000 in
theorem allocate_wHosts : ∀ (cfg : RuntimeConfig) (h : NearState),
    HostEnv.allocate (Store.empty h) { funcs := wHosts cfg } =
      ({ funcs := ((wHosts cfg).map fun fn => FuncInst.host fn.toHostFn).toArray, host := h },
        (List.range 48).map ExternVal.func) := by
  kernel_rfl_all


set_option maxRecDepth 1000000 in
theorem instantiate_core : ∀ (cfg : RuntimeConfig) (h : NearState),
    Link.instantiateModuleOf
      ({ funcs := ((wHosts cfg).map fun fn => FuncInst.host fn.toHostFn).toArray, host := h } : Store NearState)
      wPreparedK ((List.range 48).map ExternVal.func) = .ok (wStore cfg h, wInst) := by
  kernel_rfl_all

/-- **Instantiation.** The validated module, linked with its host functions,
instantiates to `wStore`. -/
theorem instantiate_wPrepared (cfg : RuntimeConfig) (h : NearState) (vm : ValidModule)
    (hvm : vm.module = wPrepared) :
    Link.instantiateModule
      ({ funcs := ((wHosts cfg).map fun fn => FuncInst.host fn.toHostFn).toArray, host := h } : Store NearState)
      vm ((List.range 48).map ExternVal.func) = .ok (wStore cfg h, wInst) := by
  unfold Link.instantiateModule
  rw [hvm, wPrepared_eq]
  exact instantiate_core cfg h

end WNear.Binary
