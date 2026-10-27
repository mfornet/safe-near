import NearVM.Interp

/-! Exact positional layout of host allocation. No host function is invoked. -/
namespace Wasm.HostEnv

/-- Allocation appends the mapped host functions and returns their consecutive
store addresses in the same order. All other store fields are preserved. -/
theorem allocate_layout (store : Store α) (env : HostEnv α) :
    (env.allocate store).1 = {store with funcs := store.funcs ++
      (env.funcs.map (fun f => FuncInst.host f.toHostFn)).toArray} ∧
    (env.allocate store).2 = (List.range' store.funcs.size env.funcs.length).map ExternVal.func := by
  suffices aux : ∀ (fs : List (NearHostFn α)) (s : Store α) (exts : List ExternVal),
      let r := fs.foldl (fun (s, exts) fn =>
        let (s, addr) := s.allocFunc (.host fn.toHostFn)
        (s, exts ++ [.func addr])) (s, exts)
      r.1 = {s with funcs := s.funcs ++ (fs.map (fun f => FuncInst.host f.toHostFn)).toArray} ∧
      r.2 = exts ++ (List.range' s.funcs.size fs.length).map ExternVal.func by
    simpa only [HostEnv.allocate, List.nil_append] using aux env.funcs store []
  intro fs s exts
  induction fs generalizing s exts with
  | nil => simp
  | cons f fs ih =>
    have hp : s.funcs.push (.host f.toHostFn) = s.funcs ++ #[.host f.toHostFn] := Array.push_eq_append
    have hc : (FuncInst.host f.toHostFn :: fs.map (fun f => FuncInst.host f.toHostFn)).toArray =
        #[FuncInst.host f.toHostFn] ++ (fs.map (fun f => FuncInst.host f.toHostFn)).toArray := List.toArray_cons _ _
    have hr : (List.range' s.funcs.size (fs.length + 1)).map ExternVal.func =
        .func s.funcs.size :: (List.range' (s.funcs.size + 1) fs.length).map ExternVal.func := by
      rw [List.range'_succ, List.map_cons]
    have hi := ih {s with funcs := s.funcs.push (.host f.toHostFn)} (exts ++ [.func s.funcs.size])
    simp only [List.foldl_cons, Store.allocFunc, List.length_cons, List.map_cons,
      hp, hc, hr, Array.size_append, Array.size_singleton,
      Array.append_assoc] at hi ⊢
    refine ⟨hi.1, ?_⟩
    rw [hi.2, List.append_assoc]
    rfl

theorem allocate_funcArray (store : Store α) (env : HostEnv α) :
    (env.allocate store).1.funcs = store.funcs ++
      (env.funcs.map (fun f => FuncInst.host f.toHostFn)).toArray :=
  congrArg Store.funcs (allocate_layout store env).1

theorem allocate_imports (store : Store α) (env : HostEnv α) :
    (env.allocate store).2 = (List.range' store.funcs.size env.funcs.length).map ExternVal.func :=
  (allocate_layout store env).2

theorem allocate_funcSize (store : Store α) (env : HostEnv α) :
    (env.allocate store).1.funcs.size = store.funcs.size + env.funcs.length := by
  rw [allocate_funcArray]
  simp

theorem allocate_modules (store : Store α) (env : HostEnv α) :
    (env.allocate store).1.modules = store.modules :=
  by
    have h := congrArg (fun s : Store α => s.modules) (allocate_layout store env).1
    exact h

/-- Counting imported function addresses needs no concrete environment list. -/
theorem importAddrs_funcSize (addresses : List Nat) :
    (Link.importAddrs (addresses.map ExternVal.func)).funcAddrs.size = addresses.length := by
  suffices aux : ∀ (i : ModuleInst),
      (addresses.foldl (fun i a => {i with funcAddrs := i.funcAddrs.push a}) i).funcAddrs.size =
        i.funcAddrs.size + addresses.length by
    simpa only [Link.importAddrs, List.foldl_map, Array.size_empty, Nat.zero_add] using aux {}
  intro i
  induction addresses generalizing i with
  | nil => simp
  | cons a xs ih =>
    simpa only [List.foldl_cons, Array.size_push, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1] using ih {i with funcAddrs := i.funcAddrs.push a}

theorem allocate_importFuncSize (store : Store α) (env : HostEnv α) :
    (Link.importAddrs (env.allocate store).2).funcAddrs.size = env.funcs.length := by
  rw [allocate_imports, importAddrs_funcSize]
  simp

end Wasm.HostEnv
