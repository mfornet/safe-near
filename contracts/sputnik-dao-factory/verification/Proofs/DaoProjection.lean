import Proofs.StorageProjection

namespace SputnikFactory

theorem dao_layout_to_vector (raw : Raw) (order : List Account)
    (layout : Spec.DaoLayout raw order) : Spec.DaoVectorLayout raw order :=
  ⟨layout.state, layout.element⟩

/-- The source-model account decoder accepts a canonical Borsh string only
when its length fits u32 and the account syntax validator accepts it. -/
theorem exact_account_encode (account : Account)
    (hbytes : account.toUTF8.data.toList.length < 256 ^ 4)
    (hvalid : validAccount account = true) :
    Borsh.account (borshString account) = some account := by
  have htext := text_encode account [] hbytes (string_utf8_roundtrip account)
  have htext' : Borsh.text (borshString account) = some (account, []) := by
    simpa using htext
  simp [Borsh.account, Borsh.exact, htext', hvalid]

theorem dao_cons_reads (raw : Raw) (order : List Account)
    (layout : Spec.DaoVectorLayout raw order)
    (bounded : ∀ account ∈ order,
      account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true)
    (index : Nat) (account : Account) (indexes : List Nat)
    (accounts : List Account)
    (hentry : order[index]? = some account)
    (hrest : (accountsAt (Spec.daoHeader order).elements indexes).run raw =
      .ok (accounts, raw)) :
    (accountsAt (Spec.daoHeader order).elements (index :: indexes)).run raw =
      .ok (account :: accounts, raw) := by
  have hi : index < order.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hread := layout.element index hi
  simp [hentry] at hread
  have hb := bounded account (List.mem_of_getElem? hentry)
  have hdecode := exact_account_encode account hb.1 hb.2
  have hget : (vectorGet (Spec.daoHeader order).elements index).run raw =
      .ok (some (borshString account), raw) := by
    apply vector_get_present
    · simpa [Spec.daoHeader] using hi
    · simpa [Spec.daoHeader, vectorKey, daoElementKey, initialSet] using hread
  simp [accountsAt, hget, hdecode, hrest, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem dao_indices_project (raw : Raw) (order : List Account)
    (layout : Spec.DaoVectorLayout raw order)
    (bounded : ∀ account ∈ order,
      account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true)
    (indexes : List Nat) (accounts : List Account)
    (hselect : Spec.selectAccounts order indexes = some accounts) :
    (accountsAt (Spec.daoHeader order).elements indexes).run raw =
      .ok (accounts, raw) := by
  induction indexes generalizing accounts with
  | nil =>
    simp [Spec.selectAccounts] at hselect
    subst accounts
    rfl
  | cons index indexes ih =>
    cases hentry : order[index]? with
    | none =>
      simp [Spec.selectAccounts, hentry] at hselect
    | some account =>
      cases htail : Spec.selectAccounts order indexes with
      | none =>
        simp [Spec.selectAccounts, hentry, htail] at hselect
      | some rest =>
        simp [Spec.selectAccounts, hentry, htail] at hselect
        subst accounts
        exact dao_cons_reads raw order layout bounded index account indexes
          rest hentry (ih rest htail)

theorem select_accounts_cons_succ (head : Account) (tail : List Account)
    (indexes : List Nat) :
    Spec.selectAccounts (head :: tail) (indexes.map Nat.succ) =
      Spec.selectAccounts tail indexes := by
  induction indexes with
  | nil => rfl
  | cons index indexes ih =>
    simp [Spec.selectAccounts, ih]

theorem select_accounts_complete (order : List Account) :
    Spec.selectAccounts order (List.range order.length) = some order := by
  induction order with
  | nil => rfl
  | cons head tail ih =>
    change Spec.selectAccounts (head :: tail) (List.range (tail.length + 1)) =
      some (head :: tail)
    rw [List.range_succ_eq_map]
    simp [Spec.selectAccounts, select_accounts_cons_succ, ih]

theorem select_accounts_window (order : List Account) (start count : Nat)
    (hbound : start + count ≤ order.length) :
    Spec.selectAccounts order ((List.range count).map (start + ·)) =
      some ((order.drop start).take count) := by
  induction order generalizing start count with
  | nil =>
    have hc : count = 0 := by simp at hbound; omega
    subst count
    simp [Spec.selectAccounts]
  | cons head tail ih =>
    cases start with
    | zero =>
      cases count with
      | zero => simp [Spec.selectAccounts]
      | succ count =>
        have hb : count ≤ tail.length := by simp at hbound; omega
        have htail := ih 0 count (by simpa using hb)
        have htail' : Spec.selectAccounts tail (List.range count) =
            some (tail.take count) := by simpa using htail
        change Spec.selectAccounts (head :: tail)
          ((List.range (count + 1)).map (0 + ·)) =
          some ((head :: tail).take (count + 1))
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, Nat.zero_add, Spec.selectAccounts,
          List.take_succ_cons]
        have hmap : List.map (fun x => x)
            (List.map Nat.succ (List.range count)) =
            List.map Nat.succ (List.range count) := by simp
        rw [hmap]
        simp [select_accounts_cons_succ, htail']
    | succ start =>
      have hb : start + count ≤ tail.length := by simp at hbound; omega
      have htail := ih start count hb
      have hindexes :
          (List.range count).map (start + 1 + ·) =
            ((List.range count).map (start + ·)).map Nat.succ := by
        simp [List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
      rw [hindexes, select_accounts_cons_succ]
      simpa using htail

theorem select_accounts_page (order : List Account)
    (fromIndex limit : Nat) :
    Spec.selectAccounts order
      ((List.range (min (fromIndex + limit) order.length - fromIndex)).map
        (fromIndex + ·)) =
      some ((order.drop fromIndex).take
        (min (fromIndex + limit) order.length - fromIndex)) := by
  by_cases hstart : fromIndex ≤ order.length
  · apply select_accounts_window
    omega
  · have hupper : min (fromIndex + limit) order.length = order.length := by
      omega
    have hzero : order.length - fromIndex = 0 := by omega
    simp [hupper, hzero, Spec.selectAccounts]

theorem dao_vector_projects_order (raw : Raw) (order : List Account)
    (layout : Spec.DaoVectorLayout raw order)
    (bounded : ∀ account ∈ order,
      account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true) :
    (accountsAt (Spec.daoHeader order).elements
      (List.range order.length)).run raw = .ok (order, raw) := by
  exact dao_indices_project raw order layout bounded _ _
    (select_accounts_complete order)

/-- The DAO getter reports the physical vector order. Coherent layout makes
that order unique, but raw index/code aliasing can break the layout later. -/
theorem dao_list_matches_layout (cfg : Config) (raw : Raw) (env : Env)
    (order : List Account) (layout : Spec.DaoVectorLayout raw order)
    (hbound : order.length < 256 ^ 8)
    (bounded : ∀ account ∈ order,
      account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true) :
    step cfg raw env .daoList = .ok ⟨raw, [], .accounts order⟩ := by
  have hdecode : Borsh.exact Borsh.setHeader
      (Borsh.encodeSet (Spec.daoHeader order)) =
      some (Spec.daoHeader order) := by
    apply exact_set_encode
    · simp [Spec.daoHeader, initialSet]
    · simpa [Spec.daoHeader] using hbound
    · simp [Spec.daoHeader, initialSet]
  have hproject := dao_vector_projects_order raw order layout bounded
  simp [Spec.daoHeader] at hdecode hproject
  simp [step, entry, loadFactory, layout.state, hdecode, body, done,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, Spec.daoHeader, require, expect, load, Bind.bind, Pure.pure,
    Tx.run_bind, hproject, Tx.bind, Tx.run, Except.bind]

/-- Pagination rejects u64 addition overflow before reading the DAO vector. -/
theorem dao_page_overflow (cfg : Config) (raw : Raw) (env : Env)
    (header : SetHeader) (fromIndex limit : Nat)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (hoverflow : ¬ fromIndex + limit < u64Bound) :
    step cfg raw env (.daos fromIndex limit) = .error .overflow := by
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, hstate, hdecode, body, hoverflow,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, load, Bind.bind, Pure.pure,
    Tx.bind, Tx.run]

/-- For in-range arguments, the exported page getter projects exactly the
specified contiguous vector indexes. `selectAccounts` is kept explicit so
there is no hidden assumption that an arbitrary corrupted vector decodes. -/
theorem dao_page_matches_selection (cfg : Config) (raw : Raw) (env : Env)
    (order : List Account) (layout : Spec.DaoVectorLayout raw order)
    (hbound : order.length < 256 ^ 8)
    (bounded : ∀ account ∈ order,
      account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true)
    (fromIndex limit : Nat) (accounts : List Account)
    (hadd : fromIndex + limit < u64Bound)
    (hselect : Spec.selectAccounts order
      ((List.range (min (fromIndex + limit) order.length - fromIndex)).map
        (fromIndex + ·)) = some accounts) :
    step cfg raw env (.daos fromIndex limit) =
      .ok ⟨raw, [], .accounts accounts⟩ := by
  have hdecode : Borsh.exact Borsh.setHeader
      (Borsh.encodeSet (Spec.daoHeader order)) =
      some (Spec.daoHeader order) := by
    apply exact_set_encode
    · simp [Spec.daoHeader, initialSet]
    · simpa [Spec.daoHeader] using hbound
    · simp [Spec.daoHeader, initialSet]
  have hproject := dao_indices_project raw order layout bounded _ _ hselect
  simp [Spec.daoHeader] at hdecode hproject
  simp [step, entry, loadFactory, layout.state, hdecode, body, hadd,
    Spec.daoHeader, done, Call.private, Call.rejectDeposit, Call.isNew,
    Call.ownerOnly, Call.saveHeader, require, expect, load,
    Bind.bind, Pure.pure, Tx.run_bind, hproject, Tx.bind, Tx.run, Except.bind]

/-- Successful pagination returns the contiguous physical slice and an
out-of-range starting index yields an empty list. -/
theorem dao_page_matches_layout (cfg : Config) (raw : Raw) (env : Env)
    (order : List Account) (layout : Spec.DaoVectorLayout raw order)
    (hbound : order.length < 256 ^ 8)
    (bounded : ∀ account ∈ order,
      account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true)
    (fromIndex limit : Nat) (hadd : fromIndex + limit < u64Bound) :
    step cfg raw env (.daos fromIndex limit) =
      .ok ⟨raw, [], .accounts
        ((order.drop fromIndex).take
          (min (fromIndex + limit) order.length - fromIndex))⟩ := by
  exact dao_page_matches_selection cfg raw env order layout hbound bounded
    fromIndex limit _ hadd (select_accounts_page order fromIndex limit)

end SputnikFactory
