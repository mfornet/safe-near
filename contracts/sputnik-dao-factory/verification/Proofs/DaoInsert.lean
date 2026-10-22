import Proofs.DaoProjection
import Proofs.Callbacks
import Proofs.MetadataGeneralInsert

namespace SputnikFactory

def daoAppendBodyRaw (raw : Raw) (order : List Account)
    (account : Account) : Raw :=
  write
    (write raw (daoIndexKey account) (leBytes 8 order.length))
    (daoElementKey order.length) (borshString account)

def daoAppendRaw (raw : Raw) (order : List Account)
    (account : Account) : Raw :=
  write (daoAppendBodyRaw raw order account) stateKey
    (Borsh.encodeSet (Spec.daoHeader (order ++ [account])))

theorem set_insert_absent_general (header : SetHeader) (raw : Raw)
    (account : Account)
    (habsent : read raw (setIndexKey header account) = none)
    (hroom : header.elements.length + 1 < u64Bound) :
    (setInsert header account).run raw =
      .ok ({ header with elements :=
          { header.elements with length := header.elements.length + 1 } },
        write
          (write raw (setIndexKey header account)
            (leBytes 8 header.elements.length))
          (vectorKey header.elements header.elements.length)
          (borshString account)) := by
  simp [setInsert, setContains, habsent, vectorPush, hroom,
    load, save, require, Bind.bind, Pure.pure, Tx.bind, Tx.run]

theorem canonical_set_insert_absent (raw : Raw) (order : List Account)
    (account : Account)
    (habsent : read raw (daoIndexKey account) = none)
    (hroom : order.length + 1 < u64Bound) :
    (setInsert (Spec.daoHeader order) account).run raw =
      .ok (Spec.daoHeader (order ++ [account]),
        daoAppendBodyRaw raw order account) := by
  have hkey : setIndexKey (Spec.daoHeader order) account =
      daoIndexKey account := by rfl
  have hs := set_insert_absent_general (Spec.daoHeader order) raw account
    (by simpa [hkey] using habsent)
    (by simpa [Spec.daoHeader] using hroom)
  simpa [daoAppendBodyRaw, Spec.daoHeader, daoIndexKey,
    setIndexKey, vectorKey, daoElementKey, initialSet] using hs

/-- A successful private callback appends an absent DAO exactly once and
commits the incremented vector length to STATE. The callback's `true` return
does not itself establish any property of the preceding account-creation
receipt; its success result is an explicit environment premise. -/
theorem successful_creation_appends_dao (cfg : Config) (raw : Raw)
    (env : Env) (order : List Account) (account predecessor : Account)
    (amount : Nat) (bytes : Bytes)
    (layout : Spec.DaoLayout raw order)
    (hroom : order.length + 1 < u64Bound)
    (habsent : read raw (daoIndexKey account) = none)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes]) :
    step cfg raw env (.onCreate account amount predecessor) =
      .ok ⟨daoAppendRaw raw order account, [], .boolean true⟩ := by
  have hlen : order.length < 256 ^ 8 := by
    simp [u64Bound] at hroom
    omega
  have hinsertion := canonical_set_insert_absent raw order account habsent hroom
  have hentry := successful_creation_entry_registers cfg
    (Spec.daoHeader order) (Spec.daoHeader (order ++ [account]))
    raw (daoAppendBodyRaw raw order account) env account predecessor amount bytes
    layout.state (by simp [Spec.daoHeader, initialSet])
    (by simpa [Spec.daoHeader] using hlen)
    (by simp [Spec.daoHeader, initialSet]) hauth hdeposit hresults hinsertion
  simpa [daoAppendRaw] using hentry

theorem borsh_string_injective (left right : Account)
    (heq : borshString left = borshString right) : left = right := by
  have hbytes : left.toUTF8.data.toList = right.toUTF8.data.toList := by
    have hdrop := congrArg (List.drop 4) heq
    simpa [borshString, borshBytes, List.drop_append, leBytes_length]
      using hdrop
  have hl := string_utf8_roundtrip left
  have hr := string_utf8_roundtrip right
  rw [hbytes] at hl
  rw [hl] at hr
  exact Option.some.inj hr

theorem dao_index_key_injective (left right : Account)
    (heq : daoIndexKey left = daoIndexKey right) : left = right := by
  have hbytes : borshString left = borshString right := by
    simpa [daoIndexKey] using List.append_cancel_left heq
  exact borsh_string_injective left right hbytes

theorem find_account_append_other (order : List Account)
    (account query : Account) (hne : account ≠ query) :
    Spec.findAccount (order ++ [account]) query =
      Spec.findAccount order query := by
  induction order with
  | nil =>
    simp [Spec.findAccount, hne]
  | cons head tail ih =>
    simp only [List.cons_append, Spec.findAccount]
    rw [ih]

theorem find_account_append_new (order : List Account)
    (account : Account) (habsent : Spec.findAccount order account = none) :
    Spec.findAccount (order ++ [account]) account = some order.length := by
  induction order with
  | nil => simp [Spec.findAccount]
  | cons head tail ih =>
    have hhead : head ≠ account := by
      intro he
      subst account
      simp [Spec.findAccount] at habsent
    have htail : Spec.findAccount tail account = none := by
      simpa [Spec.findAccount, hhead] using habsent
    simp [Spec.findAccount, hhead, ih htail]

theorem find_account_none_not_mem (order : List Account)
    (account : Account) (habsent : Spec.findAccount order account = none) :
    account ∉ order := by
  induction order with
  | nil => simp
  | cons head tail ih =>
    have hhead : head ≠ account := by
      intro he
      subst account
      simp [Spec.findAccount] at habsent
    have htail : Spec.findAccount tail account = none := by
      simpa [Spec.findAccount, hhead] using habsent
    simp [Ne.symm hhead, ih htail]

theorem dao_append_preserves_layout (raw : Raw) (order : List Account)
    (account : Account) (layout : Spec.DaoLayout raw order)
    (habsent : read raw (daoIndexKey account) = none)
    (hbound : order.length < 256 ^ 8) :
    Spec.DaoLayout (daoAppendRaw raw order account) (order ++ [account]) := by
  have hfindAbsent : Spec.findAccount order account = none := by
    have hread := layout.index account
    rw [habsent] at hread
    cases hfind : Spec.findAccount order account <;> simp [hfind] at hread ⊢
  have hnotmem := find_account_none_not_mem order account hfindAbsent
  constructor
  · apply List.nodup_append.mpr
    constructor
    · exact layout.unique
    constructor
    · simp
    · intro old hold new hnew
      simp at hnew
      subst new
      intro he
      exact hnotmem (he ▸ hold)
  · exact read_write_self _ _ _
  · intro query
    have hstate : daoIndexKey query ≠ stateKey := by
      intro he
      have hlen := congrArg List.length he
      simp [dao_index_key_length, stateKey] at hlen
      omega
    have helement : daoIndexKey query ≠ daoElementKey order.length :=
      dao_index_ne_element query order.length
    unfold daoAppendRaw daoAppendBodyRaw
    rw [read_write_other _ _ _ _ hstate]
    rw [read_write_other _ _ _ _ helement]
    by_cases he : query = account
    · subst query
      rw [read_write_self]
      simp [find_account_append_new order account hfindAbsent]
    · have hnotIndex : daoIndexKey query ≠ daoIndexKey account := by
        intro heq
        exact he (dao_index_key_injective query account heq)
      rw [read_write_other _ _ _ _ hnotIndex]
      rw [find_account_append_other order account query (Ne.symm he)]
      exact layout.index query
  · intro index hindex
    have hi : index < order.length + 1 := by simpa using hindex
    have hstate : daoElementKey index ≠ stateKey := by
      intro he
      have hlen := congrArg List.length he
      simp [dao_element_key_length, stateKey] at hlen
    unfold daoAppendRaw daoAppendBodyRaw
    rw [read_write_other _ _ _ _ hstate]
    by_cases he : index = order.length
    · subst index
      rw [read_write_self]
      simp
    · have hiOld : index < order.length := by omega
      have hnotElement : daoElementKey index ≠
          daoElementKey order.length := by
        intro heq
        have hiBound : index < 256 ^ 8 := Nat.lt_trans hiOld hbound
        have heqIndex := vector_key_injective_bounded initialSet.elements
          index order.length hiBound hbound
          (by simpa [daoElementKey, vectorKey, initialSet] using heq)
        exact he heqIndex
      have hnotIndex : daoElementKey index ≠ daoIndexKey account :=
        (dao_index_ne_element account index).symm
      rw [read_write_other _ _ _ _ hnotElement]
      rw [read_write_other _ _ _ _ hnotIndex]
      rw [List.getElem?_append_left hiOld]
      exact layout.element index hiOld

theorem successful_creation_preserves_dao_layout (cfg : Config)
    (raw : Raw) (env : Env) (order : List Account)
    (account predecessor : Account) (amount : Nat) (bytes : Bytes)
    (layout : Spec.DaoLayout raw order)
    (hroom : order.length + 1 < u64Bound)
    (habsent : read raw (daoIndexKey account) = none)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes])
    (out : Outcome)
    (hstep : step cfg raw env (.onCreate account amount predecessor) = .ok out) :
    Spec.DaoLayout out.raw (order ++ [account]) := by
  rw [successful_creation_appends_dao cfg raw env order account predecessor
    amount bytes layout hroom habsent hauth hdeposit hresults] at hstep
  cases hstep
  have hbound : order.length < 256 ^ 8 := by
    simp [u64Bound] at hroom
    omega
  exact dao_append_preserves_layout raw order account layout habsent hbound

theorem successful_creation_dao_list_readback (cfg : Config)
    (raw : Raw) (env : Env) (order : List Account)
    (account predecessor : Account) (amount : Nat) (bytes : Bytes)
    (layout : Spec.DaoLayout raw order)
    (hroom : order.length + 1 < u64Bound)
    (habsent : read raw (daoIndexKey account) = none)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes])
    (hbounded : ∀ existing ∈ order,
      existing.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount existing = true)
    (hnew : account.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount account = true)
    (out : Outcome)
    (hstep : step cfg raw env (.onCreate account amount predecessor) = .ok out) :
    step cfg out.raw env .daoList =
      .ok ⟨out.raw, [], .accounts (order ++ [account])⟩ := by
  have hpost := successful_creation_preserves_dao_layout cfg raw env order
    account predecessor amount bytes layout hroom habsent hauth hdeposit
    hresults out hstep
  have hpostLength : (order ++ [account]).length < 256 ^ 8 := by
    simp [u64Bound] at hroom
    simp
    omega
  have hpostBounded : ∀ existing ∈ order ++ [account],
      existing.toUTF8.data.toList.length < 256 ^ 4 ∧
      validAccount existing = true := by
    intro existing hmem
    rcases List.mem_append.mp hmem with hold | htail
    · exact hbounded existing hold
    · have he : existing = account := by simpa using htail
      subst existing
      exact hnew
  exact dao_list_matches_layout cfg out.raw env (order ++ [account])
    (dao_layout_to_vector out.raw (order ++ [account]) hpost)
    hpostLength hpostBounded

theorem set_insert_present_general (header : SetHeader) (raw : Raw)
    (account : Account) (indexBytes : Bytes)
    (hpresent : read raw (setIndexKey header account) = some indexBytes) :
    (setInsert header account).run raw = .ok (header, raw) := by
  simp [setInsert, setContains, hpresent, load,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- A successful callback is also `true` when the DAO membership key already
exists. In this branch it commits the same header and emits no refund, but does
not append another vector entry. -/
theorem successful_creation_existing_dao (cfg : Config) (raw : Raw)
    (env : Env) (order : List Account) (account predecessor : Account)
    (amount : Nat) (bytes indexBytes : Bytes)
    (layout : Spec.DaoLayout raw order)
    (hbound : order.length < 256 ^ 8)
    (hpresent : read raw (daoIndexKey account) = some indexBytes)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes]) :
    step cfg raw env (.onCreate account amount predecessor) =
      .ok ⟨write raw stateKey (Borsh.encodeSet (Spec.daoHeader order)),
        [], .boolean true⟩ := by
  have hinsertion : (setInsert (Spec.daoHeader order) account).run raw =
      .ok (Spec.daoHeader order, raw) := by
    apply set_insert_present_general
    simpa [Spec.daoHeader, setIndexKey, daoIndexKey, initialSet] using hpresent
  exact successful_creation_entry_registers cfg (Spec.daoHeader order)
    (Spec.daoHeader order) raw raw env account predecessor amount bytes
    layout.state (by simp [Spec.daoHeader, initialSet])
    (by simpa [Spec.daoHeader] using hbound)
    (by simp [Spec.daoHeader, initialSet]) hauth hdeposit hresults hinsertion

theorem dao_header_resave_preserves_layout (raw : Raw) (order : List Account)
    (layout : Spec.DaoLayout raw order) :
    Spec.DaoLayout
      (write raw stateKey (Borsh.encodeSet (Spec.daoHeader order))) order := by
  constructor
  · exact layout.unique
  · exact read_write_self _ _ _
  · intro query
    have hkey : daoIndexKey query ≠ stateKey := by
      intro he
      have hlen := congrArg List.length he
      simp [dao_index_key_length, stateKey] at hlen
      omega
    rw [read_write_other _ _ _ _ hkey]
    exact layout.index query
  · intro index hi
    have hkey : daoElementKey index ≠ stateKey := by
      intro he
      have hlen := congrArg List.length he
      simp [dao_element_key_length, stateKey] at hlen
    rw [read_write_other _ _ _ _ hkey]
    exact layout.element index hi

theorem successful_creation_existing_preserves_layout (cfg : Config)
    (raw : Raw) (env : Env) (order : List Account)
    (account predecessor : Account) (amount : Nat)
    (bytes indexBytes : Bytes) (layout : Spec.DaoLayout raw order)
    (hbound : order.length < 256 ^ 8)
    (hpresent : read raw (daoIndexKey account) = some indexBytes)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes])
    (out : Outcome)
    (hstep : step cfg raw env (.onCreate account amount predecessor) = .ok out) :
    Spec.DaoLayout out.raw order := by
  rw [successful_creation_existing_dao cfg raw env order account predecessor
    amount bytes indexBytes layout hbound hpresent hauth hdeposit hresults] at hstep
  cases hstep
  exact dao_header_resave_preserves_layout raw order layout

end SputnikFactory
