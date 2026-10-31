import Bridge.Methods.FtBalanceOfPresentArray

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WNear.Binary
open NearInterface NearInterface.Json WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.BalanceOf297AbsentCall (accepted_object_model account_value_model)
set_option maxRecDepth 100000
def ArrayPresentCase (st : Option WNear.State) (ctx : Context) (c : WNear.Call) : Prop :=
  ∃ (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat),
    st = some S ∧ c = .ftBalanceOf a ∧ a ∈ S.registered ∧ ctx.args = bs ∧
    bs.length ≤ 4194304 ∧ bs[wsLen bs]? = some 0x5B ∧
    j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) ∧ bs[j]? = some 0x22 ∧
    bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D ∧
    k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1 ∧
    k + wsLen (bs.drop k) = bs.length ∧
    Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)

def FullGeneralObjectPresentCase (st : Option WNear.State) (ctx : Context) (c : WNear.Call) : Prop :=
  ∃ (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat),
    st = some S ∧ c = .ftBalanceOf a ∧ a ∈ S.registered ∧ ctx.args = bs ∧
    bs.length ≤ 4194304 ∧ bs[wsLen bs]? = some 0x7B ∧
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      SerdeIgnObject.ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest) ∧
    bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length

theorem full_general_present_case_accepted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : FullGeneralObjectPresentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st c
    ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.full_weighted_present_refines_init cfg size codeOf raw ctx S a bs rest N hreceipt hp hwf hm hl
    ho hloop hend hc hsize hargs hrep ha).2

theorem full_general_present_case_no_issue (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : FullGeneralObjectPresentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.full_weighted_present_refines_init cfg size codeOf raw ctx S a bs rest N hreceipt hp hwf hm hl
    ho hloop hend hc hsize hargs hrep ha).1

theorem accepted_array_present_case (S : WNear.State) (ctx : NearInterface.Context) (a : WNear.AccountId)
    (bs : List UInt8) (hargs : ctx.args = bs) (ha : a ∈ S.registered)
    (hlen : bs.length ≤ 4194304) (ho : bs[wsLen bs]? = some 0x5B)
    (hd : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) :
    ArrayPresentCase (some S) ctx (.ftBalanceOf a) := by
  have hdv : Agrees (valueAs WNear.account) (valueAs WNear.account) := fun _ => Or.inl rfl
  obtain ⟨r, hs, he⟩ := SerdeFromTrait.decode_struct hdv SerdeIgnObject.ignored_agrees hd
  have hskip := WNear.SerdeStructLoop.skip_drop_of (bs := bs) (x := 0) (by simpa using ho)
  simp only [List.drop_zero, Nat.zero_add] at hskip
  have hnot : ∀ r', skipWhitespace (bs.drop (wsLen bs + 1)) ≠ 0x5D :: r' := by
    intro r' hx
    rw [structDe_arrE "account_id" _ _ hskip hx] at hs
    cases hs
  rw [structDe_arrM "account_id" _ _ hskip hnot] at hs
  simp only [Option.bind_eq_some_iff] at hs
  obtain ⟨⟨a', rest⟩, hv, hend⟩ := hs
  have hvalue : valueAs WNear.account (bs.drop (wsLen bs + 1)) = some (a', rest) := by
    simpa only [valueAs, valueR_skip] using hv
  unfold arrEnd at hend
  split at hend
  · rename_i tail hclose
    simp only [Option.some.injEq, Prod.mk.injEq] at hend
    obtain ⟨rfl, rfl⟩ := hend
    have hsuffix := WNear.JsonSuffix.valueAs_suf WNear.account hvalue
    have hr := WNear.JsonSuffix.drop_suf' hsuffix
    have hclose' := hclose
    rw [← hr] at hclose'
    obtain ⟨hb, htail⟩ := WNear.SerdeStructLoop.skip_drop_cons hclose'
    obtain ⟨hq, hmodel⟩ := account_value_model hvalue
    have hws := SerdeFromTrait.wsLen_all he
    have hlast := (WNear.JsonSuffix.cons_suf hclose).trans (hsuffix.trans (List.drop_suffix _ bs))
    have hlastlen := hlast.length_le
    have hlastdrop := WNear.JsonSuffix.drop_suf hlast
    refine ⟨S, a', bs, rest, wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)),
      bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1,
      rfl, rfl, ha, hargs, by omega, ho, rfl, hq, hb, rfl, ?_, hmodel⟩
    rw [htail] at he
    have hws' := SerdeFromTrait.wsLen_all he
    simp only [List.length_drop] at hws'
    have hbl := SerdeNextKey.getElem_lt hb
    omega
  · simp at hend

theorem accepted_present_cases (cfg : WNear.Config) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a))
    (ha : a ∈ S.registered) (hlen : ctx.args.length ≤ 4194304) :
    ArrayPresentCase (some S) ctx (.ftBalanceOf a) ∨
      FullGeneralObjectPresentCase (some S) ctx (.ftBalanceOf a) := by
  have hd : WNear.Call.decode "ft_balance_of" ctx.args = some (.ftBalanceOf a) := by
    change WNear.Call.decode ctx.method ctx.args = some (.ftBalanceOf a) at hp
    rwa [hm] at hp
  by_cases ho : ctx.args[wsLen ctx.args]? = some 0x7B
  · obtain ⟨N, rest, hloop, hend⟩ := accepted_object_model ctx.args a ho hd
    exact Or.inr ⟨S, a, ctx.args, rest, N, rfl, rfl, ha, rfl, hlen, ho, hloop, hend⟩
  · by_cases harr : ctx.args[wsLen ctx.args]? = some 0x5B
    · exact Or.inl (accepted_array_present_case S ctx a ctx.args rfl ha hlen harr hd)
    · have hdv : Agrees (valueAs WNear.account) (valueAs WNear.account) := fun _ => Or.inl rfl
      obtain ⟨r, hs, _⟩ := SerdeFromTrait.decode_struct hdv SerdeIgnObject.ignored_agrees hd
      have hobj : ∀ tail, skipWhitespace ctx.args ≠ 0x7B :: tail := by
        intro tail hx
        have hb := (WNear.SerdeStructLoop.skip_drop_cons (bs := ctx.args) (x := 0) (by simpa using hx)).1
        apply ho
        simpa only [List.drop_zero, Nat.zero_add] using hb
      have harr' : ∀ tail, skipWhitespace ctx.args ≠ 0x5B :: tail := by
        intro tail hx
        have hb := (WNear.SerdeStructLoop.skip_drop_cons (bs := ctx.args) (x := 0) (by simpa using hx)).1
        apply harr
        simpa only [List.drop_zero, Nat.zero_add] using hb
      rw [structDe_other "account_id" _ _ hobj harr'] at hs
      cases hs


end WNear.Binary.BalanceOf297PresentCall


namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WNear.Binary NearInterface
set_option maxRecDepth 100000
theorem array_present_case_accepted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : ArrayPresentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st c
    ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨S, a, bs, rest, j, k, rfl, rfl, ha, hargs, hreceipt, ho, hj, hq, hclose, hk, hend, hmodel⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.full_array_present_refines_init cfg size codeOf raw ctx S a bs rest j k hreceipt hp hwf hm hl
    ho hj hq hclose hk hend hmodel hc hsize hargs hrep ha).2

theorem array_present_case_no_issue (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : ArrayPresentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  obtain ⟨S, a, bs, rest, j, k, rfl, rfl, ha, hargs, hreceipt, ho, hj, hq, hclose, hk, hend, hmodel⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.full_array_present_refines_init cfg size codeOf raw ctx S a bs rest j k hreceipt hp hwf hm hl
    ho hj hq hclose hk hend hmodel hc hsize hargs hrep ha).1


open ContractModel in
theorem initialized_present_refines (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hrep : (WNear.wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a))
    (ha : a ∈ S.registered) (hlen : ctx.args.length ≤ 4194304) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  rcases accepted_present_cases cfg ctx S a hm hp ha hlen with hcase | hcase
  · exact ⟨array_present_case_no_issue cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
      hrep hwf hctx hm hcase,
      array_present_case_accepted cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
      hrep hwf hctx hm hcase⟩
  · exact ⟨full_general_present_case_no_issue cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
      hrep hwf hctx hm hcase,
      full_general_present_case_accepted cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
      hrep hwf hctx hm hcase⟩
end WNear.Binary.BalanceOf297PresentCall


namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WNear.Binary NearInterface
set_option maxRecDepth 100000
open ContractModel in
theorem initialized_balance_refines (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hrep : (WNear.wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a))
    (hlen : ctx.args.length ≤ 4194304) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  by_cases ha : a ∈ S.registered
  · exact initialized_present_refines cfg size codeOf protocol he hsize raw ctx S a hrep hwf hctx hm hp ha hlen
  · rcases BalanceOf297AbsentCall.accepted_absent_cases cfg ctx S a hm hp ha hlen with hcase | hcase
    · exact ⟨BalanceOf297AbsentCall.array_case_no_issue cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
        hrep hwf hctx hm hcase,
        BalanceOf297AbsentCall.array_case_accepted cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
        hrep hwf hctx hm hcase⟩
    · exact ⟨BalanceOf297AbsentCall.full_general_object_case_no_issue cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
        hrep hwf hctx hm hcase,
        BalanceOf297AbsentCall.full_general_object_case_accepted cfg size codeOf protocol he hsize raw (some S) ctx (.ftBalanceOf a)
        hrep hwf hctx hm hcase⟩

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WNear.Binary NearInterface
open ContractModel in
theorem initialized_accepted_refines (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (ctx : Context) (S : WNear.State) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args c)
    (hlen : ctx.args.length ≤ 4194304) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hd : WNear.Call.decode "ft_balance_of" ctx.args = some c := by
    change WNear.Call.decode ctx.method ctx.args = some c at hp
    rwa [hm] at hp
  obtain ⟨a, rfl⟩ := FromSliceSpec.decode_shape ctx.args c hd
  exact initialized_balance_refines cfg size codeOf protocol he hsize raw ctx S a hrep hwf hctx hm hp hlen

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WNear.Binary NearInterface
open ContractModel in
theorem initialized_accepted_refines_under_limit (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (ctx : Context) (S : WNear.State) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args c)
    (hlimit : InputDomain.ArgumentLimitV86 ctx.protocol) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact initialized_accepted_refines cfg size codeOf protocol he hsize raw ctx S c hrep hwf hctx hm hp
    (InputDomain.wf_arguments_small ctx raw hwf hlimit)
end WNear.Binary.BalanceOf297PresentCall
