import Bridge.Methods.FtBalanceOfNoneArray
import Bridge.Methods.FtBalanceOfInitialized

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WNear.Binary NearInterface NearInterface.Json WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.BalanceOf297AbsentCall (account_value_model accepted_object_model)

/-- Accepted arrays supply the exact raw string model and final whitespace/EOF positions. -/
theorem accepted_none_array_model (bs : List UInt8) (a : WNear.AccountId)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hd : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) :
    ∃ rest j k, j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) ∧ bs[j]? = some 0x22 ∧
      bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D ∧
      k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1 ∧
      k + wsLen (bs.drop k) = bs.length ∧
      NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest) := by
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
    refine ⟨rest, wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)),
      bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1,
      rfl, hq, hb, rfl, ?_, hmodel⟩
    rw [htail] at he
    have hws' := SerdeFromTrait.wsLen_all he
    simp only [List.length_drop] at hws'
    have hbl := SerdeNextKey.getElem_lt hb
    omega
  · simp at hend

open NearInterface.ContractModel in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem uninitialized_accepted_refines (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw none) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args c)
    (hlen : ctx.args.length ≤ 4194304) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hd : WNear.Call.decode "ft_balance_of" ctx.args = some c := by
    change WNear.Call.decode ctx.method ctx.args = some c at hp
    rwa [hm] at hp
  obtain ⟨a, rfl⟩ := FromSliceSpec.decode_shape ctx.args c hd
  have hproto : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  by_cases ho : ctx.args[wsLen ctx.args]? = some 0x7B
  · obtain ⟨N, rest, hloop, hend⟩ := accepted_object_model ctx.args a ho hd
    exact full_object_none_refines cfg size codeOf raw ctx a ctx.args rest N hproto hwf hrep hm hl hc hsize rfl hlen ho hloop hend
  · by_cases harr : ctx.args[wsLen ctx.args]? = some 0x5B
    · obtain ⟨rest, j, k, hj, hq, he, hk, hend, hmodel⟩ := accepted_none_array_model ctx.args a harr hd
      exact full_array_none_refines cfg size codeOf raw ctx a ctx.args rest j k hlen hproto hwf hm hl
        harr hj hq he hk hend hmodel hc hsize rfl hrep
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

end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WNear.Binary NearInterface ContractModel
theorem uninitialized_accepted_refines_under_limit (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw none) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args c)
    (hlimit : InputDomain.ArgumentLimitV86 ctx.protocol) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact uninitialized_accepted_refines cfg size codeOf protocol he hsize raw ctx c hrep hwf hctx hm hp
    (InputDomain.wf_arguments_small ctx raw hwf hlimit)
end WNear.Binary.BalanceOf297NoneCall
