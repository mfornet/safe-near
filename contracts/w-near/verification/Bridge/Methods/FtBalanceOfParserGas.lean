import Bridge.Methods.FtBalanceOfInitialAdequacy
import Bridge.Methods.FtTotalSupplyGas
/-! Successful copied-array parser work and allocator charges. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic WNear.Binary
open SerdeRead ParseStrSuccess

theorem copied_array_partition (cfg : WasmConfig) (bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat)
    (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)))
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    wsLen bs + wsLen (bs.drop (wsLen bs + 1)) + wsLen (bs.drop (bs.length - rest.length)) +
      wsLen (bs.drop k) + ((bs.drop (j + 1)).length - rest.length) + 3 = bs.length := by
  have hok := (SerdeAccountIdEsc.strRun_of_stringBody (bs.drop (j + 1)) a.val rest hmodel).1
  have hr := (costRun_growth cfg 0 0 [] (bs.drop (j + 1)) a.val.toUTF8.toList rest bs.length hok
    (by simp only [List.length_nil, Nat.zero_add, List.length_drop]; omega)).1
  simp only [List.length_drop] at hr ⊢
  omega

theorem wsLen_quote (bs : List UInt8) (j : Nat) (hq : bs[j]? = some 0x22) : wsLen (bs.drop j) = 0 := by
  by_contra hn
  obtain ⟨b, hb, hw⟩ := wsLen_ws (bs.drop j) 0 (by omega)
  have hb' : bs[j]? = some b := by simpa using hb
  have he : b = 0x22 := Option.some.inj (hb'.symm.trans hq)
  subst b
  simp [NearInterface.Json.isWhitespace] at hw

theorem copied_array_linear_work (cfg : WasmConfig) (bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat) (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    (1300 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)) +
      wsLen (bs.drop (bs.length - rest.length)))) +
      (910 + 96 * wsLen (bs.drop j) + 470 * ((bs.drop (j + 1)).length - rest.length)) +
      (700 + 96 * wsLen (bs.drop k)) ≤ 2910 + 470 * bs.length := by
  have hp := copied_array_partition cfg bs a rest j k hlen hj hk hend hmodel
  have hz := wsLen_quote bs j hq
  omega

theorem copied_growth_count_le5 (bs : List UInt8) (a : WNear.AccountId) (q : Nat) (rest : List UInt8)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some a.val, rest))
    (hlen : bs.length < 2 ^ 24) : ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) ≤ 5 := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hshort : a.val.toUTF8.toList.length ≤ 64 := by omega
  have hok := (SerdeAccountIdEsc.strRun_of_stringBody (bs.drop q) a.val rest hmodel).1
  have hcount := appendChunks_growthCount 0 [] (bs.drop q) a.val.toUTF8.toList rest hok
    (by simp) (by decide) (by simp only [List.length_nil, Nat.zero_add, List.length_drop]; omega)
  change ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) = 0 ∨
    8 * 2 ^ (ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) - 1) ≤
      2 * a.val.toUTF8.toList.length + 8 at hcount
  rcases hcount with hz | hp
  · omega
  · by_contra! hn
    have he : 2 ^ 5 ≤ 2 ^ (ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem copied_parser_free_le12 (bs : List UInt8) (a : WNear.AccountId) (q : Nat) (rest : List UInt8)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some a.val, rest))
    (hlen : bs.length < 2 ^ 24) : copiedParserFree bs q 1 ≤ 12 := by
  have hc := copied_growth_count_le5 bs a q rest hmodel hlen
  unfold copiedParserFree
  rw [ScratchGrow.endFreeBound_eq]
  omega
theorem short_growth_budget_le17b (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (G N : Nat) (hg : G ≤ 5) (hn : N ≤ 64) : growthBudget p.wasm 1 G N ≤ 17 * 10 ^ 9 := by
  unfold growthBudget
  split
  · omega
  · have hgg : G * G ≤ 25 := (Nat.mul_le_mul hg hg).trans (by decide)
    have hcoef : 1790 * G + (1 * G + G * G - G) * 320 + 36 * N + 144 ≤ 19500 := by omega
    have hp : (4 * N + 16 + 66066 * G) / 65536 ≤ 5 := by omega
    have ht1 := Nat.mul_le_mul hcoef hc.regularOp
    have ht2 := Nat.mul_le_mul hg hc.linearBase
    have ht3 := Nat.mul_le_mul hc.linearUnit hp
    omega

open ParseStr ParseEscape NearInterface.Json

theorem unicode_consumed_le10 (l r : List UInt8) (c : Char)
    (h : unicodeEscape l = some (c, r)) : l.length - r.length ≤ 10 := by
  unfold unicodeEscape at h
  cases h4 : hex4 l with
  | none => simp [h4] at h
  | some p =>
    obtain ⟨n, r1⟩ := p
    obtain ⟨hl1, rfl⟩ := ParseEscape.hex4_some _ _ _ h4
    simp only [h4, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · rename_i r2 heq
        cases h5 : hex4 r2 with
        | none => simp [h5] at h
        | some q =>
          obtain ⟨m, r3⟩ := q
          obtain ⟨hl2, rfl⟩ := ParseEscape.hex4_some _ _ _ h5
          simp only [h5, Option.bind_some] at h
          split at h
          · split at h
            · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              have hl : (l.drop 4).length = r2.length + 2 := by rw [heq]; simp
              simp only [List.length_drop] at hl ⊢
              omega
            · simp at h
          · simp at h
      · simp at h
    · split at h
      · simp at h
      · split at h
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          simp only [List.length_drop]
          omega
        · simp at h

theorem escape_consumed_le12 (l out : List UInt8) (m : Nat)
    (he : escDecode l = some (out, m)) : m + 1 ≤ 12 * out.length := by
  cases l with
  | nil => simp [escDecode] at he
  | cons e tail =>
    simp only [escDecode] at he
    split_ifs at he <;> (try (simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp))
    cases hu : unicodeEscape tail with
    | none => simp [hu] at he
    | some p =>
      obtain ⟨c, rest⟩ := p
      rw [hu] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hm := unicode_consumed_le10 tail rest c hu
      rw [String.length_utf8EncodeChar]
      have hc := c.utf8Size_pos
      omega

theorem strRun_encoded_le12 (l acc bytes rest : List UInt8) (h : strRun l acc = .ok bytes rest) :
    l.length - rest.length ≤ 12 * (bytes.length - acc.length) + 1 := by
  have hsplit := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
  simp only [List.length_append] at hsplit
  match hd : l.dropWhile plain with
  | [] => rw [strRun_nil l acc hd] at h; cases h
  | x :: tail =>
    have hl : l.length = (l.takeWhile plain).length + 1 + tail.length := by
      rw [hd] at hsplit
      simp only [List.length_cons] at hsplit
      omega
    rw [strRun_cons l acc x tail hd] at h
    split at h
    · cases h
      simp only [List.length_append]
      omega
    · split at h
      · split at h
        · rename_i out m he
          have hc := escape_consumed_le12 tail out m he
          have hm := escDecode_len tail out m he
          have hr := strRun_encoded_le12 (tail.drop m) (acc ++ l.takeWhile plain ++ out) bytes rest h
          have ha := ParseStrRoom.strRun_acc_le (tail.drop m) (acc ++ l.takeWhile plain ++ out) bytes rest h
          simp only [List.length_append, List.length_drop] at hr ha
          omega
        · cases h
      · cases h
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega

theorem account_encoded_le769 (bs : List UInt8) (a : WNear.AccountId) (q : Nat) (rest : List UInt8)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some a.val, rest)) :
    (bs.drop q).length - rest.length ≤ 769 := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hok := (SerdeAccountIdEsc.strRun_of_stringBody (bs.drop q) a.val rest hmodel).1
  have hc := strRun_encoded_le12 (bs.drop q) [] a.val.toUTF8.toList rest hok
  simp only [List.length_nil, Nat.sub_zero] at hc
  omega

theorem copied_array_short_work (cfg : WasmConfig) (bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat) (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    (1300 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)) +
      wsLen (bs.drop (bs.length - rest.length)))) +
      (910 + 96 * wsLen (bs.drop j) + 470 * ((bs.drop (j + 1)).length - rest.length)) +
      (700 + 96 * wsLen (bs.drop k)) ≤ 300000 + 96 * bs.length := by
  have hp := copied_array_partition cfg bs a rest j k hlen hj hk hend hmodel
  have hz := wsLen_quote bs j hq
  have hc := account_encoded_le769 bs a (j + 1) rest hmodel
  omega

theorem copied_array_parser_cost_le (cfg : WasmConfig) (bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat) (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    (700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
      SerdeStruct78Esc.costArray cfg 1 0 bs a.val.toUTF8.toList rest j ≤
    (300400 + AccountIdValid.cost554 a.val.toUTF8.toList.length + 96 * bs.length) * cfg.regularOpCost +
      growthBudget cfg 1 (ScratchGrow.growthCount 0 0 (appendChunks (bs.drop (j + 1)) [])) a.val.toUTF8.toList.length +
      SerdeString.cost618 cfg (ScratchGrow.endFreeBound 1 0 0 (appendChunks (bs.drop (j + 1)) []))
        (UInt32.ofNat a.val.toUTF8.toList.length) := by
  have hw := Nat.mul_le_mul_right cfg.regularOpCost
    (copied_array_short_work cfg bs a rest j k hlen hj hq hk hend hmodel)
  simp only [SerdeStruct78Esc.costArray, SerdeDeStrEsc.costCopied]
  simp only [Nat.add_mul] at hw ⊢
  omega

theorem alloc_walk32_cost_le (cfg : WasmConfig) (F P : Nat) (size : UInt32)
    (hF : F ≤ 32) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat ≤ P) :
    AllocWalk.cost310W cfg F size 1 ≤ 11210 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * P := by
  have hf := Nat.mul_le_mul_right (320 * cfg.regularOpCost) hF
  have hpg := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
  simp only [AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc]
  omega

theorem alloc32_cost_le (cfg : WasmConfig) (F P : Nat) (size : UInt32)
    (hF : F ≤ 32) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat ≤ P) :
    VecWithCap.costAllocF cfg F size ≤ 11210 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * P := by
  unfold VecWithCap.costAllocF
  split
  · simp only [VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581]
    have hpg := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
    omega
  · exact alloc_walk32_cost_le cfg F P size hF hp

theorem owned_short_cost_le11b (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (F : Nat) (size : UInt32) (hF : F ≤ 32) (hs : size.toNat ≤ 64) :
    SerdeString.cost618 p.wasm F size ≤ 11 * 10 ^ 9 := by
  have hp := LookupMapOps.cellPages_le4096 size (hs.trans (by decide))
  have ha := alloc_walk32_cost_le p.wasm F 1 size hF (by omega)
  have hm := FtTotalSupplyMethod.memcpy_le size.toNat
  have hmc : MemCpy.cost size.toNat ≤ 1158 := by omega
  have hmu := Nat.mul_le_mul hmc hc.regularOp
  have hop := Nat.mul_le_mul_left 11210 hc.regularOp
  have hc100 := Nat.mul_le_mul_left 100 hc.regularOp
  have hc240 := Nat.mul_le_mul_left 240 hc.regularOp
  have hb := hc.linearBase
  have hu := hc.linearUnit
  simp only [SerdeString.cost618, SerdeString.costA, Nat.add_mul]
  omega

set_option maxRecDepth 20000 in
theorem copied_array_parser_cost_le300b (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (bs : List UInt8) (a : WNear.AccountId) (rest : List UInt8) (j k : Nat) (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    (700 + 96 * wsLen (bs.drop k)) * p.wasm.regularOpCost +
      SerdeStruct78Esc.costArray p.wasm 1 0 bs a.val.toUTF8.toList rest j ≤
      300 * 10 ^ 9 + (80 * 10 ^ 6) * bs.length := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hn : a.val.toUTF8.toList.length ≤ 64 := by omega
  have hp := copied_array_parser_cost_le p.wasm bs a rest j k hlen hj hq hk hend hmodel
  have hg := copied_growth_count_le5 bs a (j + 1) rest hmodel hlen
  have hgb := short_growth_budget_le17b p hc _ _ hg hn
  have hF : ScratchGrow.endFreeBound 1 0 0 (appendChunks (bs.drop (j + 1)) []) ≤ 32 := by
    rw [ScratchGrow.endFreeBound_eq]; omega
  have hsize : (UInt32.ofNat a.val.toUTF8.toList.length).toNat ≤ 64 :=
    (Nat.mod_le _ _).trans hn
  have ho := owned_short_cost_le11b p hc _ _ hF hsize
  have hval : AccountIdValid.cost554 a.val.toUTF8.toList.length ≤ 3940 := by unfold AccountIdValid.cost554; omega
  have hconst := Nat.mul_le_mul_left (300400 + AccountIdValid.cost554 a.val.toUTF8.toList.length) hc.regularOp
  have hcoef : 96 * p.wasm.regularOpCost ≤ 80 * 10 ^ 6 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hcoef
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hp hconst hlinear ⊢
  omega
end WNear.Binary.BalanceOf297AbsentCall
