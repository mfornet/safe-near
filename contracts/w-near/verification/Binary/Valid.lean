import Binary.Valid.Context
import Binary.Valid.Part00
import Binary.Valid.Part01
import Binary.Valid.Part02
import Binary.Valid.Part03
import Binary.Valid.Part04
import Binary.Valid.Part05
import Binary.Valid.Part06
import Binary.Valid.Part07
import Binary.Valid.Part08
import Binary.Valid.Part09
import Binary.Valid.Part10
import Binary.Valid.Part11
import Binary.Valid.Part12
import Binary.Valid.Part13
import Binary.Valid.Part14
import Binary.Valid.Part15
import Binary.Valid.Part16
import Binary.Valid.Part17
import Binary.Valid.Part18
import Binary.Valid.Part19
import Binary.Valid.Part20
import Binary.Valid.Part21

/-!
# `contract.wasm` validates

The module nearcore prepares from `contract.wasm` under v86's memory limits
is valid: its context (`Binary.Valid.Context`) and each range of bodies
(`Binary.Valid.Part*`), checked by the kernel one range at a time.
-/

namespace WNear.Binary

open Wasm

theorem funcs_rangeOk : RangeOk funcs.toList := by
  rw [funcs, List.toList_toArray]
  exact (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append (rangeOk_append valid_0_74 valid_74_145)
    valid_145_173)
    valid_173_177)
    valid_177_181)
    valid_181_255)
    valid_255_291)
    valid_291_360)
    valid_360_389)
    valid_389_451)
    valid_451_532)
    valid_532_595)
    valid_595_666)
    valid_666_728)
    valid_728_799)
    valid_799_814)
    valid_814_815)
    valid_815_819)
    valid_819_850)
    valid_850_874)
    valid_874_906)
    valid_906_907)

theorem validate_wPrepared : ∃ vm, wPrepared.validate (Features.nearcore true) = .ok vm ∧ vm.module = wPrepared :=
  Module.validate_ok (Validate.module_ok context_wPrepared fun _ hf => rangeOk_mem funcs_rangeOk hf)

end WNear.Binary
