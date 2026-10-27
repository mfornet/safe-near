import Binary.Code.Part00
import Binary.Code.Part01
import Binary.Code.Part02
import Binary.Code.Part03
import Binary.Code.Part04
import Binary.Code.Part05
import Binary.Code.Part06
import Binary.Code.Part07
import Binary.Code.Part08
import Binary.Code.Part09
import Binary.Code.Part10
import Binary.Code.Part11
import Binary.Code.Part12
import Binary.Code.Part13
import Binary.Code.Part14
import Binary.Code.Part15
import Binary.Code.Part16
import Binary.Code.Part17
import Binary.Code.Part18
import Binary.Code.Part19
import Binary.Code.Part20
import Binary.Code.Part21

/-!
# The code section of `contract.wasm`

`codes` is the code section's entries as the decoder reads them, in order,
and `reads_codes` says that they decode one after another. `funcs` is the
defined functions, which the decoder assembles from `funcTypes` (the
function section) and `codes` (`zip_codes`). The 22 `Binary.Code.Part*`
files prove each fact for consecutive ranges of entries.
-/

namespace WNear.Binary

open Wasm Binary Parser

/-- The code section's entries: byte size, locals and body of each defined
function. -/
noncomputable def codes : List (Nat × List ValType × Wasm.Expr) :=
    (((((((((((((((((((((codes_0_74) ++ codes_74_145) ++ codes_145_173) ++ codes_173_177) ++
    codes_177_181) ++ codes_181_255) ++ codes_255_291) ++ codes_291_360) ++ codes_360_389) ++
    codes_389_451) ++ codes_451_532) ++ codes_532_595) ++ codes_595_666) ++ codes_666_728) ++
    codes_728_799) ++ codes_799_814) ++ codes_814_815) ++ codes_815_819) ++ codes_819_850) ++
    codes_850_874) ++ codes_874_906) ++ codes_906_907

/-- The type of each defined function, as the function section gives it. -/
def funcTypesList : List Nat :=
    (((((((((((((((((((((funcTypes_0_74) ++ funcTypes_74_145) ++ funcTypes_145_173) ++
    funcTypes_173_177) ++ funcTypes_177_181) ++ funcTypes_181_255) ++ funcTypes_255_291) ++
    funcTypes_291_360) ++ funcTypes_360_389) ++ funcTypes_389_451) ++ funcTypes_451_532) ++
    funcTypes_532_595) ++ funcTypes_595_666) ++ funcTypes_666_728) ++ funcTypes_728_799) ++
    funcTypes_799_814) ++ funcTypes_814_815) ++ funcTypes_815_819) ++ funcTypes_819_850) ++
    funcTypes_850_874) ++ funcTypes_874_906) ++ funcTypes_906_907

/-- The defined functions of `contract.wasm`, as decoded (function indices
48 to 954; the 48 imported functions come first). -/
noncomputable def funcs : Array Func :=
    ((((((((((((((((((((((funcs_0_74) ++ funcs_74_145) ++ funcs_145_173) ++ funcs_173_177) ++
    funcs_177_181) ++ funcs_181_255) ++ funcs_255_291) ++ funcs_291_360) ++ funcs_360_389) ++
    funcs_389_451) ++ funcs_451_532) ++ funcs_532_595) ++ funcs_595_666) ++ funcs_666_728) ++
    funcs_728_799) ++ funcs_799_814) ++ funcs_814_815) ++ funcs_815_819) ++ funcs_819_850) ++
    funcs_850_874) ++ funcs_874_906) ++ funcs_906_907).toArray

/-- The code section as the decoder reads it: `contract.wasm`, ending at the
end of the section. -/
def codeInput : Input := { wNearSource.input with limit := 159291 }

/-- The code section's entries decode to `codes`, one after another, from
the first entry (byte 3445) to the end of the section. -/
theorem reads_codes : Reads code codeInput codes 3445 159291 :=
    (((((((((((((((((((((reads_0_74).append reads_74_145).append reads_145_173).append
    reads_173_177).append reads_177_181).append reads_181_255).append reads_255_291).append
    reads_291_360).append reads_360_389).append reads_389_451).append reads_451_532).append
    reads_532_595).append reads_595_666).append reads_666_728).append reads_728_799).append
    reads_799_814).append reads_814_815).append reads_815_819).append reads_819_850).append
    reads_850_874).append reads_874_906).append reads_906_907

/-- No body uses a data index. -/
theorem noData_codes : (codes.any fun e => anyUsesDataIndex e.2.2) = false := by
  simp only [codes, List.any_append,
    noData_0_74, noData_74_145, noData_145_173, noData_173_177, noData_177_181, noData_181_255,
    noData_255_291, noData_291_360, noData_360_389, noData_389_451, noData_451_532, noData_532_595,
    noData_595_666, noData_666_728, noData_728_799, noData_799_814, noData_814_815, noData_815_819,
    noData_819_850, noData_850_874, noData_874_906, noData_906_907,
    Bool.or_self]

/-- The decoder assembles `funcs` from the types and the entries. -/
theorem zip_codes : List.zipWith entryFunc funcTypesList codes = funcs.toList := by
  simp only [funcTypesList, codes, funcs, List.toList_toArray]
  repeat rw [List.zipWith_append]
  · simp only [zip_0_74, zip_74_145, zip_145_173, zip_173_177, zip_177_181, zip_181_255, zip_255_291,
    zip_291_360, zip_360_389, zip_389_451, zip_451_532, zip_532_595, zip_595_666, zip_666_728,
    zip_728_799, zip_799_814, zip_814_815, zip_815_819, zip_819_850, zip_850_874, zip_874_906,
    zip_906_907]
  all_goals decide +kernel

end WNear.Binary
