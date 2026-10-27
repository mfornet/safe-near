import Binary.Code

/-!
# `contract.wasm` as a module, decoded in the kernel

`wNearModule` is the module the decoder reads from `contract.wasm`, and
`decode_wNearBytes` proves it. The proof follows the decoder section by
section: the small sections are run by the kernel (`kernel_rfl`), the code
section is `reads_codes`, and the data segment's bytes are left as the
decoder reads them (`dataInit`), so the kernel never builds the 26 KB array.
-/

namespace WNear.Binary

open Wasm Binary Parser Wasm.Embed

#embed_wasm_sections "../contract.wasm"

/-- The bytes of the data segment: positions 159306 to the end of the file. -/
noncomputable def dataInit : ByteArray :=
  ⟨Array.ofFn (n := 26319) fun i => wNearSource.read (159306 + ↑i)⟩

/-- The data section: one active segment at address 1048576. -/
noncomputable def datas : Array Data := #[{ init := dataInit, mode := .active 0 [.i32_const 1048576] }]

/-- `contract.wasm`, decoded. -/
noncomputable def wNearModule : Module :=
  { types, funcs, tables, mems, globals, elems, datas, imports, exports }

/-! ## Section by section -/

theorem header_wNear : header wNearSource.input 0 = .ok ((), 8) := by kernel_rfl

theorem section_types : oneSection {} wNearSource.input 8 =
    .ok ({ module := { types }, lastRank := 1 }, 556) := by kernel_rfl

theorem section_imports : oneSection { module := { types }, lastRank := 1 } wNearSource.input 556 =
    .ok ({ module := { types, imports }, lastRank := 2 }, 1734) := by kernel_rfl

theorem section_funcs :
    oneSection { module := { types, imports }, lastRank := 2 } wNearSource.input 1734 =
      .ok ({ module := { types, imports }, funcTypes, lastRank := 3 }, 2646) := by kernel_rfl

theorem section_tables :
    oneSection { module := { types, imports }, funcTypes, lastRank := 3 } wNearSource.input 2646 =
      .ok ({ module := { types, imports, tables }, funcTypes, lastRank := 4 }, 2655) := by
  kernel_rfl

theorem section_mems :
    oneSection { module := { types, imports, tables }, funcTypes, lastRank := 4 }
      wNearSource.input 2655 =
      .ok ({ module := { types, imports, tables, mems }, funcTypes, lastRank := 5 }, 2660) := by
  kernel_rfl

theorem section_globals :
    oneSection { module := { types, imports, tables, mems }, funcTypes, lastRank := 5 }
      wNearSource.input 2660 =
      .ok ({ module := { types, imports, tables, mems, globals }, funcTypes, lastRank := 6 },
        2687) := by
  kernel_rfl

theorem section_exports :
    oneSection { module := { types, imports, tables, mems, globals }, funcTypes, lastRank := 6 }
      wNearSource.input 2687 =
      .ok ({ module := { types, imports, tables, mems, globals, exports }, funcTypes
             lastRank := 7 }, 3012) := by
  kernel_rfl

theorem section_elems :
    oneSection { module := { types, imports, tables, mems, globals, exports }, funcTypes
                 lastRank := 7 } wNearSource.input 3012 =
      .ok ({ module := { types, imports, tables, mems, globals, exports, elems }, funcTypes
             lastRank := 9 }, 3439) := by
  kernel_rfl

theorem vec_code : vec code codeInput 3443 = .ok (codes.toArray, 159291) := by
  have hn : u32 codeInput 3443 = .ok (codes.length, 3445) := by kernel_rfl
  exact (bind_ok hn).trans (count_of_reads reads_codes)

theorem section_code :
    oneSection { module := { types, imports, tables, mems, globals, exports, elems }, funcTypes
                 lastRank := 9 } wNearSource.input 3439 =
      .ok ({ module := { types, imports, tables, mems, globals, exports, elems }, funcTypes
             codes := codes.toArray, lastRank := 11 }, 159291) :=
  oneSection_code (q := 3443) (size := 155848) (by kernel_rfl) (by kernel_rfl) (by decide)
    (by decide) vec_code

theorem section_data :
    oneSection { module := { types, imports, tables, mems, globals, exports, elems }, funcTypes
                 codes := codes.toArray, lastRank := 11 } wNearSource.input 159291 =
      .ok ({ module := { types, imports, tables, mems, globals, exports, elems, datas }
             funcTypes, codes := codes.toArray, lastRank := 12 }, 185625) := by
  kernel_rfl

/-- What the section loop ends with. -/
noncomputable def sectionsEnd : Sections :=
  { module := { types, imports, tables, mems, globals, exports, elems, datas }
    funcTypes, codes := codes.toArray, lastRank := 12 }

theorem sections_wNear : sections (wNearSource.input.limit - 8) {} wNearSource.input 8 =
    .ok (sectionsEnd, 185625) :=
  (sections_step 185616 (by decide +kernel) section_types).trans <|
  (sections_step 185615 (by decide +kernel) section_imports).trans <|
  (sections_step 185614 (by decide +kernel) section_funcs).trans <|
  (sections_step 185613 (by decide +kernel) section_tables).trans <|
  (sections_step 185612 (by decide +kernel) section_mems).trans <|
  (sections_step 185611 (by decide +kernel) section_globals).trans <|
  (sections_step 185610 (by decide +kernel) section_exports).trans <|
  (sections_step 185609 (by decide +kernel) section_elems).trans <|
  (sections_step 185608 (by decide +kernel) section_code).trans <|
  (sections_step 185607 (by decide +kernel) section_data).trans <|
  sections_end 185607 (by decide +kernel)

theorem funcTypes_toList : funcTypes.toList = funcTypesList := by kernel_rfl

theorem body_wNear : body wNearSource.input 8 = .ok (wNearModule, 185625) := by
  rw [body_eq sections_wNear (by decide +kernel) rfl (by simpa [sectionsEnd] using noData_codes)]
  have hfuncs : funcTypes.zipWith entryFunc codes.toArray = funcs := by
    apply Array.toList_inj.mp
    rw [Array.toList_zipWith, funcTypes_toList, List.toList_toArray, zip_codes]
  simp only [sectionsEnd, hfuncs]
  rfl

theorem module_wNear : Parser.module wNearSource.input 0 = .ok (wNearModule, 185625) := by
  unfold Parser.module
  rw [bind_ok header_wNear]
  exact body_wNear

/-- The deployed binary decodes to `wNearModule`. -/
theorem decode_wNearBytes : Binary.decode wNearBytes = .ok wNearModule := by
  rw [wNearBytes, ByteSource.decode_toBytes, decodeInput, module_wNear]

end WNear.Binary
