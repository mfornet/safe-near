import NearRuntime.Boundary

/-!
# M2 walking module

A straight-line method takes arbitrary bytes from the input register,
puts them at key `k`, logs `saved`, and returns the same bytes. Register reads
use NEAR's `u64::MAX` length convention. The log follows the write so that a
failed later charge exercises rollback of a completed write.

The module is defined directly as syntax with loading size zero; binary
correspondence is the separate M0 obligation.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near

def module : Module :=
  { types := #[
      { params := [.i64], results := [] },
      { params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] },
      { params := [.i64, .i64], results := [] },
      { params := [], results := [] }],
    imports := #[
      { «module» := "env", name := "input", desc := .func 0 },
      { «module» := "env", name := "storage_write", desc := .func 1 },
      { «module» := "env", name := "log_utf8", desc := .func 2 },
      { «module» := "env", name := "value_return", desc := .func 2 }],
    funcs := #[{ type := 3, locals := [], body := [
      .i64_const 0, .call 0,
      .i64_const 1, .i64_const 0,
      .i64_const 0xffffffffffffffff, .i64_const 0,
      .i64_const 0xffffffffffffffff, .call 1, .drop,
      .i64_const 5, .i64_const 1, .call 2,
      .i64_const 0xffffffffffffffff, .i64_const 0, .call 3] }],
    mems := #[{ type := { limits := { min := 1, max := none } } }],
    datas := #[{ init := ⟨#[107, 115, 97, 118, 101, 100]⟩, mode := .active 0 [.i32_const 0] }],
    exports := #[{ name := "save", desc := .func 4 }] }

/-- Promised deployments are absent, so the decoder is unused. -/
def code : Near.Boundary.Code :=
  { code := { module, size := 0, hash := "walking-skeleton" }, codeOf := fun _ => default }

@[simp] theorem no_start : module.start = none := rfl
@[simp] theorem save_export : module.exportFunc? "save" = some 4 := by decide
@[simp] theorem save_type : module.funcType? 4 = some { params := [], results := [] } := by decide

/-- The model's successful storage update, preserving unrelated keys. -/
def savedStorage (storage : List (Near.Bytes × Near.Bytes)) (args : Near.Bytes) :
    List (Near.Bytes × Near.Bytes) :=
  ("k".toUTF8.toList, args) :: storage.filter (fun entry => entry.1 != "k".toUTF8.toList)

/-- Executable successful postcondition, including the storage usage delta. -/
def matchesCheck (ctx : NearInterface.Context) (storage : List (Near.Bytes × Near.Bytes))
    (r : NearInterface.Observation) : Bool :=
  (match r.outcome with | .ok (.value value) => value == ctx.args | _ => false) &&
  decide (r.storage = (savedStorage storage ctx.args).toFinset) &&
  r.balance == ctx.balance + ctx.attached &&
  r.storageUsage == ctx.storageUsage - NearInterface.storageUsageOf ctx.protocol storage.toFinset +
    NearInterface.storageUsageOf ctx.protocol (savedStorage storage ctx.args).toFinset &&
  r.logs == ["saved"] && r.receipts.isEmpty

/-- Creation and replacement both install precisely the supplied bytes. -/
theorem savedStorage_head (storage : List (Near.Bytes × Near.Bytes)) (args : Near.Bytes) :
    ("k".toUTF8.toList, args) ∈ savedStorage storage args := by
  simp [savedStorage]

/-- The model does not remove or alter any other key-value pair. -/
theorem savedStorage_other (storage : List (Near.Bytes × Near.Bytes)) (args key value : Near.Bytes)
    (hkey : key ≠ "k".toUTF8.toList) :
    (key, value) ∈ savedStorage storage args ↔ (key, value) ∈ storage := by
  have hkey' : key ≠ "k".toByteArray.toList := hkey
  simp [savedStorage, hkey']



/-- Successful method behavior is independent of any earlier value at `k`. -/
theorem savedStorage_key (storage : List (Near.Bytes × Near.Bytes)) (args value : Near.Bytes) :
    ("k".toUTF8.toList, value) ∈ savedStorage storage args ↔ value = args := by
  simp [savedStorage]

end WNear.Skeleton
