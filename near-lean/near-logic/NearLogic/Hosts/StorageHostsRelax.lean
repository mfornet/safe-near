import NearLogic.Hosts.StorageFnsRelax
import NearLogic.Hosts.StorageRelax

/-!
# The storage hosts under raised gas limits

The storage phase (`invokeRelax_storage`) and each storage host's
functional part (`StorageFnsRelax`) give `RelaxFn` for the four storage
hosts wNEAR imports.
-/

namespace NearLogic

open Wasm Wasm.Near

theorem relaxFn_storageRead (extra : Nat) : RelaxFn (metered extra "storage_read" storageReadFn).toHostFn :=
  relaxFn_metered extra (by simp [gasNames]) storageReadFn
    (invokeRelax_storage extra _ storageReadFn storageReadFn_relax storageReadFn_keep)

theorem relaxFn_storageWrite (extra : Nat) : RelaxFn (metered extra "storage_write" storageWriteFn).toHostFn :=
  relaxFn_metered extra (by simp [gasNames]) storageWriteFn
    (invokeRelax_storage extra _ storageWriteFn storageWriteFn_relax storageWriteFn_keep)

theorem relaxFn_storageRemove (extra : Nat) : RelaxFn (metered extra "storage_remove" storageRemoveFn).toHostFn :=
  relaxFn_metered extra (by simp [gasNames]) storageRemoveFn
    (invokeRelax_storage extra _ storageRemoveFn storageRemoveFn_relax storageRemoveFn_keep)

theorem relaxFn_storageHasKey (extra : Nat) :
    RelaxFn (metered extra "storage_has_key" storageHasKeyFn).toHostFn :=
  relaxFn_metered extra (by simp [gasNames]) storageHasKeyFn
    (invokeRelax_storage extra _ storageHasKeyFn storageHasKeyFn_relax storageHasKeyFn_keep)

end NearLogic
