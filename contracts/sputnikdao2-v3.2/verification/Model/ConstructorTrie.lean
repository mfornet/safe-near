import Model.RootStateEncoding
import Model.ConfigPolicyDecoding
import Model.BountyTrie

namespace SputnikDAO2

/-! Fresh-storage constructor image. `new` writes four auxiliary keys; the
near-sdk generated `#[init]` wrapper subsequently writes the root `STATE`
key. Wrapper guards, rollback, and arbitrary pre-existing storage are outside
this functional trie projection. -/

def daoConfigKey : BountyBytes := [0]
def daoPolicyKey : BountyBytes := [1]
def daoFactoryKey : BountyBytes := [70, 65, 67, 84, 79, 82, 89]
def daoVersionKey : BountyBytes :=
  [83, 84, 65, 84, 69, 86, 69, 82, 83, 73, 79, 78]
def daoRootKey : BountyBytes := [83, 84, 65, 84, 69]

def constructorAuxTrie (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) : BountyRawTrie :=
  bountyRawWrite
    (bountyRawWrite
      (bountyRawWrite
        (bountyRawWrite bountyEmptyRaw daoConfigKey
          (encodeWireConfig config))
        daoPolicyKey (encodeWireVersionedPolicy (.current policy)))
      daoFactoryKey (initializedFactoryBytes predecessor))
    daoVersionKey initializedVersionBytes

def constructorTrie (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) : BountyRawTrie :=
  bountyRawWrite (constructorAuxTrie config policy predecessor)
    daoRootKey initializedRootBytes

-- The generated `#[init]` wrapper checks only the root `STATE` key. If it is
-- absent while other keys are present, direct `new` overwrites its four
-- auxiliary keys and the wrapper writes STATE, leaving unrelated keys intact.
def constructorOnExistingTrie (raw : BountyRawTrie)
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) : BountyRawTrie :=
  bountyRawWrite
    (bountyRawWrite
      (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoConfigKey
            (encodeWireConfig config))
          daoPolicyKey (encodeWireVersionedPolicy (.current policy)))
        daoFactoryKey (initializedFactoryBytes predecessor))
      daoVersionKey initializedVersionBytes)
    daoRootKey initializedRootBytes

def constructorKey (key : BountyBytes) : Prop :=
  key = daoConfigKey ∨ key = daoPolicyKey ∨
  key = daoFactoryKey ∨ key = daoVersionKey ∨
  key = daoRootKey

def daoCollectionTags : List UInt8 := [2, 3, 4, 5, 6, 7]

end SputnikDAO2
