import NearFastVM.Run
import NearRuntime.VmEngine

/-!
# The VM engine of the node

Every chunk the node applies and every view call it answers runs contracts with `NearFastVM` (notes/design/
NEAR_NODE.md, M10): the `Impl` of `Wasm.Near.run`, compared with it by `fastvm-differential` and, on the replay
corpus and the localnet chains, by every state root. Importing this module makes it the instance of
`Near.VmEngine` for the importing module; the runtime's own default is the specification.
-/

namespace Near.Node

instance fastEngine : Near.VmEngine :=
  ⟨fun cfg code codeSize method ctx storage => NearFastVM.run cfg code codeSize method ctx storage⟩

end Near.Node
