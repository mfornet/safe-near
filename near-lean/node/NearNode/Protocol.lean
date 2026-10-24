/-!
# Protocol pin

The node implements exactly one nearcore release. These values must match
`near-lean/runtime/reference.json`; `tools/check_node_isolation.py` checks it.
-/

namespace Near.Node

/-- The nearcore release the node is compatible with. -/
def nearcoreRelease : String := "2.13.4"

/-- The protocol version the node speaks. -/
def protocolVersion : Nat := 86

end Near.Node
