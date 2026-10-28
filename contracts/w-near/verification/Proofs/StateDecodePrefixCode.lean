import Proofs.StateDecodePrefixState

/-! Original code descriptors for316's real positive branch, including the
allocation/copy helper374 whose execution remains a separate proof obligation. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic

structure Code (s:Store NearState) (inst:Nat) (p:Layout) : Prop where
  module : s.modules[inst]?=some p.mi
  memoryIndex : p.mi.memAddrs[0]?=some p.memoryIndex
  globalIndex : p.mi.globalAddrs[0]?=some p.globalIndex
  takeAddress : p.mi.funcAddrs[362]?=some p.takeAddress
  takeFunction : s.funcs[p.takeAddress]?=some (.wasm WNear.Binary.StateDecodeSlices.signature inst (WNear.Binary.StateDecodeSlices.function false))
  dropAddress : p.mi.funcAddrs[361]?=some p.dropAddress
  dropFunction : s.funcs[p.dropAddress]?=some (.wasm WNear.Binary.StateDecodeSlices.signature inst (WNear.Binary.StateDecodeSlices.function true))
  wordAddress : p.mi.funcAddrs[765]?=some p.wordAddress
  wordFunction : s.funcs[p.wordAddress]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.wordSignature inst WNear.Binary.StateDecodePrefixLeaves.wordFunction)
  lengthAddress : p.mi.funcAddrs[764]?=some p.lengthAddress
  lengthFunction : s.funcs[p.lengthAddress]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.recordSignature inst WNear.Binary.StateDecodePrefixLeaves.recordFunction)
  copyAddress : p.mi.funcAddrs[374]?=some p.copyAddress
  copyFunction : s.funcs[p.copyAddress]?=some (.wasm
    {params:=[.num .i32,.num .i32,.num .i32],results:=[]} inst WNear.Binary.f374)
end WNear.Proofs.StateDecodePrefix
