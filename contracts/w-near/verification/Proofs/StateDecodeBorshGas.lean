import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodePrefixWrapperCallResult
import Proofs.StateDecodeScalarResult

/-! Exact425 phase charges, including actual315/372/371 entry and body charges.
The only domain premises are original Native and allocation compatibility. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
private theorem units_set(s:Store NearState)(op n index:Nat)(v:Value):
    GasUnits s (setGlobal (paid s op n) index v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem units32(s:Store NearState)(op n index address:Nat)(memory:Memory)(v:UInt32):
    GasUnits s (storeI32 (paid s op n) index address memory v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem units64(s:Store NearState)(op n index address:Nat)(memory:Memory)(v:UInt64):
    GasUnits s (storeI64 (paid s op n) index address memory v) op n := (gasUnits_paid s op n).host_eq rfl
attribute [local irreducible] reserved prefixArguments prefixDecoded prefixCached prefixGuarded prefixHighSaved prefixSaved wideArguments wideDecoded wideFirstSaved wideSecondSaved wideSaved wideGuarded wideCached narrowArguments narrowDecoded narrowHighSaved narrowSaved narrowGuarded vectorHighSaved vectorSaved usageCached output16 output8 output24 output32 output40 tagged branched after

theorem reserved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (reserved s cfg.regularOpCost p) cfg.regularOpCost 5:=by
  unfold reserved
  exact units_set s cfg.regularOpCost 5 p.globalIndex (.i32 (scratch p))
theorem prefixArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (prefixArguments s cfg.regularOpCost p) cfg.regularOpCost 9:=by
  have h:=(reserved_gas cfg s p).trans (gasUnits_paid (reserved s cfg.regularOpCost p) cfg.regularOpCost 4)
  simpa only[prefixArguments,Nat.reduceAdd] using h

theorem prefixDecoded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (prefixDecoded cfg s p q) cfg.regularOpCost (18*(count p).toNat+981):=by
  have step:=StateDecodePrefixWrapper.callAfter_gas cfg (prefixArguments s cfg.regularOpCost p) p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  have h:=(prefixArguments_gas cfg s p).trans step
  simpa only[prefixDecoded,count,show 9+(18*(StateDecodePrefix.count p.toPrefix).toNat+972)=18*(StateDecodePrefix.count p.toPrefix).toNat+981 by omega] using h

theorem prefixCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (prefixCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+984):=by
  have step:=gasUnits_paid (prefixDecoded cfg s p q) cfg.regularOpCost 3
  have h:=(prefixDecoded_gas cfg s p q hn hd).trans step
  simpa only[prefixCached,show (18*(count p).toNat+981)+3=18*(count p).toNat+984 by omega] using h

theorem prefixGuarded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (prefixGuarded cfg s p q) cfg.regularOpCost (18*(count p).toNat+989):=by
  have step:=gasUnits_paid (prefixCached cfg s p q) cfg.regularOpCost 5
  have h:=(prefixCached_gas cfg s p q hn hd).trans step
  simpa only[prefixGuarded,show (18*(count p).toNat+984)+5=18*(count p).toNat+989 by omega] using h

theorem prefixHighSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (prefixHighSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+996):=by
  have step:=units32 (prefixGuarded cfg s p q) cfg.regularOpCost 7 p.memoryIndex ((scratch p).toNat+24) (prefixMemory p q) (prefixLength p q)
  have h:=(prefixGuarded_gas cfg s p q hn hd).trans step
  simpa only[prefixHighSaved,show (18*(count p).toNat+989)+7=18*(count p).toNat+996 by omega] using h

theorem prefixSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (prefixSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+999):=by
  have step:=units64 (prefixHighSaved cfg s p q) cfg.regularOpCost 3 p.memoryIndex ((scratch p).toNat+16) (prefixHighMemory p q) (prefixPacked p q)
  have h:=(prefixHighSaved_gas cfg s p q hn hd).trans step
  simpa only[prefixSaved,show (18*(count p).toNat+996)+3=18*(count p).toNat+999 by omega] using h

theorem wideArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+1003):=by
  have step:=gasUnits_paid (prefixSaved cfg s p q) cfg.regularOpCost 4
  have h:=(prefixSaved_gas cfg s p q hn hd).trans step
  simpa only[wideArguments,show (18*(count p).toNat+999)+4=18*(count p).toNat+1003 by omega] using h

theorem wideDecoded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideDecoded cfg s p q) cfg.regularOpCost (18*(count p).toNat+1171):=by
  have step:=StateDecodeScalar.callAfter_gas true cfg (wideArguments cfg s p q) (wideLayout p q)
  have h:=(wideArguments_gas cfg s p q hn hd).trans step
  simpa only[wideDecoded,ite_true,show (18*(count p).toNat+1003)+168=18*(count p).toNat+1171 by omega] using h

theorem wideFirstSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideFirstSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1179):=by
  have step:=units64 (wideDecoded cfg s p q) cfg.regularOpCost 8 p.memoryIndex ((scratch p+32)+8).toNat (wideMemory p q) (readI64 (wideMemory p q) (scratch p+68).toNat)
  have h:=(wideDecoded_gas cfg s p q hn hd).trans step
  simpa only[wideFirstSaved,show (18*(count p).toNat+1171)+8=18*(count p).toNat+1179 by omega] using h

theorem wideSecondSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideSecondSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1187):=by
  have step:=units32 (wideFirstSaved cfg s p q) cfg.regularOpCost 8 p.memoryIndex (scratch p+48).toNat (wideFirstMemory p q) (readI32 (wideFirstMemory p q) (scratch p+76).toNat)
  have h:=(wideFirstSaved_gas cfg s p q hn hd).trans step
  simpa only[wideSecondSaved,show (18*(count p).toNat+1179)+8=18*(count p).toNat+1187 by omega] using h

theorem wideSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1191):=by
  have step:=units64 (wideSecondSaved cfg s p q) cfg.regularOpCost 4 p.memoryIndex ((scratch p).toNat+32) (wideSecondMemory p q) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60))
  have h:=(wideSecondSaved_gas cfg s p q hn hd).trans step
  simpa only[wideSaved,show (18*(count p).toNat+1187)+4=18*(count p).toNat+1191 by omega] using h

theorem wideGuarded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideGuarded cfg s p q) cfg.regularOpCost (18*(count p).toNat+1196):=by
  have step:=gasUnits_paid (wideSaved cfg s p q) cfg.regularOpCost 5
  have h:=(wideSaved_gas cfg s p q hn hd).trans step
  simpa only[wideGuarded,show (18*(count p).toNat+1191)+5=18*(count p).toNat+1196 by omega] using h

theorem wideCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wideCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+1206):=by
  have step:=gasUnits_paid (wideGuarded cfg s p q) cfg.regularOpCost 10
  have h:=(wideGuarded_gas cfg s p q hn hd).trans step
  simpa only[wideCached,show (18*(count p).toNat+1196)+10=18*(count p).toNat+1206 by omega] using h

theorem narrowArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (narrowArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+1210):=by
  have step:=gasUnits_paid (wideCached cfg s p q) cfg.regularOpCost 4
  have h:=(wideCached_gas cfg s p q hn hd).trans step
  simpa only[narrowArguments,show (18*(count p).toNat+1206)+4=18*(count p).toNat+1210 by omega] using h

theorem narrowDecoded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (narrowDecoded cfg s p q) cfg.regularOpCost (18*(count p).toNat+1361):=by
  have step:=StateDecodeScalar.callAfter_gas false cfg (narrowArguments cfg s p q) (narrowLayout p q)
  have h:=(narrowArguments_gas cfg s p q hn hd).trans step
  simpa only[narrowDecoded,Bool.false_eq_true,ite_false,show (18*(count p).toNat+1210)+151=18*(count p).toNat+1361 by omega] using h

theorem narrowHighSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (narrowHighSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1373):=by
  have step:=units32 (narrowDecoded cfg s p q) cfg.regularOpCost 12 p.memoryIndex ((scratch p+80)+8).toNat (narrowMemory p q) (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat)
  have h:=(narrowDecoded_gas cfg s p q hn hd).trans step
  simpa only[narrowHighSaved,show (18*(count p).toNat+1361)+12=18*(count p).toNat+1373 by omega] using h

theorem narrowSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (narrowSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1377):=by
  have step:=units64 (narrowHighSaved cfg s p q) cfg.regularOpCost 4 p.memoryIndex ((scratch p).toNat+80) (narrowHighMemory p q) (readI64 (narrowHighMemory p q) ((scratch p).toNat+60))
  have h:=(narrowHighSaved_gas cfg s p q hn hd).trans step
  simpa only[narrowSaved,show (18*(count p).toNat+1373)+4=18*(count p).toNat+1377 by omega] using h

theorem narrowGuarded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (narrowGuarded cfg s p q) cfg.regularOpCost (18*(count p).toNat+1382):=by
  have step:=gasUnits_paid (narrowSaved cfg s p q) cfg.regularOpCost 5
  have h:=(narrowSaved_gas cfg s p q hn hd).trans step
  simpa only[narrowGuarded,show (18*(count p).toNat+1377)+5=18*(count p).toNat+1382 by omega] using h

theorem vectorHighSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (vectorHighSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1393):=by
  have step:=units32 (narrowGuarded cfg s p q) cfg.regularOpCost 11 p.memoryIndex (scratch p+8).toNat (savedNarrowMemory p q) (vectorLength p q)
  have h:=(narrowGuarded_gas cfg s p q hn hd).trans step
  simpa only[vectorHighSaved,show (18*(count p).toNat+1382)+11=18*(count p).toNat+1393 by omega] using h

theorem vectorSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (vectorSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+1398):=by
  have step:=units64 (vectorHighSaved cfg s p q) cfg.regularOpCost 5 p.memoryIndex (scratch p).toNat (vectorHighMemory p q) (vectorPacked p q)
  have h:=(vectorHighSaved_gas cfg s p q hn hd).trans step
  simpa only[vectorSaved,show (18*(count p).toNat+1393)+5=18*(count p).toNat+1398 by omega] using h

theorem usageCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (usageCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+1401):=by
  have step:=gasUnits_paid (vectorSaved cfg s p q) cfg.regularOpCost 3
  have h:=(vectorSaved_gas cfg s p q hn hd).trans step
  simpa only[usageCached,show (18*(count p).toNat+1398)+3=18*(count p).toNat+1401 by omega] using h

theorem output16_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (output16 cfg s p q) cfg.regularOpCost (18*(count p).toNat+1406):=by
  have step:=units64 (usageCached cfg s p q) cfg.regularOpCost 5 p.memoryIndex (p.out425+16).toNat (cachedMemory p q) (wideHigh p q)
  have h:=(usageCached_gas cfg s p q hn hd).trans step
  simpa only[output16,show (18*(count p).toNat+1401)+5=18*(count p).toNat+1406 by omega] using h

theorem output8_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (output8 cfg s p q) cfg.regularOpCost (18*(count p).toNat+1411):=by
  have step:=units64 (output16 cfg s p q) cfg.regularOpCost 5 p.memoryIndex (p.out425+8).toNat (output16Memory p q) (wideLow p q)
  have h:=(output16_gas cfg s p q hn hd).trans step
  simpa only[output8,show (18*(count p).toNat+1406)+5=18*(count p).toNat+1411 by omega] using h

theorem output24_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (output24 cfg s p q) cfg.regularOpCost (18*(count p).toNat+1416):=by
  have step:=units64 (output8 cfg s p q) cfg.regularOpCost 5 p.memoryIndex (p.out425+24).toNat (output8Memory p q) (usageValue p q)
  have h:=(output8_gas cfg s p q hn hd).trans step
  simpa only[output24,show (18*(count p).toNat+1411)+5=18*(count p).toNat+1416 by omega] using h

theorem output32_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (output32 cfg s p q) cfg.regularOpCost (18*(count p).toNat+1421):=by
  have step:=units64 (output24 cfg s p q) cfg.regularOpCost 5 p.memoryIndex (p.out425+32).toNat (output24Memory p q) (vectorPacked p q)
  have h:=(output24_gas cfg s p q hn hd).trans step
  simpa only[output32,show (18*(count p).toNat+1416)+5=18*(count p).toNat+1421 by omega] using h

theorem output40_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (output40 cfg s p q) cfg.regularOpCost (18*(count p).toNat+1426):=by
  have step:=units32 (output32 cfg s p q) cfg.regularOpCost 5 p.memoryIndex (p.out425+40).toNat (output32Memory p q) (vectorLength p q)
  have h:=(output32_gas cfg s p q hn hd).trans step
  simpa only[output40,show (18*(count p).toNat+1421)+5=18*(count p).toNat+1426 by omega] using h

theorem tagged_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (tagged cfg s p q) cfg.regularOpCost (18*(count p).toNat+1429):=by
  have step:=units32 (output40 cfg s p q) cfg.regularOpCost 3 p.memoryIndex p.out425.toNat (output40Memory p q) 0
  have h:=(output40_gas cfg s p q hn hd).trans step
  simpa only[tagged,show (18*(count p).toNat+1426)+3=18*(count p).toNat+1429 by omega] using h

theorem branched_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (branched cfg s p q) cfg.regularOpCost (18*(count p).toNat+1430):=by
  have step:=gasUnits_charge (tagged cfg s p q) cfg.regularOpCost 1
  have h:=(tagged_gas cfg s p q hn hd).trans step
  simpa only[branched,Nat.one_mul,show (18*(count p).toNat+1429)+1=18*(count p).toNat+1430 by omega] using h

theorem after_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (after cfg s p q) cfg.regularOpCost (18*(count p).toNat+1434):=by
  have step:=units_set (branched cfg s p q) cfg.regularOpCost 4 p.globalIndex (.i32 p.sp425)
  have h:=(branched_gas cfg s p q hn hd).trans step
  simpa only[after,show (18*(count p).toNat+1430)+4=18*(count p).toNat+1434 by omega] using h

/-! Credit cuts use the original store budget and leave the stated remainder. -/

theorem reserved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest)):
    (reserved s cfg.regularOpCost p).host.gas.Credits rest := (reserved_gas cfg s p rest hc).2.2

theorem prefixArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (9*cfg.regularOpCost+rest)):
    (prefixArguments s cfg.regularOpCost p).host.gas.Credits rest := (prefixArguments_gas cfg s p rest hc).2.2

theorem prefixDecoded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+981)*cfg.regularOpCost+rest)):
    (prefixDecoded cfg s p q).host.gas.Credits rest := (prefixDecoded_gas cfg s p q hn hd rest hc).2.2

theorem prefixCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+984)*cfg.regularOpCost+rest)):
    (prefixCached cfg s p q).host.gas.Credits rest := (prefixCached_gas cfg s p q hn hd rest hc).2.2

theorem prefixGuarded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+989)*cfg.regularOpCost+rest)):
    (prefixGuarded cfg s p q).host.gas.Credits rest := (prefixGuarded_gas cfg s p q hn hd rest hc).2.2

theorem prefixHighSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+996)*cfg.regularOpCost+rest)):
    (prefixHighSaved cfg s p q).host.gas.Credits rest := (prefixHighSaved_gas cfg s p q hn hd rest hc).2.2

theorem prefixSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+999)*cfg.regularOpCost+rest)):
    (prefixSaved cfg s p q).host.gas.Credits rest := (prefixSaved_gas cfg s p q hn hd rest hc).2.2

theorem wideArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1003)*cfg.regularOpCost+rest)):
    (wideArguments cfg s p q).host.gas.Credits rest := (wideArguments_gas cfg s p q hn hd rest hc).2.2

theorem wideDecoded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1171)*cfg.regularOpCost+rest)):
    (wideDecoded cfg s p q).host.gas.Credits rest := (wideDecoded_gas cfg s p q hn hd rest hc).2.2

theorem wideFirstSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1179)*cfg.regularOpCost+rest)):
    (wideFirstSaved cfg s p q).host.gas.Credits rest := (wideFirstSaved_gas cfg s p q hn hd rest hc).2.2

theorem wideSecondSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1187)*cfg.regularOpCost+rest)):
    (wideSecondSaved cfg s p q).host.gas.Credits rest := (wideSecondSaved_gas cfg s p q hn hd rest hc).2.2

theorem wideSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1191)*cfg.regularOpCost+rest)):
    (wideSaved cfg s p q).host.gas.Credits rest := (wideSaved_gas cfg s p q hn hd rest hc).2.2

theorem wideGuarded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1196)*cfg.regularOpCost+rest)):
    (wideGuarded cfg s p q).host.gas.Credits rest := (wideGuarded_gas cfg s p q hn hd rest hc).2.2

theorem wideCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1206)*cfg.regularOpCost+rest)):
    (wideCached cfg s p q).host.gas.Credits rest := (wideCached_gas cfg s p q hn hd rest hc).2.2

theorem narrowArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1210)*cfg.regularOpCost+rest)):
    (narrowArguments cfg s p q).host.gas.Credits rest := (narrowArguments_gas cfg s p q hn hd rest hc).2.2

theorem narrowDecoded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1361)*cfg.regularOpCost+rest)):
    (narrowDecoded cfg s p q).host.gas.Credits rest := (narrowDecoded_gas cfg s p q hn hd rest hc).2.2

theorem narrowHighSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1373)*cfg.regularOpCost+rest)):
    (narrowHighSaved cfg s p q).host.gas.Credits rest := (narrowHighSaved_gas cfg s p q hn hd rest hc).2.2

theorem narrowSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1377)*cfg.regularOpCost+rest)):
    (narrowSaved cfg s p q).host.gas.Credits rest := (narrowSaved_gas cfg s p q hn hd rest hc).2.2

theorem narrowGuarded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1382)*cfg.regularOpCost+rest)):
    (narrowGuarded cfg s p q).host.gas.Credits rest := (narrowGuarded_gas cfg s p q hn hd rest hc).2.2

theorem vectorHighSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1393)*cfg.regularOpCost+rest)):
    (vectorHighSaved cfg s p q).host.gas.Credits rest := (vectorHighSaved_gas cfg s p q hn hd rest hc).2.2

theorem vectorSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1398)*cfg.regularOpCost+rest)):
    (vectorSaved cfg s p q).host.gas.Credits rest := (vectorSaved_gas cfg s p q hn hd rest hc).2.2

theorem usageCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1401)*cfg.regularOpCost+rest)):
    (usageCached cfg s p q).host.gas.Credits rest := (usageCached_gas cfg s p q hn hd rest hc).2.2

theorem output16_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1406)*cfg.regularOpCost+rest)):
    (output16 cfg s p q).host.gas.Credits rest := (output16_gas cfg s p q hn hd rest hc).2.2

theorem output8_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1411)*cfg.regularOpCost+rest)):
    (output8 cfg s p q).host.gas.Credits rest := (output8_gas cfg s p q hn hd rest hc).2.2

theorem output24_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1416)*cfg.regularOpCost+rest)):
    (output24 cfg s p q).host.gas.Credits rest := (output24_gas cfg s p q hn hd rest hc).2.2

theorem output32_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1421)*cfg.regularOpCost+rest)):
    (output32 cfg s p q).host.gas.Credits rest := (output32_gas cfg s p q hn hd rest hc).2.2

theorem output40_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1426)*cfg.regularOpCost+rest)):
    (output40 cfg s p q).host.gas.Credits rest := (output40_gas cfg s p q hn hd rest hc).2.2

theorem tagged_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1429)*cfg.regularOpCost+rest)):
    (tagged cfg s p q).host.gas.Credits rest := (tagged_gas cfg s p q hn hd rest hc).2.2

theorem branched_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1430)*cfg.regularOpCost+rest)):
    (branched cfg s p q).host.gas.Credits rest := (branched_gas cfg s p q hn hd rest hc).2.2

theorem after_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+1434)*cfg.regularOpCost+rest)):
    (after cfg s p q).host.gas.Credits rest := (after_gas cfg s p q hn hd rest hc).2.2
end WNear.Proofs.StateDecodeBorsh
