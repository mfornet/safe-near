# Pinned statements

Generated from `statements.json` by the axiom audit with `--update-statements`.
The audit fails when a statement here differs from the build: a change to
this file is a change to what the proofs prove, and is reviewed as one.

## Bridge.Exported

`WNear.Binary.Exported.At` (hash `0a1da15c89c211c8`)

```lean
def WNear.Binary.Exported.At (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (raw : WNear.RawStorage) (st : Option WNear.State) (ctx : NearInterface.Context) : Prop :=
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    (∀ (c : (WNear.wnear cfg).Call),
        (WNear.wnear cfg).Parses ctx.method ctx.args c →
          have res := (WNear.wnear cfg).step ctx st c;
          ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
              ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
                NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
                  r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
            (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
              NearInterface.ResourceFailure r ∧
                NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)) ∧
      ((¬∃ c, (WNear.wnear cfg).Parses ctx.method ctx.args c) →
        NearInterface.RolledBack ctx raw r)
```

`WNear.Binary.Exported.Environment` (hash `c6566a7375002a94`)

```lean
inductive WNear.Binary.Exported.Environment (protocol : Wasm.Near.RuntimeConfig) : Prop
| WNear.Binary.Exported.Environment.mk {protocol : Wasm.Near.RuntimeConfig} (runtime : WNear.Binary.WProtocol protocol)
  (costs : WNear.Binary.FtTotalSupplyMethod.CostsV86 protocol)
  (limits : WNear.Binary.FtTotalSupplyMethod.LimitsV86 protocol)
  (newCosts : WNear.Binary.NewMethod.CostsNewV86 protocol)
  (depositCosts : WNear.Binary.NearDepositGas.CostsDepositV86 protocol) : WNear.Binary.Exported.Environment protocol
```

`WNear.Binary.Exported.MethodClause` (hash `d439a2fea9f546d2`)

```lean
def WNear.Binary.Exported.MethodClause (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (method : String) : Prop :=
  cfg.WF →
    ∀ (raw : WNear.RawStorage) (st : Option WNear.State) (ctx : NearInterface.Context),
      (WNear.wnear cfg).Represents raw st →
        ctx.WF raw →
          ctx.protocol = protocol →
            ctx.method = method → WNear.Binary.Exported.At cfg size codeOf raw st ctx
```

`WNear.Binary.Exported.Remaining` (hash `a4f8f9acdf95444d`)

```lean
inductive WNear.Binary.Exported.Remaining (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) : Prop
| WNear.Binary.Exported.Remaining.mk {cfg : WNear.Config} {size : ℕ} {codeOf : List UInt8 → Near.ContractCode}
  {protocol : Wasm.Near.RuntimeConfig}
  (nearWithdraw : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "near_withdraw")
  (ftTransfer : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "ft_transfer")
  (ftTransferCall : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "ft_transfer_call")
  (ftBalanceOf : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "ft_balance_of")
  (ftResolveTransfer : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "ft_resolve_transfer")
  (storageDeposit : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "storage_deposit")
  (storageWithdraw : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "storage_withdraw")
  (storageUnregister : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "storage_unregister")
  (storageBalanceOf : WNear.Binary.Exported.MethodClause cfg size codeOf protocol "storage_balance_of") :
  WNear.Binary.Exported.Remaining cfg size codeOf protocol
```

`WNear.Binary.Exported.all_methods` (hash `000000002f5f4612`)

```lean
theorem WNear.Binary.Exported.all_methods (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625)
  (hr : WNear.Binary.Exported.Remaining cfg size codeOf protocol) (method : String)
  (hm : method ∈ WNear.exportedMethods) : WNear.Binary.Exported.MethodClause cfg size codeOf protocol method
```

`WNear.Binary.Exported.ftMetadata_complete` (hash `00000000223a89bf`)

```lean
theorem WNear.Binary.Exported.ftMetadata_complete (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) :
  WNear.Binary.Exported.MethodClause cfg size codeOf protocol "ft_metadata"
```

`WNear.Binary.Exported.ftTotalSupply_complete` (hash `00000000d059218f`)

```lean
theorem WNear.Binary.Exported.ftTotalSupply_complete (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) :
  WNear.Binary.Exported.MethodClause cfg size codeOf protocol "ft_total_supply"
```

`WNear.Binary.Exported.nearDeposit_complete` (hash `00000000c1cac692`)

```lean
theorem WNear.Binary.Exported.nearDeposit_complete (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) :
  WNear.Binary.Exported.MethodClause cfg size codeOf protocol "near_deposit"
```

`WNear.Binary.Exported.new_complete` (hash `00000000d0db84e1`)

```lean
theorem WNear.Binary.Exported.new_complete (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) :
  WNear.Binary.Exported.MethodClause cfg size codeOf protocol "new"
```

`WNear.Binary.Exported.storageBalanceBounds_complete` (hash `00000000af337474`)

```lean
theorem WNear.Binary.Exported.storageBalanceBounds_complete (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) :
  WNear.Binary.Exported.MethodClause cfg size codeOf protocol "storage_balance_bounds"
```

`WNear.Binary.Exported.storageMinimumBalance_complete` (hash `00000000a38c7a94`)

```lean
theorem WNear.Binary.Exported.storageMinimumBalance_complete (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) :
  WNear.Binary.Exported.MethodClause cfg size codeOf protocol "storage_minimum_balance"
```

`WNear.Binary.Exported.unit_at` (hash `00000000bb8f33ef`)

```lean
theorem WNear.Binary.Exported.unit_at (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (raw : WNear.RawStorage) (st : Option WNear.State) (ctx : NearInterface.Context) (c0 : WNear.Call)
  (hdecode : WNear.Call.decode ctx.method ctx.args = some c0)
  (hcall :
    have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
    have res := (WNear.wnear cfg).step ctx st c0;
    (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
      ((WNear.wnear cfg).gas ctx st c0 ≤ ctx.gasLimit →
          ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c0) →
            NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c0) ∧
        (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
          NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)) :
  WNear.Binary.Exported.At cfg size codeOf raw st ctx
```

## Bridge.Functions.BalanceOf297AbsentCall

`WNear.Binary.BalanceOf297AbsentCall.call_absent` (hash `000000003c0ef13a`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.call_absent {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ)
  (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth)
  (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 pp pc pl p c L idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob : List UInt8) (hs : 384 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hpre : pre.length = pl.toNat)
  (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120)
  (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 2 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        NearLogic.credits Cg
            (2100 * cfg.regularOpCost +
                WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)) +
              R) ∗
          WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl (s + 88) p c L idx
              maxP len live F pre key rest ob h
              [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] ∗
            ▷
              ∀ rs,
                NearLogic.credits Cg R -∗
                  WNear.Binary.BalanceOfAbsent.post293 n g ta A gt s (s + 8) (s + 48 + 24) pp pc pl (s + 88) p c L idx
                      maxP len live F pre (NearLogic.StorageReadPost h (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st)
                      [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] rs -∗
                    Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 10 (List.drop 91 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297AbsentCopy

`WNear.Binary.BalanceOf297AbsentCall.call_and_copy_absent` (hash `00000000d685e1bd`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.call_and_copy_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 pp pc pl p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob dest : List UInt8) (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (hpre : pre.length = pl.toNat)
  (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120)
  (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 2 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        NearLogic.credits Cg
            (2112 * cfg.regularOpCost +
                WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)) +
              R) ∗
          WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl (s + 88) p c L idx
              maxP len live F pre key rest ob h
              [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] ∗
            n ↦[wms][ (s + 128).toNat ] dest ∗
              ▷
                ∀ rs,
                  NearLogic.credits Cg R ∗
                      WNear.Binary.BalanceOfAbsent.post293 n g ta A gt s (s + 8) (s + 48 + 24) pp pc pl (s + 88) p c L
                          idx maxP len live F pre
                          (NearLogic.StorageReadPost h (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st)
                          [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] rs ∗
                        n ↦[wms][ (s + 128).toNat ]
                          WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++ WasmLogic.storeBytes (Wasm.Value.i64 0) 8 -∗
                    Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 22 (List.drop 91 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copy_zero` (hash `0000000093a0303d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copy_zero {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (n : ℕ)
  (hn : mi.memAddrs[0]? = some n) (Cg R : ℕ) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (ob : List UInt8) (hob : ob.length = 16) (Φ : WasmLogic.Post Wasm.NearState GF) :
  NearLogic.credits Cg (12 * cfg.regularOpCost + R) ∗
      n ↦[wms][ (s + 8).toNat ] WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++ WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ∗
        n ↦[wms][ (s + 128).toNat ] ob ∗
          ▷
            (NearLogic.credits Cg R ∗
                n ↦[wms][ (s + 8).toNat ]
                    WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++ WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ∗
                  n ↦[wms][ (s + 128).toNat ]
                    WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++ WasmLogic.storeBytes (Wasm.Value.i64 0) 8 -∗
              Φ.normal [] (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 12 (List.drop 101 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ArgumentCopy

`WNear.Binary.BalanceOf297AbsentCall.argument_copy` (hash `000000000afb975d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.argument_copy {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (n : ℕ)
  (hn : mi.memAddrs[0]? = some n) (Cg R : ℕ) (s x1 : UInt32) (x2 : UInt64) (p c L : UInt32) (ob : List UInt8)
  (hob : ob.length = 12) (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : WasmLogic.Post Wasm.NearState GF) :
  NearLogic.credits Cg (12 * cfg.regularOpCost + R) ∗
      n ↦[wms][ (s + 32).toNat ] WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
        n ↦[wms][ (s + 88).toNat ] ob ∗
          ▷
            (NearLogic.credits Cg R ∗
                n ↦[wms][ (s + 32).toNat ] WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) -∗
              Φ.normal [] (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 12 (List.drop 79 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297Cleanup

`WNear.Binary.BalanceOf297AbsentCall.cleanup` (hash `00000000ba1e7433`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.cleanup {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 q len pp pc pl : UInt32) (maxP hl F : ℕ) (live : List (ℕ × ℕ)) (qb pb : List UInt8)
  (hqb : qb.length = 128) (hpb : pb.length = pc.toNat) (hc : pc ≠ 0) (hframe : s.toNat + 160 ≤ 2 ^ 32)
  (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.DropVec.dropCode inst mi A ∗
      A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
        NearLogic.credits Cg (660 * cfg.regularOpCost + R) ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
            n ↦[wms][ (s + 144).toNat ] WasmLogic.bytes32 q ++ (WasmLogic.bytes32 128 ++ WasmLogic.bytes32 len) ∗
              n ↦[wms][ (s + 72).toNat ] WasmLogic.bytes32 pp ++ (WasmLogic.bytes32 pc ++ WasmLogic.bytes32 pl) ∗
                n ↦[wms][ q.toNat ] qb ∗
                  n ↦[wms][ pp.toNat ] pb ∗
                    WNear.Binary.AllocInv.heapInv n maxP hl ((q.toNat, 128) :: (pp.toNat, pc.toNat) :: live) F ∗
                      ▷
                        (NearLogic.credits Cg R ∗
                            g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                              n ↦[wms][ (s + 144).toNat ] WasmLogic.bytes32 q ∗
                                n ↦[wms][ (s + 144).toNat + 4 ] WasmLogic.bytes32 128 ∗
                                  n ↦[wms][ (s + 144).toNat + 8 ] WasmLogic.bytes32 len ∗
                                    n ↦[wms][ (s + 72).toNat ] WasmLogic.bytes32 pp ∗
                                      n ↦[wms][ (s + 72).toNat + 4 ] WasmLogic.bytes32 pc ∗
                                        n ↦[wms][ (s + 72).toNat + 8 ] WasmLogic.bytes32 pl ∗
                                          WNear.Binary.AllocInv.heapInv n maxP hl live (F + 1 + 1) -∗
                          Φ.normal [] (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 12 (List.drop 138 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297Compose

`WNear.Binary.BalanceOf297AbsentCall.call_copy_and_format_absent` (hash `000000007a075c62`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.call_copy_and_format_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 pp pc pl p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob dest tail : List UInt8) (hs : 416 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16)
  (htail : tail.length = 4) (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4)
  (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 4 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (ptr0 : UInt32)
  (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
          A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
            inst ↪[inst] mi ∗
              NearLogic.credits Cg
                  (2112 * cfg.regularOpCost +
                      WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)) +
                    (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 3) 0 0 + R)) ∗
                WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl (s + 88) p c L
                    idx maxP len live F pre key rest ob h
                    [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] ∗
                  WNear.Binary.VecFromElem.stk n (s.toNat - 416) 32 ∗
                    n ↦[wms][ (s + 100).toNat ] tail ∗
                      n ↦[wms][ (s + 128).toNat ] dest ∗
                        WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                          ▷
                            ∀ rs,
                              (NearLogic.credits Cg R ∗
                                  ⌜rs = []⌝ ∗
                                    g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                      WNear.Binary.VecFromElem.stk n (s.toNat - 416) 416 ∗
                                        WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                          WNear.Binary.LookupMapLeaves.prefixAt n (s + 48 + 24) pp pc pl ∗
                                            n ↦[wms][ pp.toNat ] pre ∗
                                              n ↦[wms][ (s + 8).toNat ]
                                                  WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++
                                                    WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ∗
                                                (∃ h',
                                                    ⌜NearLogic.StorageReadPost h (pre ++ (WasmLogic.bytes32 L ++ key)) 0
                                                          st h'⌝ ∗
                                                      NearLogic.mhostPt h') ∗
                                                  n ↦[wms][ (s + 128).toNat ] WNear.Binary.U128From.u128Bytes 0 0 ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                        ∃ q rest',
                                                          ⌜rest'.length =
                                                                128 -
                                                                  ((WNear.Binary.FmtString.kOf
                                                                        (WNear.Binary.FmtU128.val 0 0)).toNat +
                                                                    2)⌝ ∗
                                                            n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                                              n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 q ∗
                                                                n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 128 ∗
                                                                  n ↦[wms][ (s + 88).toNat + 12 ]
                                                                      WasmLogic.bytes32
                                                                        (0 +
                                                                            WNear.Binary.FmtString.kOf
                                                                              (WNear.Binary.FmtU128.val 0 0) +
                                                                          2) ∗
                                                                    n ↦[wms][ q.toNat ]
                                                                        [34] ++
                                                                              WNear.Binary.FmtDigits.decDigits
                                                                                (WNear.Binary.FmtU128.val 0 0) ++
                                                                            [34] ++
                                                                          rest' ∗
                                                                      ∃ hl',
                                                                        WNear.Binary.AllocInv.heapInv n maxP hl'
                                                                          ((q.toNat, 128) :: live) (F + 3 + 1)) -∗
                                Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 29 (List.drop 91 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ComposeCleanup

`WNear.Binary.BalanceOf297AbsentCall.call_through_cleanup_absent` (hash `00000000f8bc11ca`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.call_through_cleanup_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 pp pc pl p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob dest tail out head padding : List UInt8) (hs : 416 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16)
  (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8)
  (hpadding : pre.length + padding.length = pc.toNat) (hpc : pc ≠ 0) (hpre : pre.length = pl.toNat)
  (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120)
  (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 4 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
          A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
            A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
              A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                  A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                    WNear.Binary.DropVec.dropCode inst mi A ∗
                      A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                        WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                          inst ↪[inst] mi ∗
                            NearLogic.credits Cg
                                (2112 * cfg.regularOpCost +
                                    WNear.Binary.LookupMapGet.cost399None cfg F pl L h
                                      (pre ++ (WasmLogic.bytes32 L ++ key)) +
                                  (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 3) 0 0 +
                                    (44 * cfg.regularOpCost +
                                      (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                        (660 * cfg.regularOpCost + R))))) ∗
                              WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl
                                  (s + 88) p c L idx maxP len ((pp.toNat, pc.toNat) :: live) F pre key rest ob h
                                  [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] ∗
                                WNear.Binary.VecFromElem.stk n (s.toNat - 416) 32 ∗
                                  n ↦[wms][ (s + 100).toNat ] tail ∗
                                    n ↦[wms][ (s + 128).toNat ] dest ∗
                                      WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                        n ↦[wms][ (s + 144).toNat ] out ∗
                                          n ↦[wms][ s.toNat ] head ∗
                                            n ↦[wms][ pp.toNat + pre.length ] padding ∗
                                              ▷
                                                ((NearLogic.credits Cg R ∗
                                                    g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                      (∃ hl',
                                                          WNear.Binary.AllocInv.heapInv n maxP hl' live
                                                            (F + 3 + 1 + 1 + 1)) ∗
                                                        ∃ h',
                                                          ⌜NearLogic.StorageReadPost h
                                                                (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st h'⌝ ∗
                                                            NearLogic.mhostPt (h'.selectReturnValue [34, 48, 34])) -∗
                                                  Φ.normal []
                                                    (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 59 (List.drop 91 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ComposeExpect

`WNear.Binary.BalanceOf297AbsentCall.call_copy_format_and_expect_absent` (hash `00000000d7fd4324`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.call_copy_format_and_expect_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 pp pc pl p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob dest tail out : List UInt8) (hs : 416 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16)
  (htail : tail.length = 4) (hout : out.length = 12) (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4)
  (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 4 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (ptr0 : UInt32)
  (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
          A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
            A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
              inst ↪[inst] mi ∗
                NearLogic.credits Cg
                    (2112 * cfg.regularOpCost +
                        WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)) +
                      (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 3) 0 0 +
                        (44 * cfg.regularOpCost + R))) ∗
                  WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl (s + 88) p c
                      L idx maxP len live F pre key rest ob h
                      [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] ∗
                    WNear.Binary.VecFromElem.stk n (s.toNat - 416) 32 ∗
                      n ↦[wms][ (s + 100).toNat ] tail ∗
                        n ↦[wms][ (s + 128).toNat ] dest ∗
                          WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                            n ↦[wms][ (s + 144).toNat ] out ∗
                              ▷
                                ∀ rs,
                                  (NearLogic.credits Cg R ∗
                                      ⌜rs = []⌝ ∗
                                        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                          WNear.Binary.VecFromElem.stk n (s.toNat - 416) 416 ∗
                                            WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                              WNear.Binary.LookupMapLeaves.prefixAt n (s + 48 + 24) pp pc pl ∗
                                                n ↦[wms][ pp.toNat ] pre ∗
                                                  n ↦[wms][ (s + 8).toNat ]
                                                      WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++
                                                        WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ∗
                                                    (∃ h',
                                                        ⌜NearLogic.StorageReadPost h
                                                              (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st h'⌝ ∗
                                                          NearLogic.mhostPt h') ∗
                                                      n ↦[wms][ (s + 128).toNat ] WNear.Binary.U128From.u128Bytes 0 0 ∗
                                                        WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                          WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                            ∃ q rest',
                                                              ⌜rest'.length =
                                                                    128 -
                                                                      ((WNear.Binary.FmtString.kOf
                                                                            (WNear.Binary.FmtU128.val 0 0)).toNat +
                                                                        2)⌝ ∗
                                                                n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                                                  n ↦[wms][ (s + 88).toNat + 4 ]
                                                                      WasmLogic.bytes32 q ++ WasmLogic.bytes32 128 ++
                                                                        WasmLogic.bytes32
                                                                          (0 +
                                                                              WNear.Binary.FmtString.kOf
                                                                                (WNear.Binary.FmtU128.val 0 0) +
                                                                            2) ∗
                                                                    n ↦[wms][ (s + 144).toNat ]
                                                                        WasmLogic.bytes32 q ++ WasmLogic.bytes32 128 ++
                                                                          WasmLogic.bytes32
                                                                            (0 +
                                                                                WNear.Binary.FmtString.kOf
                                                                                  (WNear.Binary.FmtU128.val 0 0) +
                                                                              2) ∗
                                                                      n ↦[wms][ q.toNat ]
                                                                          [34] ++
                                                                                WNear.Binary.FmtDigits.decDigits
                                                                                  (WNear.Binary.FmtU128.val 0 0) ++
                                                                              [34] ++
                                                                            rest' ∗
                                                                        ∃ hl',
                                                                          WNear.Binary.AllocInv.heapInv n maxP hl'
                                                                            ((q.toNat, 128) :: live) (F + 3 + 1)) -∗
                                    Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 37 (List.drop 91 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ComposeReturn

`WNear.Binary.BalanceOf297AbsentCall.call_through_value_return_absent` (hash `000000009359573a`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.call_through_value_return_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 pp pc pl p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob dest tail out head : List UInt8) (hs : 416 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16)
  (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8) (hpre : pre.length = pl.toNat)
  (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120)
  (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 4 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
          A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
            A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
              A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                  A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                      inst ↪[inst] mi ∗
                        NearLogic.credits Cg
                            (2112 * cfg.regularOpCost +
                                WNear.Binary.LookupMapGet.cost399None cfg F pl L h
                                  (pre ++ (WasmLogic.bytes32 L ++ key)) +
                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 3) 0 0 +
                                (44 * cfg.regularOpCost +
                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 + R)))) ∗
                          WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl
                              (s + 88) p c L idx maxP len live F pre key rest ob h
                              [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 88)] ∗
                            WNear.Binary.VecFromElem.stk n (s.toNat - 416) 32 ∗
                              n ↦[wms][ (s + 100).toNat ] tail ∗
                                n ↦[wms][ (s + 128).toNat ] dest ∗
                                  WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                    n ↦[wms][ (s + 144).toNat ] out ∗
                                      n ↦[wms][ s.toNat ] head ∗
                                        ▷
                                          ∀ rs,
                                            (NearLogic.credits Cg R ∗
                                                WNear.Binary.VecFromElem.stk n (s.toNat - 416) 384 ∗
                                                  WNear.Binary.VecFromElem.stk n (s.toNat - 16) 8 ∗
                                                    WNear.Binary.Interface.slot n ta 12 38 (A 240) ∗
                                                      WNear.Binary.LookupMapLeaves.prefixAt n (s + 48 + 24) pp pc pl ∗
                                                        n ↦[wms][ pp.toNat ] pre ∗
                                                          n ↦[wms][ (s + 8).toNat ]
                                                              WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ++
                                                                WasmLogic.storeBytes (Wasm.Value.i64 0) 8 ∗
                                                            n ↦[wms][ (s + 128).toNat ]
                                                                WNear.Binary.U128From.u128Bytes 0 0 ∗
                                                              WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                                                    ∃ q rest',
                                                                      ⌜rest'.length = 125⌝ ∗
                                                                        n ↦[wms][ (s + 88).toNat + 4 ]
                                                                            WasmLogic.bytes32 q ++
                                                                                WasmLogic.bytes32 128 ++
                                                                              WasmLogic.bytes32 3 ∗
                                                                          n ↦[wms][ (s + 144).toNat ]
                                                                              WasmLogic.bytes32 q ++
                                                                                  WasmLogic.bytes32 128 ++
                                                                                WasmLogic.bytes32 3 ∗
                                                                            n ↦[wms][ s.toNat ]
                                                                                WasmLogic.bytes32 q ++
                                                                                  WasmLogic.bytes32 3 ∗
                                                                              n ↦[wms][ q.toNat + 3 ] rest' ∗
                                                                                (∃ hl',
                                                                                    WNear.Binary.AllocInv.heapInv n maxP
                                                                                      hl' ((q.toNat, 128) :: live)
                                                                                      (F + 3 + 1)) ∗
                                                                                  ∃ h',
                                                                                    ⌜NearLogic.StorageReadPost h
                                                                                          (pre ++
                                                                                            (WasmLogic.bytes32 L ++
                                                                                              key))
                                                                                          0 st h'⌝ ∗
                                                                                      WNear.Binary.ValueReturn.post n g
                                                                                        ta A
                                                                                        { type := gt,
                                                                                          value := Wasm.Value.i32 s }
                                                                                        s q 3 [34, 48, 34] h'
                                                                                        [Wasm.Value.i32 q,
                                                                                          Wasm.Value.i32 3]
                                                                                        rs) -∗
                                              Φ.normal rs
                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 47 (List.drop 91 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297Expect

`WNear.Binary.BalanceOf297AbsentCall.expect_ok` (hash `000000004f11059d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.expect_ok {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 q L : UInt32) (ob : List UInt8) (hob : ob.length = 12)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
      inst ↪[inst] mi ∗
        NearLogic.credits Cg (44 * cfg.regularOpCost + R) ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
            n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
              n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 q ∗
                n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 128 ∗
                  n ↦[wms][ (s + 88).toNat + 12 ] WasmLogic.bytes32 L ∗
                    n ↦[wms][ (s + 144).toNat ] ob ∗
                      ▷
                        ∀ rs,
                          NearLogic.credits Cg R ∗
                              ⌜rs = []⌝ ∗
                                g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                    n ↦[wms][ (s + 88).toNat + 4 ]
                                        WasmLogic.bytes32 q ++ WasmLogic.bytes32 128 ++ WasmLogic.bytes32 L ∗
                                      n ↦[wms][ (s + 144).toNat ]
                                        WasmLogic.bytes32 q ++ WasmLogic.bytes32 128 ++ WasmLogic.bytes32 L -∗
                            Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 8 (List.drop 120 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297Format

`WNear.Binary.BalanceOf297AbsentCall.format_zero` (hash `0000000056abf64d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.format_zero {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 ptr0 aidx : UInt32) (ob : List UInt8) (maxP hl : ℕ) (live : List (ℕ × ℕ))
  (hs : 416 ≤ s.toNat) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16)
  (hr1 : WNear.Binary.VecFromElem.roomFor hl maxP 128)
  (hr2 :
    ∀ (hl1 : ℕ),
      hl1 = hl ∨ hl1 = WNear.Binary.VecFromElem.grownLen hl 128 →
        WNear.Binary.VecFromElem.roomFor hl1 maxP
          (WNear.Binary.FmtGrow.newCap 0 (WNear.Binary.FmtString.kOf (WNear.Binary.FmtU128.val 0 0))))
  (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
        inst ↪[inst] mi ∗
          NearLogic.credits Cg (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg F 0 0 + R) ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
              WNear.Binary.VecFromElem.stk n (s.toNat - 416) 416 ∗
                n ↦[wms][ (s + 88).toNat ] ob ∗
                  n ↦[wms][ (s + 128).toNat ] WNear.Binary.U128From.u128Bytes 0 0 ∗
                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                      WNear.Binary.AllocFirstFit.vt n 1057464 aidx ta (A 578) ∗
                        WNear.Binary.AllocInv.heapInv n maxP hl live F ∗
                          ▷
                            ∀ rs,
                              (NearLogic.credits Cg R ∗
                                  ⌜rs = []⌝ ∗
                                    g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                      WNear.Binary.VecFromElem.stk n (s.toNat - 416) 416 ∗
                                        n ↦[wms][ (s + 128).toNat ] WNear.Binary.U128From.u128Bytes 0 0 ∗
                                          WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                            WNear.Binary.AllocFirstFit.vt n 1057464 aidx ta (A 578) ∗
                                              ∃ q rest,
                                                ⌜rest.length =
                                                      128 -
                                                        ((WNear.Binary.FmtString.kOf
                                                              (WNear.Binary.FmtU128.val 0 0)).toNat +
                                                          2)⌝ ∗
                                                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                                    n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 q ∗
                                                      n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 128 ∗
                                                        n ↦[wms][ (s + 88).toNat + 12 ]
                                                            WasmLogic.bytes32
                                                              (0 +
                                                                  WNear.Binary.FmtString.kOf
                                                                    (WNear.Binary.FmtU128.val 0 0) +
                                                                2) ∗
                                                          n ↦[wms][ q.toNat ]
                                                              [34] ++
                                                                    WNear.Binary.FmtDigits.decDigits
                                                                      (WNear.Binary.FmtU128.val 0 0) ++
                                                                  [34] ++
                                                                rest ∗
                                                            ∃ hl',
                                                              WNear.Binary.AllocInv.heapInv n maxP hl'
                                                                ((q.toNat, 128) :: live) (F + 1)) -∗
                                Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 7 (List.drop 113 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ParsedSuffix

`WNear.Binary.BalanceOf297AbsentCall.parsed_account_through_cleanup_absent` (hash `000000007b0305ce`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parsed_account_through_cleanup_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (pp pc pl p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob dest tail out head padding old : List UInt8)
  (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16)
  (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8)
  (hold : old.length = 12) (hpadding : pre.length + padding.length = pc.toNat) (hpc : pc ≠ 0)
  (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0)
  (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
  (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hroom : WNear.Binary.LookupMapOps.HeapRoomK 4 len maxP) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) {bud : ℕ} (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
      A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
        WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
          A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
            A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
              A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                  A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                    WNear.Binary.DropVec.dropCode inst mi A ∗
                      A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                        WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                          inst ↪[inst] mi ∗
                            NearLogic.credits Cg
                                (12 * cfg.regularOpCost +
                                  (2112 * cfg.regularOpCost +
                                      WNear.Binary.LookupMapGet.cost399None cfg F pl L h
                                        (pre ++ (WasmLogic.bytes32 L ++ key)) +
                                    (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 3) 0 0 +
                                      (44 * cfg.regularOpCost +
                                        (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                          (660 * cfg.regularOpCost + R)))))) ∗
                              WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s (s + 8) (s + 48) (s + 48 + 24) pp pc pl
                                  (s + 32) p c L idx maxP len ((pp.toNat, pc.toNat) :: live) F pre key rest ob h
                                  [Wasm.Value.i32 (s + 8), Wasm.Value.i32 (s + 48), Wasm.Value.i32 (s + 32)] ∗
                                n ↦[wms][ (s + 88).toNat ] old ∗
                                  WNear.Binary.VecFromElem.stk n (s.toNat - 416) 32 ∗
                                    n ↦[wms][ (s + 100).toNat ] tail ∗
                                      n ↦[wms][ (s + 128).toNat ] dest ∗
                                        WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                          n ↦[wms][ (s + 144).toNat ] out ∗
                                            n ↦[wms][ s.toNat ] head ∗
                                              n ↦[wms][ pp.toNat + pre.length ] padding ∗
                                                ▷
                                                  ((NearLogic.credits Cg R ∗
                                                      g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                        (∃ hl',
                                                            WNear.Binary.AllocInv.heapInv n maxP hl' live
                                                              (F + 3 + 1 + 1 + 1)) ∗
                                                          ∃ h',
                                                            ⌜NearLogic.StorageReadPost h
                                                                  (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st h'⌝ ∗
                                                              NearLogic.mhostPt (h'.selectReturnValue [34, 48, 34])) -∗
                                                    Φ.normal []
                                                      (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2
                                                        (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 71 (List.drop 79 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ParserCompose

`WNear.Binary.BalanceOf297AbsentCall.parser_through_cleanup` (hash `0000000020a5ce42`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 p c L ip ic il idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (key rest ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hic : ic ≠ 0) (hL : L.toNat + 4 ≤ 120)
  (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16) (hstateTail : stateTail.length = 24)
  (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4) (hA : oldA.length = 8)
  (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 6 len maxP) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (400 * cfg.regularOpCost +
                                          (800 * cfg.regularOpCost +
                                              WNear.Binary.BalanceOf297AbsentCall.cost219F cfg (F + 1) h S +
                                            (12 * cfg.regularOpCost +
                                              (2112 * cfg.regularOpCost +
                                                  WNear.Binary.LookupMapGet.cost399None cfg (F + 1 + 1) 1 L h
                                                    (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) +
                                                (17 * cfg.regularOpCost +
                                                    WNear.Binary.ToVec.cost96F cfg (F + 1 + 1 + 3) 0 0 +
                                                  (44 * cfg.regularOpCost +
                                                    (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                      (660 * cfg.regularOpCost + R)))))))) ∗
                                      g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                        WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                          WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                            WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                              n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                NearLogic.mhostPt h ∗
                                                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                                    n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 p ∗
                                                      n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 c ∗
                                                        n ↦[wms][ (s + 88).toNat + 12 ] WasmLogic.bytes32 L ∗
                                                          n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                            n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                              n ↦[wms][ (s + 128).toNat + 8 ] WasmLogic.bytes32 oldC ∗
                                                                n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                  n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                    n ↦[wms][ (s + 32).toNat + 8 ]
                                                                        WasmLogic.bytes32 oldD ∗
                                                                      n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ∗
                                                                        n ↦[wms][ (s + 48).toNat + 4 ]
                                                                            WasmLogic.bytes32 ic ∗
                                                                          n ↦[wms][ (s + 48).toNat + 8 ]
                                                                              WasmLogic.bytes32 il ∗
                                                                            n ↦[wms][ (s + 60).toNat ] contractTail ∗
                                                                              WNear.Binary.AllocInv.block n ip.toNat
                                                                                  ic.toNat ∗
                                                                                WNear.Binary.AllocInv.heapInv n maxP len
                                                                                    ((ip.toNat, ic.toNat) ::
                                                                                      (p.toNat, c.toNat) :: live)
                                                                                    F ∗
                                                                                  n ↦[wms][ p.toNat ] key ∗
                                                                                    n ↦[wms][ p.toNat + key.length ]
                                                                                        rest ∗
                                                                                      n ↦[wms][ (s + 8).toNat ] ob ∗
                                                                                        WNear.Binary.ToVec.tvData n ta
                                                                                            ptr0 (A 759) (A 353) ∗
                                                                                          n ↦[wms][ (s + 144).toNat ]
                                                                                              out ∗
                                                                                            n ↦[wms][ s.toNat ] head ∗
                                                                                              ▷
                                                                                                (NearLogic.credits Cg
                                                                                                      R ∗
                                                                                                    g ↦[wg]
                                                                                                        { type := gt,
                                                                                                          value :=
                                                                                                            Wasm.Value.i32
                                                                                                              (s +
                                                                                                                160) } ∗
                                                                                                      ⋯ ∗ ⋯ -∗
                                                                                                  Φ.normal []
                                                                                                    (WNear.Binary.BalanceOf297AbsentCall.frame
                                                                                                      inst mi s L
                                                                                                      (WNear.Binary.VecFromElem.pair64
                                                                                                        p c)
                                                                                                      (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 114 (List.drop 36 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ParserHandoff

`WNear.Binary.BalanceOf297AbsentCall.parser_handoff` (hash `00000000c2a26165`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_handoff {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg R : ℕ) (s x1 : UInt32)
  (x2 : UInt64) (x3 p c L ip ic il : UInt32) (maxP hl F : ℕ) (live : List (ℕ × ℕ)) (oldA oldB : List UInt8)
  (oldC oldD : UInt32) (hA : oldA.length = 8) (hB : oldB.length = 8) (hc : ic ≠ 0) (hs : s.toNat + 160 ≤ 2 ^ 32)
  (hal : s.toNat % 8 = 0) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.DropVec.dropCode inst mi A ∗
      A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
        NearLogic.credits Cg (400 * cfg.regularOpCost + R) ∗
          n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
            n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 p ∗
              n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 c ∗
                n ↦[wms][ (s + 88).toNat + 12 ] WasmLogic.bytes32 L ∗
                  n ↦[wms][ (s + 128).toNat ] oldA ∗
                    n ↦[wms][ (s + 128).toNat + 8 ] WasmLogic.bytes32 oldC ∗
                      n ↦[wms][ (s + 32).toNat ] oldB ∗
                        n ↦[wms][ (s + 32).toNat + 8 ] WasmLogic.bytes32 oldD ∗
                          n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ∗
                            n ↦[wms][ (s + 48).toNat + 4 ] WasmLogic.bytes32 ic ∗
                              n ↦[wms][ (s + 48).toNat + 8 ] WasmLogic.bytes32 il ∗
                                WNear.Binary.AllocInv.block n ip.toNat ic.toNat ∗
                                  WNear.Binary.AllocInv.heapInv n maxP hl
                                      ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F ∗
                                    ▷
                                      (NearLogic.credits Cg R ∗
                                          n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 0 ∗
                                            n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 p ++ WasmLogic.bytes32 c ∗
                                              n ↦[wms][ (s + 88).toNat + 12 ] WasmLogic.bytes32 L ∗
                                                n ↦[wms][ (s + 128).toNat ] WasmLogic.bytes32 p ++ WasmLogic.bytes32 c ∗
                                                  n ↦[wms][ (s + 128).toNat + 8 ] WasmLogic.bytes32 L ∗
                                                    n ↦[wms][ (s + 32).toNat ]
                                                        WasmLogic.bytes32 p ++ WasmLogic.bytes32 c ∗
                                                      n ↦[wms][ (s + 32).toNat + 8 ] WasmLogic.bytes32 L ∗
                                                        n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ∗
                                                          n ↦[wms][ (s + 48).toNat + 4 ] WasmLogic.bytes32 ic ∗
                                                            n ↦[wms][ (s + 48).toNat + 8 ] WasmLogic.bytes32 il ∗
                                                              WNear.Binary.AllocInv.heapInv n maxP hl
                                                                ((p.toNat, c.toNat) :: live) (F + 1) -∗
                                        Φ.normal []
                                          (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s L
                                            (WNear.Binary.VecFromElem.pair64 p c) (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 32 (List.drop 36 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ParserResult

`WNear.Binary.BalanceOf297AbsentCall.parser_result_resources` (hash `00000000fd7e4212`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_result_resources {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (n : ℕ) (out : UInt32) (a : WNear.AccountId) (ip ic : UInt32)
  (live : List (ℕ × ℕ)) :
  WNear.Binary.FromSliceSpec.okAt n out a ((ip.toNat, ic.toNat) :: live) ⊢
    ∃ p c hl F rest,
      ⌜c ≠ 0 ∧
            (↑a).toUTF8.toList.length = (UInt32.ofNat (↑a).utf8ByteSize).toNat ∧
              (↑a).toUTF8.toList.length + rest.length = c.toNat ∧
                (UInt32.ofNat (↑a).utf8ByteSize).toNat + 4 ≤ 120 ∧ p.toNat + c.toNat ≤ 2 ^ 32⌝ ∗
        n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
          n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
            n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
              n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ∗
                n ↦[wms][ p.toNat ] (↑a).toUTF8.toList ∗
                  n ↦[wms][ p.toNat + (↑a).toUTF8.toList.length ] rest ∗
                    WNear.Binary.AllocInv.heapInv n 2048 hl ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F
```

## Bridge.Functions.BalanceOf297ReadBudget

`WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterState` (hash `986ab76f6c55d06e`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterState (cfg : Wasm.Near.WasmConfig) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (K : ℕ) : Prop :=
  ∀ (h1 : Wasm.NearState),
    NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
      WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h1
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
        K
```

`WNear.Binary.BalanceOf297AbsentCall.balanceReadAfterState_of_budget` (hash `00000000160f0cb7`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.balanceReadAfterState_of_budget (cfg : Wasm.Near.WasmConfig) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (K bud : ℕ) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlim :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hgas : WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterState cfg h st L key K) (h1 : Wasm.NearState) :
  NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
    ∃ st1 bud1,
      h1.storageAccounting = some st1 ∧
        Wasm.Near.withinLimit h1.config.maxStorageKeyLen
              (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
            true ∧
          Near.TrieConstruction.build st1.entries = Except.ok st1.base ∧
            NearLogic.zeroHash ∉ List.map Prod.fst st1.base.witness ∧
              h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) =
                  NearLogic.viewVal st1
                    (Near.TrieOverlay.contractKey h1.context.currentAccountId
                      (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ∧
                NearLogic.ProofBudget h1 st1 bud1 ∧
                  NearLogic.readProofCost
                        (Near.TrieOverlay.contractKey h1.context.currentAccountId
                          (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
                        (h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
                      bud1 ∧
                    h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none ∧
                      WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h1
                          (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
                        K
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_of_budget` (hash `0000000013bff8c0`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_of_budget {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R K : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ))
  (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
  (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16)
  (holdState : oldState.length = 40) (holdContract : oldContract.length = 40) (hdest : dest.length = 16)
  (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len1 : ℕ),
      len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1)
  (hroom :
    ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hgas : WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterState cfg h st L key K) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateRead.stateCode e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost + WNear.Binary.FtTotalSupply.cost219 cfg h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost + K +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg 5 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateRead.pre219 n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live 8) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ReadBudgetF

`WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterStateF` (hash `6e4ffb22d8c0da9f`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterStateF (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (K : ℕ) : Prop :=
  ∀ (h1 : Wasm.NearState),
    NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
      WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h1
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
        K
```

`WNear.Binary.BalanceOf297AbsentCall.balanceReadAfterState_of_budgetF` (hash `00000000a390ebe0`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.balanceReadAfterState_of_budgetF (cfg : Wasm.Near.WasmConfig) (F : ℕ)
  (h : Wasm.NearState) (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (K bud : ℕ)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlim :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hgas : WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterStateF cfg F h st L key K) (h1 : Wasm.NearState) :
  NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
    ∃ st1 bud1,
      h1.storageAccounting = some st1 ∧
        Wasm.Near.withinLimit h1.config.maxStorageKeyLen
              (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
            true ∧
          Near.TrieConstruction.build st1.entries = Except.ok st1.base ∧
            NearLogic.zeroHash ∉ List.map Prod.fst st1.base.witness ∧
              h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) =
                  NearLogic.viewVal st1
                    (Near.TrieOverlay.contractKey h1.context.currentAccountId
                      (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ∧
                NearLogic.ProofBudget h1 st1 bud1 ∧
                  NearLogic.readProofCost
                        (Near.TrieOverlay.contractKey h1.context.currentAccountId
                          (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
                        (h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
                      bud1 ∧
                    h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none ∧
                      WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h1
                          (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
                        K
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_of_budgetF` (hash `0000000078477d62`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_of_budgetF {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R K : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F)
  (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
  (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16)
  (holdState : oldState.length = 40) (holdContract : oldContract.length = 40) (hdest : dest.length = 16)
  (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len1 : ℕ),
      len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1)
  (hroom :
    ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hgas : WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterStateF cfg F h st L key K) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost +
                                            WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost + K +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 1 + 3) 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateReadLenF.pre219F n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) F oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live
                                                                        (F + 1 + 3 + 1 + 1 + 1)) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ReadGas

`WNear.Binary.BalanceOf297AbsentCall.balanceReadGasAfterState_exact` (hash `000000009235055b`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.balanceReadGasAfterState_exact (cfg : Wasm.Near.WasmConfig) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (h1 : Wasm.NearState) :
  NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
    WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h1 (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
      WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_exact_gas` (hash `00000000f20d6a28`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_exact_gas {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (p c L idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (key rest ob oldState oldContract dest out head : List UInt8)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hob : ob.length = 16) (holdState : oldState.length = 40) (holdContract : oldContract.length = 40)
  (hdest : dest.length = 16) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len1 : ℕ),
      len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1)
  (hroom :
    ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateRead.stateCode e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost + WNear.Binary.FtTotalSupply.cost219 cfg h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost +
                                                WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h
                                                  (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg 5 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateRead.pre219 n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live 8) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.storageReadUse_after_read` (hash `000000007391460d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.storageReadUse_after_read {h h1 : Wasm.NearState} {st : Near.TrieOverlay.State}
  {first next : List UInt8} {r : UInt64} (hread : NearLogic.StorageReadPost h first r st h1) (n : ℕ) :
  NearLogic.storageReadUse h1 next n = NearLogic.storageReadUse h next n
```

## Bridge.Functions.BalanceOf297ReadGasF

`WNear.Binary.BalanceOf297AbsentCall.balanceReadGasAfterState_exactF` (hash `00000000ec1f3279`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.balanceReadGasAfterState_exactF (cfg : Wasm.Near.WasmConfig) (F : ℕ)
  (h : Wasm.NearState) (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (h1 : Wasm.NearState) :
  NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
    WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h1 (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
      WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_exact_gasF` (hash `000000000179d57d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_exact_gasF {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (p c L idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F)
  (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
  (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16)
  (holdState : oldState.length = 40) (holdContract : oldContract.length = 40) (hdest : dest.length = 16)
  (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len1 : ℕ),
      len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1)
  (hroom :
    ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost +
                                            WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost +
                                                WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h
                                                  (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 1 + 3) 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateReadLenF.pre219F n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) F oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live
                                                                        (F + 1 + 3 + 1 + 1 + 1)) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297Return

`WNear.Binary.BalanceOf297AbsentCall.return_vec` (hash `000000000b35889c`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.return_vec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg R : ℕ)
  (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 q L : UInt32) (bs ob : List UInt8)
  (hbs : bs.length = L.toNat) (hob : ob.length = 8) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (_hframe : s.toNat + 160 ≤ 2 ^ 32) (h : Wasm.NearState)
  (hlim : Wasm.Near.withinLimit h.config.maxReturnLen L.toNat = true) (hpos : 0 < L.toNat)
  (s8 s12 w0 w4 w8 w12 : UInt32) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
      A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
        A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
          WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
            inst ↪[inst] mi ∗
              NearLogic.credits Cg (306 * cfg.regularOpCost + NearLogic.valueReturnUse h L.toNat + R) ∗
                n ↦[wms][ s.toNat ] ob ∗
                  n ↦[wms][ (s + 144).toNat ] WasmLogic.bytes32 q ++ WasmLogic.bytes32 128 ++ WasmLogic.bytes32 L ∗
                    WNear.Binary.ValueReturn.pre n g ta A { type := gt, value := Wasm.Value.i32 s } s q L bs s8 s12 w0
                        w4 w8 w12 h [Wasm.Value.i32 q, Wasm.Value.i32 L] ∗
                      ▷
                        ∀ rs,
                          NearLogic.credits Cg R ∗
                              n ↦[wms][ s.toNat ] WasmLogic.bytes32 q ++ WasmLogic.bytes32 L ∗
                                n ↦[wms][ (s + 144).toNat ]
                                    WasmLogic.bytes32 q ++ WasmLogic.bytes32 128 ++ WasmLogic.bytes32 L ∗
                                  WNear.Binary.ValueReturn.post n g ta A { type := gt, value := Wasm.Value.i32 s } s q L
                                    bs h [Wasm.Value.i32 q, Wasm.Value.i32 L] rs -∗
                            Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 10 (List.drop 128 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297Room

`WNear.Binary.BalanceOf297AbsentCall.room_after_state` (hash `00000000a978a50d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.room_after_state (len maxP : ℕ)
  (h : WNear.Binary.LookupMapOps.HeapRoomK 6 len maxP) :
  WNear.Binary.VecFromElem.roomFor len maxP 29 ∧
    (∀ (len1 : ℕ),
        len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1) ∧
      ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_six_grows` (hash `000000003e822194`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_six_grows {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (p c L idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (key rest ob oldState oldContract dest out head : List UInt8)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
  (hob : ob.length = 16) (holdState : oldState.length = 40) (holdContract : oldContract.length = 40)
  (hdest : dest.length = 16) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 6 len maxP) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateRead.stateCode e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost + WNear.Binary.FtTotalSupply.cost219 cfg h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost +
                                                WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h
                                                  (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg 5 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateRead.pre219 n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live 8) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297RoomF

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_six_growsF` (hash `00000000bfd473d8`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_six_growsF {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (p c L idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F)
  (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
  (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16)
  (holdState : oldState.length = 40) (holdContract : oldContract.length = 40) (hdest : dest.length = 16)
  (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 6 len maxP) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
          (h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
      true)
  (hnone : h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost +
                                            WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost +
                                                WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h
                                                  (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 1 + 3) 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateReadLenF.pre219F n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) F oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live
                                                                        (F + 1 + 3 + 1 + 1 + 1)) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297StateBridge

`WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterState` (hash `19b737fce7c552c2`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterState (cfg : Wasm.Near.WasmConfig) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (K : ℕ) : Prop :=
  ∀ (h1 : Wasm.NearState),
    NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
      ∃ st1 bud,
        h1.storageAccounting = some st1 ∧
          Wasm.Near.withinLimit h1.config.maxStorageKeyLen
                (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
              true ∧
            Near.TrieConstruction.build st1.entries = Except.ok st1.base ∧
              NearLogic.zeroHash ∉ List.map Prod.fst st1.base.witness ∧
                h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) =
                    NearLogic.viewVal st1
                      (Near.TrieOverlay.contractKey h1.context.currentAccountId
                        (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ∧
                  NearLogic.ProofBudget h1 st1 bud ∧
                    NearLogic.readProofCost
                          (Near.TrieOverlay.contractKey h1.context.currentAccountId
                            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
                          (h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
                        bud ∧
                      h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none ∧
                        WNear.Binary.LookupMapGet.cost399None cfg 2 1 L h1
                            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
                          K
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_absent` (hash `0000000000b3982f`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_absent {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R K : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ))
  (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
  (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16)
  (holdState : oldState.length = 40) (holdContract : oldContract.length = 40) (hdest : dest.length = 16)
  (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len1 : ℕ),
      len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1)
  (hroom :
    ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage WNear.stateKey =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey))
  (hproof :
    NearLogic.ProofBudget h st
      (NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
        (h.storage WNear.stateKey)))
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hnext : WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterState cfg h st L key K) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateRead.stateCode e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost + WNear.Binary.FtTotalSupply.cost219 cfg h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost + K +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg 5 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateRead.pre219 n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live 8) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297StateBridgeF

`WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterStateF` (hash `ce3676af370c6520`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterStateF (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) (L : UInt32) (key : List UInt8) (K : ℕ) : Prop :=
  ∀ (h1 : Wasm.NearState),
    NearLogic.StorageReadPost h WNear.stateKey 0 st h1 →
      ∃ st1 bud,
        h1.storageAccounting = some st1 ∧
          Wasm.Near.withinLimit h1.config.maxStorageKeyLen
                (List.length (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) =
              true ∧
            Near.TrieConstruction.build st1.entries = Except.ok st1.base ∧
              NearLogic.zeroHash ∉ List.map Prod.fst st1.base.witness ∧
                h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) =
                    NearLogic.viewVal st1
                      (Near.TrieOverlay.contractKey h1.context.currentAccountId
                        (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ∧
                  NearLogic.ProofBudget h1 st1 bud ∧
                    NearLogic.readProofCost
                          (Near.TrieOverlay.contractKey h1.context.currentAccountId
                            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)))
                          (h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key))) ≤
                        bud ∧
                      h1.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) = none ∧
                        WNear.Binary.LookupMapGet.cost399None cfg (F + 1) 1 L h1
                            (WNear.accountsPrefix ++ (WasmLogic.bytes32 L ++ key)) ≤
                          K
```

`WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_absentF` (hash `0000000025a219db`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_absentF {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R K : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F)
  (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
  (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hob : ob.length = 16)
  (holdState : oldState.length = 40) (holdContract : oldContract.length = 40) (hdest : dest.length = 16)
  (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len1 : ℕ),
      len1 = len ∨ len1 = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len1 maxP 1)
  (hroom :
    ∀ (len1 : ℕ), WNear.Binary.StateReadLen.LenStep len 29 1 len1 → WNear.Binary.LookupMapOps.HeapRoomK 4 len1 maxP)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage WNear.stateKey =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey))
  (hproof :
    NearLogic.ProofBudget h st
      (NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
        (h.storage WNear.stateKey)))
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hnext : WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterStateF cfg F h st L key K) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n maxP inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg
                                        (800 * cfg.regularOpCost +
                                            WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S +
                                          (12 * cfg.regularOpCost +
                                            (2112 * cfg.regularOpCost + K +
                                              (17 * cfg.regularOpCost + WNear.Binary.ToVec.cost96F cfg (F + 1 + 3) 0 0 +
                                                (44 * cfg.regularOpCost +
                                                  (306 * cfg.regularOpCost + NearLogic.valueReturnUse h 3 +
                                                    (660 * cfg.regularOpCost + R))))))) ∗
                                      WNear.Binary.StateReadLenF.pre219F n g ta A gt s (s + 88) idx maxP len
                                          ((p.toNat, c.toNat) :: live) F oldState h [Wasm.Value.i32 (s + 88)] ∗
                                        n ↦[wms][ (s + 48).toNat ] oldContract ∗
                                          n ↦[wms][ (s + 32).toNat ]
                                              WasmLogic.bytes32 p ++ (WasmLogic.bytes32 c ++ WasmLogic.bytes32 L) ∗
                                            n ↦[wms][ p.toNat ] key ∗
                                              n ↦[wms][ p.toNat + key.length ] rest ∗
                                                n ↦[wms][ (s + 8).toNat ] ob ∗
                                                  n ↦[wms][ (s + 128).toNat ] dest ∗
                                                    WNear.Binary.ToVec.tvData n ta ptr0 (A 759) (A 353) ∗
                                                      n ↦[wms][ (s + 144).toNat ] out ∗
                                                        n ↦[wms][ s.toNat ] head ∗
                                                          ▷
                                                            ((NearLogic.credits Cg R ∗
                                                                g ↦[wg]
                                                                    { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                  (∃ hl,
                                                                      WNear.Binary.AllocInv.heapInv n maxP hl live
                                                                        (F + 1 + 3 + 1 + 1 + 1)) ∗
                                                                    ∃ h1,
                                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st
                                                                            h1⌝ ∗
                                                                        ∃ st1 h2,
                                                                          ⌜NearLogic.StorageReadPost h1
                                                                                (WNear.accountsPrefix ++
                                                                                  (WasmLogic.bytes32 L ++ key))
                                                                                0 st1 h2⌝ ∗
                                                                            NearLogic.mhostPt
                                                                              (h2.selectReturnValue [34, 48, 34])) -∗
                                                              Φ.normal []
                                                                (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1
                                                                  x2 (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40)) []
      (List.take 82 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297StateRead

`WNear.Binary.BalanceOf297AbsentCall.state_read_and_unwrap` (hash `00000000a1d7673b`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_read_and_unwrap {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 18 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (ob old : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 40) (hold : old.length = 40) (h : Wasm.NearState)
  (S : WNear.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len' maxP 1)
  (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage WNear.stateKey =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey))
  (hproof :
    NearLogic.ProofBudget h st
      (NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
        (h.storage WNear.stateKey)))
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.StateRead.stateCode e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            inst ↪[inst] mi ∗
              NearLogic.credits Cg (800 * cfg.regularOpCost + WNear.Binary.FtTotalSupply.cost219 cfg h S + R) ∗
                WNear.Binary.StateRead.pre219 n g ta A gt s (s + 88) idx maxP len live ob h [Wasm.Value.i32 (s + 88)] ∗
                  n ↦[wms][ (s + 48).toNat ] old ∗
                    ▷
                      ∀ rs,
                        (NearLogic.credits Cg R ∗
                            ⌜rs = []⌝ ∗
                              g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                  WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                    WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                      n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                        ∃ pv p pad len',
                                          ⌜pad.length = 4 ∧ WNear.Binary.StateReadLen.LenStep len 29 1 len'⌝ ∗
                                            n ↦[wms][ (s + 88).toNat ]
                                                WNear.Binary.StateReadModel.contractBytes S p ++ pad ∗
                                              n ↦[wms][ (s + 48).toNat ]
                                                  WNear.Binary.StateReadModel.contractBytes S p ++ pad ∗
                                                WNear.Binary.AllocInv.heapInv n maxP len'
                                                    (((p.toNat, 1) :: (pv.toNat, 29) :: live).erase (pv.toNat, 29)) 2 ∗
                                                  n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
                                                    ∃ h',
                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st h'⌝ ∗
                                                        NearLogic.mhostPt h') -∗
                          Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 11 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297StateReadF

`WNear.Binary.BalanceOf297AbsentCall.state_read_and_unwrapF` (hash `0000000078d964f9`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_read_and_unwrapF {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 18 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (ob old : List UInt8)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 40)
  (hold : old.length = 40) (h : Wasm.NearState) (S : WNear.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hr1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hr2 :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len' maxP 1)
  (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage WNear.stateKey =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey))
  (hproof :
    NearLogic.ProofBudget h st
      (NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
        (h.storage WNear.stateKey)))
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            inst ↪[inst] mi ∗
              NearLogic.credits Cg
                  (800 * cfg.regularOpCost + WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S + R) ∗
                WNear.Binary.StateReadLenF.pre219F n g ta A gt s (s + 88) idx maxP len live F ob h
                    [Wasm.Value.i32 (s + 88)] ∗
                  n ↦[wms][ (s + 48).toNat ] old ∗
                    ▷
                      ∀ rs,
                        (NearLogic.credits Cg R ∗
                            ⌜rs = []⌝ ∗
                              g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                  WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                    WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                      n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                        ∃ pv p pad len',
                                          ⌜pad.length = 4 ∧ WNear.Binary.StateReadLen.LenStep len 29 1 len'⌝ ∗
                                            n ↦[wms][ (s + 88).toNat ]
                                                WNear.Binary.StateReadModel.contractBytes S p ++ pad ∗
                                              n ↦[wms][ (s + 48).toNat ]
                                                  WNear.Binary.StateReadModel.contractBytes S p ++ pad ∗
                                                WNear.Binary.AllocInv.heapInv n maxP len'
                                                    (((p.toNat, 1) :: (pv.toNat, 29) :: live).erase (pv.toNat, 29))
                                                    (F + 1) ∗
                                                  n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
                                                    ∃ h',
                                                      ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st h'⌝ ∗
                                                        NearLogic.mhostPt h') -∗
                          Φ.normal rs (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 11 (List.drop 68 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOfAbsent

`WNear.Binary.BalanceOfAbsent.f415_none` (hash `000000008922d795`)

```lean
theorem WNear.Binary.BalanceOfAbsent.f415_none {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out m pp pc pl v p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob : List UInt8) (hs : 352 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4)
  (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32)
  (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hroom : WNear.Binary.LookupMapOps.HeapRoomK 2 len maxP) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) {bud : ℕ} (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) :
  WNear.Binary.BalanceOfAbsent.code415 e n maxP inst mi A mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f415 Cg
      (WNear.Binary.BalanceOfAbsent.pre415 n g ta A gt s out m (m + 24) pp pc pl v p c L idx maxP len live F pre key
        rest ob h)
      (fun x =>
        1000 * cfg.regularOpCost +
          WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)))
      (WNear.Binary.BalanceOfAbsent.post415 n g ta A gt s out (m + 24) pp pc pl v p c L idx maxP len live F pre
        (NearLogic.StorageReadPost h (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st))
```

## Bridge.Functions.BalanceOfCallerAbsent

`WNear.Binary.BalanceOfAbsent.f293_none` (hash `00000000be1e1d4c`)

```lean
theorem WNear.Binary.BalanceOfAbsent.f293_none {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out m pp pc pl v p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key rest ob : List UInt8) (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
  (hrest : key.length + rest.length = c.toNat) (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4)
  (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32)
  (hp : p.toNat + c.toNat ≤ 2 ^ 32) (hroom : WNear.Binary.LookupMapOps.HeapRoomK 2 len maxP) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) {bud : ℕ} (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) :
  WNear.Binary.BalanceOfAbsent.code293 e n maxP inst mi A mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f293 Cg
      (WNear.Binary.BalanceOfAbsent.pre293 n g ta A gt s out m (m + 24) pp pc pl v p c L idx maxP len live F pre key
        rest ob h)
      (fun x =>
        2000 * cfg.regularOpCost +
          WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)))
      (WNear.Binary.BalanceOfAbsent.post293 n g ta A gt s out (m + 24) pp pc pl v p c L idx maxP len live F pre
        (NearLogic.StorageReadPost h (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st))
```

## Bridge.Functions.BorshBytesF

`WNear.Binary.BorshBytesF.f315_spec` (hash `000000009d687b75`)

```lean
theorem WNear.Binary.BorshBytesF.f315_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 13 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (s out r q m idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (ob hd4 data : List UInt8) (hob : ob.length = 16)
  (hhd : hd4.length = 4) (hL : Wasm.Memory.decodeLE hd4 = data.length) (hL0 : 0 < data.length)
  (hL28 : data.length < 2 ^ 28) (hroom : WNear.Binary.VecFromElem.roomFor len maxP (UInt32.ofNat data.length))
  (hs : 160 ≤ s.toNat) (hmL : 4 + data.length ≤ m.toNat) (hq : q.toNat + 4 + data.length ≤ 2 ^ 32)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
  WNear.Binary.BorshBytesF.bytesCode n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f315 Cg
      (WNear.Binary.BorshBytesF.pre315 n g gt s out r q m idx ta (A 578) maxP len live F ob hd4 data)
      (fun x =>
        53 * cfg.regularOpCost +
          (260 * cfg.regularOpCost + WNear.Binary.BorshVecF.cost374 cfg F (UInt32.ofNat data.length)))
      (WNear.Binary.BorshBytesF.post315 n g gt s out r q m idx ta (A 578) maxP len live F hd4 data)
```

`WNear.Binary.BorshBytesF.f316_spec` (hash `000000003c383712`)

```lean
theorem WNear.Binary.BorshBytesF.f316_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 12 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (s out r q m idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (ob hd4 data : List UInt8) (hob : ob.length = 16)
  (hhd : hd4.length = 4) (hL : Wasm.Memory.decodeLE hd4 = data.length) (hL0 : 0 < data.length)
  (hL28 : data.length < 2 ^ 28) (hroom : WNear.Binary.VecFromElem.roomFor len maxP (UInt32.ofNat data.length))
  (hs : 144 ≤ s.toNat) (hmL : 4 + data.length ≤ m.toNat) (hq : q.toNat + 4 + data.length ≤ 2 ^ 32)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
  WNear.Binary.BorshBytesF.bytesCode n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f316 Cg
      (WNear.Binary.BorshBytesF.pre316 n g gt s out r q m idx ta (A 578) maxP len live F ob hd4 data)
      (fun x => 260 * cfg.regularOpCost + WNear.Binary.BorshVecF.cost374 cfg F (UInt32.ofNat data.length))
      (WNear.Binary.BorshBytesF.post316 n g gt s out r q m idx ta (A 578) maxP len live F hd4 data)
```

## Bridge.Functions.BorshContractF

`WNear.Binary.BorshContractF.f161_spec` (hash `00000000830bf3ed`)

```lean
theorem WNear.Binary.BorshContractF.f161_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 16 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (s out q m idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (o0 o8 hd4 pre b0 b1 c0 : List UInt8)
  (ho0 : o0.length = 4) (ho8 : o8.length = 40) (hhd : hd4.length = 4) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
  (hc0 : c0.length = 8) (hL : Wasm.Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length) (hL28 : pre.length < 2 ^ 28)
  (hroom : WNear.Binary.VecFromElem.roomFor len maxP (UInt32.ofNat pre.length)) (hs : 496 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hmL : m.toNat = 4 + pre.length + 24) (hq : q.toNat + 4 + pre.length + 24 ≤ 2 ^ 32)
  (hout : out.toNat + 48 ≤ 2 ^ 32) :
  WNear.Binary.BorshContractF.sliceCode n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f161 Cg
      (WNear.Binary.BorshContractF.pre161 n g gt s out q m idx ta (A 578) maxP len live F o0 o8 hd4 pre b0 b1 c0)
      (fun x => WNear.Binary.BorshContractF.cost161 cfg F (UInt32.ofNat pre.length))
      (WNear.Binary.BorshContractF.post161 n g gt s out q idx ta (A 578) maxP len live F hd4 pre b0 b1 c0)
```

`WNear.Binary.BorshContractF.f162_spec` (hash `000000006dfab669`)

```lean
theorem WNear.Binary.BorshContractF.f162_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 15 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (s out r q m idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (o0 o8 hd4 pre b0 b1 c0 : List UInt8)
  (ho0 : o0.length = 4) (ho8 : o8.length = 40) (hhd : hd4.length = 4) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
  (hc0 : c0.length = 8) (hL : Wasm.Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length) (hL28 : pre.length < 2 ^ 28)
  (hroom : WNear.Binary.VecFromElem.roomFor len maxP (UInt32.ofNat pre.length)) (hs : 352 ≤ s.toNat)
  (hmL : 4 + pre.length + 24 ≤ m.toNat) (hq : q.toNat + 4 + pre.length + 24 ≤ 2 ^ 32) (hout : out.toNat + 48 ≤ 2 ^ 32)
  (hr : r.toNat + 8 ≤ 2 ^ 32) :
  WNear.Binary.BorshContractF.contractCode n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f162 Cg
      (WNear.Binary.BorshContractF.pre162 n g gt s out r q m idx ta (A 578) maxP len live F o0 o8 hd4 pre b0 b1 c0)
      (fun x =>
        93 * cfg.regularOpCost + WNear.Binary.BorshFTF.cost425 cfg F (UInt32.ofNat pre.length) +
            654 * cfg.regularOpCost +
          654 * cfg.regularOpCost)
      (WNear.Binary.BorshContractF.post162 n g gt s out r q m idx ta (A 578) maxP len live F hd4 pre b0 b1 c0)
```

## Bridge.Functions.BorshFTF

`WNear.Binary.BorshFTF.f425_spec` (hash `000000006fb47f5f`)

```lean
theorem WNear.Binary.BorshFTF.f425_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 14 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (s out r q m idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (o0 o8 hd4 pre b0 b1 c0 : List UInt8)
  (ho0 : o0.length = 4) (ho8 : o8.length = 36) (hhd : hd4.length = 4) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
  (hc0 : c0.length = 8) (hL : Wasm.Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length) (hL28 : pre.length < 2 ^ 28)
  (hroom : WNear.Binary.VecFromElem.roomFor len maxP (UInt32.ofNat pre.length)) (hs : 256 ≤ s.toNat)
  (hmL : 4 + pre.length + 24 ≤ m.toNat) (hq : q.toNat + 4 + pre.length + 24 ≤ 2 ^ 32) (hout : out.toNat + 44 ≤ 2 ^ 32)
  (hr : r.toNat + 8 ≤ 2 ^ 32) :
  WNear.Binary.BorshFTF.ftCode n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f425 Cg
      (WNear.Binary.BorshFTF.pre425 n g gt s out r q m idx ta (A 578) maxP len live F o0 o8 hd4 pre b0 b1 c0)
      (fun x => WNear.Binary.BorshFTF.cost425 cfg F (UInt32.ofNat pre.length))
      (WNear.Binary.BorshFTF.post425 n g gt s out r q m idx ta (A 578) maxP len live F hd4 pre b0 b1 c0)
```

## Bridge.Functions.BorshVecF

`WNear.Binary.BorshVecF.f374_spec` (hash `00000000d250d9cd`)

```lean
theorem WNear.Binary.BorshVecF.f374_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 11 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (s out src c idx : UInt32) (maxP len : ℕ)
  (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (ob sb : List UInt8) (hob : ob.length = 12)
  (hsb : sb.length = c.toNat) (hs : 80 ≤ s.toNat) (hc0 : 0 < c.toNat) (hc28 : c.toNat < 2 ^ 28)
  (hr : WNear.Binary.VecFromElem.roomFor len maxP c) (hsrc : src.toNat + c.toNat ≤ 2 ^ 32)
  (hout : out.toNat + 12 ≤ 2 ^ 32) :
  WNear.Binary.VecWithCap.vecCode2 n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f374 Cg
      (WNear.Binary.BorshVecF.pre374 n g gt s out src c idx ta (A 578) maxP len live F ob sb)
      (fun x => WNear.Binary.BorshVecF.cost374 cfg F c)
      (WNear.Binary.BorshVecF.post374 n g gt s out src idx ta (A 578) maxP len live F sb)
```

## Bridge.Functions.FromSliceSpec

`WNear.Binary.FromSliceSpec.AcceptContract` (hash `37a2beaca78490cb`)

```lean
def WNear.Binary.FromSliceSpec.AcceptContract {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (S K0 K1 X : ℕ) : Prop :=
  fun X =>
    ∀ (cfg : Wasm.Near.RuntimeConfig) (h0 : Wasm.NearState) (lim : Wasm.ExecLimits) (d : ℕ),
      d + 64 < lim.maxCallDepth →
        ∀ (Cg : ℕ) (gt : Wasm.GlobalType) (sp out rd ptr idx : UInt32) (bs ob : List UInt8)
          (hl F : ℕ) (live : List (ℕ × ℕ)) (a : WNear.AccountId),
          S ≤ sp.toNat →
            sp.toNat % 16 = 0 →
              ptr.toNat + bs.length < 2 ^ 32 →
                bs.length + 1 < 2 ^ 28 →
                  out.toNat + 16 ≤ 2 ^ 32 →
                    ob.length = 16 →
                      rd.toNat + 12 ≤ 2 ^ 32 →
                        WNear.Binary.SerdeStructArr.roomS hl 2048 →
                          WNear.Call.decode "ft_balance_of" bs = some (WNear.Call.ftBalanceOf a) →
                            WNear.Binary.FromSliceSpec.AcceptCallees cfg h0 lim Cg gt (sp - 64)
                                ptr idx bs F K0 K1 X →
                              ⊢
                                WNear.Binary.FromSliceSpec.codeCtx cfg h0 -∗
                                  NearLogic.MFunSpec cfg.wasm lim d WNear.Binary.types[14]! 0
                                    WNear.Binary.wInst WNear.Binary.f66 Cg
                                    (WNear.Binary.FromSliceSpec.pre66 S gt sp out rd ptr idx bs ob
                                      hl F live)
                                    (fun x => (K0 + K1 * bs.length) * cfg.wasm.regularOpCost + X)
                                    (WNear.Binary.FromSliceSpec.post66 S gt sp rd ptr idx bs
                                      (WNear.Binary.FromSliceSpec.okAt 0 out a live))
```

`WNear.Binary.FromSliceSpec.RejectContract` (hash `51fa1b6f9d95fc7c`)

```lean
def WNear.Binary.FromSliceSpec.RejectContract {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (S : ℕ) :
  Prop :=
  fun S =>
    ∀ (cfg : Wasm.Near.RuntimeConfig) (h0 : Wasm.NearState) (lim : Wasm.ExecLimits) (d : ℕ),
      d + 64 < lim.maxCallDepth →
        ∀ (gt : Wasm.GlobalType) (sp out rd ptr idx : UInt32) (bs ob : List UInt8) (hl F : ℕ)
          (live : List (ℕ × ℕ)),
          S ≤ sp.toNat →
            sp.toNat % 16 = 0 →
              ptr.toNat + bs.length < 2 ^ 32 →
                bs.length + 1 < 2 ^ 28 →
                  out.toNat + 16 ≤ 2 ^ 32 →
                    ob.length = 16 →
                      rd.toNat + 12 ≤ 2 ^ 32 →
                        WNear.Binary.SerdeErrBox.roomFor4 hl 2048 20 →
                          WNear.Call.decode "ft_balance_of" bs = none →
                            ∃ K,
                              ∀ (Cg : ℕ),
                                ⊢
                                  WNear.Binary.FromSliceSpec.codeCtx cfg h0 -∗
                                    NearLogic.MFunSpec cfg.wasm lim d WNear.Binary.types[14]! 0
                                      WNear.Binary.wInst WNear.Binary.f66 Cg
                                      (WNear.Binary.FromSliceSpec.pre66 S gt sp out rd ptr idx bs
                                        ob hl F live)
                                      (fun x => K)
                                      (WNear.Binary.FromSliceSpec.post66 S gt sp rd ptr idx bs
                                        (WNear.Binary.FromSliceSpec.errAt 0 out live))
```

`WNear.Binary.FromSliceSpec.okAt` (hash `51e1b053719d9a84`)

```lean
def WNear.Binary.FromSliceSpec.okAt {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n : ℕ) (out : UInt32)
  (a : WNear.AccountId) (live : List (ℕ × ℕ)) : Iris.IProp GF :=
  fun live =>
    iprop(∃ p cap hl' F',
        ⌜p ≠ 0 ∧ (↑a).utf8ByteSize ≤ cap.toNat⌝ ∗
          n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
            n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
              n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 cap ∗
                n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ∗
                  n ↦[wms][ p.toNat ] (↑a).toUTF8.toList ∗
                    WNear.Binary.AllocInv.block n (p.toNat + (↑a).utf8ByteSize)
                        (cap.toNat - (↑a).utf8ByteSize) ∗
                      WNear.Binary.AllocInv.heapInv n 2048 hl' ((p.toNat, cap.toNat) :: live) F')
```

## Bridge.Functions.LookupMapGet399None

`WNear.Binary.LookupMapGet.f399_none` (hash `00000000fc7886ca`)

```lean
theorem WNear.Binary.LookupMapGet.f399_none {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out m pp pc pl v p c L idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key ob : List UInt8) (hs : 304 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hob : ob.length = 24) (hout : out.toNat + 24 ≤ 2 ^ 32) (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat)
  (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
  (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 2 len maxP) (h : Wasm.NearState) (st : Near.TrieOverlay.State) {bud : ℕ}
  (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ (WasmLogic.bytes32 L ++ key)).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) =
      NearLogic.viewVal st
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key))))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost
        (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ (WasmLogic.bytes32 L ++ key)))
        (h.storage (pre ++ (WasmLogic.bytes32 L ++ key))) ≤
      bud)
  (hnone : h.storage (pre ++ (WasmLogic.bytes32 L ++ key)) = none) :
  WNear.Binary.LookupMapGet.code399 e n maxP inst mi A mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f399 Cg
      (WNear.Binary.LookupMapGet.pre399 n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key ob h)
      (fun x => WNear.Binary.LookupMapGet.cost399None cfg F pl L h (pre ++ (WasmLogic.bytes32 L ++ key)))
      (WNear.Binary.LookupMapGet.post399None n g ta A gt s out m pp pc pl v p c L idx maxP len live F pre key
        (NearLogic.StorageReadPost h (pre ++ (WasmLogic.bytes32 L ++ key)) 0 st))
```

## Bridge.Functions.LookupMapGetNone

`WNear.Binary.LookupMapGet.f400_none` (hash `0000000022b35359`)

```lean
theorem WNear.Binary.LookupMapGet.f400_none {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out m pp pc pl kp kl idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hF : WNear.Binary.VecWithCap.okG F) (pre key ob : List UInt8) (hs : 224 ≤ s.toNat) (hal : s.toNat % 8 = 0)
  (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32) (hpre : pre.length = pl.toNat) (hkey : key.length = kl.toNat)
  (hl : pl.toNat + kl.toNat ≤ 4096) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
  (hkp : kp.toNat + kl.toNat ≤ 2 ^ 32) (hr : WNear.Binary.VecFromElem.roomFor len maxP (pl + kl)) (h : Wasm.NearState)
  (st : Near.TrieOverlay.State) {bud : ℕ} (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen (pre ++ key).length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage (pre ++ key) =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ key)))
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId (pre ++ key))
        (h.storage (pre ++ key)) ≤
      bud)
  (hnone : h.storage (pre ++ key) = none) :
  WNear.Binary.LookupMapGet.code400 e n maxP inst mi A mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f400 Cg
      (WNear.Binary.LookupMapGet.pre400 n g ta A gt s out m pp pc pl kp kl idx maxP len live F pre key ob h)
      (fun x => WNear.Binary.LookupMapGet.cost400None cfg F pl kl h (pre ++ key))
      (WNear.Binary.LookupMapGet.post400None n g ta A gt s out m pp pc pl kp kl idx maxP len live F pre key
        (NearLogic.StorageReadPost h (pre ++ key) 0 st))
```

## Bridge.Functions.LookupMapOps

`WNear.Binary.LookupMapOps.HeapRoomK` (hash `eac35efe45334ec3`)

```lean
def WNear.Binary.LookupMapOps.HeapRoomK (k len maxP : ℕ) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + k * 65536 ≤ maxP * 65536 ∧ len + (k + 1) * 65536 ≤ 2 ^ 32
```

## Bridge.Functions.ScratchGrow

`WNear.Binary.ScratchGrow.roomRes` (hash `379cc68a65804101`)

```lean
def WNear.Binary.ScratchGrow.roomRes (hl maxP : ℕ) (cap len k : UInt32) : Prop :=
  ¬WNear.Binary.ScratchGrow.fits cap len k →
    WNear.Binary.VecFromElem.roomFor hl maxP (WNear.Binary.VecGrow.growCap cap (len + k))
```

## Bridge.Functions.SerdeStructObjKeyState

`WNear.Binary.SerdeStructObjKeyState.KeyConditions` (hash `cb18d8da05f5e7d5`)

```lean
def WNear.Binary.SerdeStructObjKeyState.KeyConditions (cfg : Wasm.Near.WasmConfig) (maxP : ℕ) (bs : List UInt8)
  (B : WNear.Binary.SerdeStructObjKeyState.Bounds) (K : ℕ → ℕ) : Prop :=
  ∀ (first : Bool) (i q : ℕ) (key : String) (rest : List UInt8) (hl F : ℕ) (cap : UInt32),
    i ≤ bs.length →
      WNear.Binary.SerdeNextKey.keyQ first bs i = some q →
        NearInterface.Json.stringBody (List.drop q bs) [] = some (some key, rest) →
          B i hl F cap →
            cap.toNat < 2 ^ 25 →
              hl % 65536 = 0 →
                0 < hl →
                  WNear.Binary.SerdeKeyReuse.keyRoom maxP hl cap (List.drop q bs) ∧
                    WNear.Binary.SerdeKeyReuse.keyCost cfg F cap bs key.toUTF8.toList rest q ≤
                        K q ∧
                      ∀ (hl' : ℕ),
                        hl ≤ hl' →
                          hl' ≤
                              hl +
                                WNear.Binary.ScratchGrow.growthPages cap 0
                                    (WNear.Binary.ParseStrSuccess.appendChunks (List.drop q bs)
                                      []) *
                                  65536 →
                            B (bs.length - rest.length) hl'
                              (WNear.Binary.ScratchGrow.endFreeBound F cap 0
                                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop q bs) []))
                              (WNear.Binary.ScratchGrow.endState cap 0
                                  (WNear.Binary.ParseStrSuccess.appendChunks (List.drop q bs)
                                    [])).1
```

## Bridge.Functions.SerdeStructObjState

`WNear.Binary.SerdeStructObjState.IgnoreHyp` (hash `cb6e804238fdbe6f`)

```lean
def WNear.Binary.SerdeStructObjState.IgnoreHyp {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (inst : ℕ) (mi : Wasm.ModuleInst) (n g Cg : ℕ)
  (gt : Wasm.GlobalType) (de ptr : UInt32) (bs : List UInt8) (ign : List UInt8 → Option (Unit × List UInt8)) (K : ℕ → ℕ)
  (J : WNear.Binary.SerdeStructObjState.MemberState) (Cd : Iris.IProp GF) : Prop :=
  fun Cd =>
    ∀ (d : ℕ) (s : UInt32) (i : ℕ) (rest : List UInt8) (seen : Option WNear.AccountId),
      d + 40 < lim.maxCallDepth →
        304 ≤ s.toNat →
          s.toNat + 64 ≤ 2 ^ 32 →
            i ≤ bs.length →
              bs[i + WNear.Binary.SerdeRead.wsLen (List.drop i bs)]? = some 58 →
                ign (List.drop (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) bs) =
                    some ((), rest) →
                  Cd ⊢
                    NearLogic.MFunSpec cfg lim d WNear.Binary.types[32]! inst mi WNear.Binary.f201
                      Cg
                      (fun args =>
                        iprop(⌜args = [Wasm.Value.i32 (s + 32)]⌝ ∗
                            n ↦[wms][ s.toNat + 32 ] WasmLogic.bytes32 de ∗
                              g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                WNear.Binary.VecFromElem.stk n (s.toNat - 304) 304 ∗
                                  WNear.Binary.SerdeRead.rd n de ptr bs i ∗
                                    WNear.Binary.SerdeStructObjState.seenRes n s J i seen))
                      (fun x =>
                        (240 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop i bs)) *
                            cfg.regularOpCost +
                          K (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1))
                      fun x rs =>
                      iprop(⌜rs = [Wasm.Value.i32 0]⌝ ∗
                          n ↦[wms][ s.toNat + 32 ] WasmLogic.bytes32 de ∗
                            g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                              WNear.Binary.VecFromElem.stk n (s.toNat - 304) 304 ∗
                                WNear.Binary.SerdeRead.rd n de ptr bs (bs.length - rest.length) ∗
                                  WNear.Binary.SerdeStructObjState.seenRes n s J
                                    (bs.length - rest.length) seen)
```

## Bridge.Functions.SerdeStructObjValueState

`WNear.Binary.SerdeStructObjValueState.ValueConditions` (hash `6157166c03963447`)

```lean
def WNear.Binary.SerdeStructObjValueState.ValueConditions (cfg : Wasm.Near.WasmConfig) (maxP : ℕ) (bs : List UInt8)
  (B Bsaved : WNear.Binary.SerdeStructObjKeyState.Bounds) (K : ℕ → ℕ) : Prop :=
  ∀ (i j : ℕ) (a : WNear.AccountId) (rest : List UInt8) (hl F : ℕ) (cap : UInt32),
    i ≤ bs.length →
      bs[i + WNear.Binary.SerdeRead.wsLen (List.drop i bs)]? = some 58 →
        j =
            i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1 +
              WNear.Binary.SerdeRead.wsLen
                (List.drop (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) bs) →
          bs[j]? = some 34 →
            NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest) →
              B i hl F cap →
                cap.toNat < 2 ^ 25 →
                  hl % 65536 = 0 →
                    0 < hl →
                      WNear.Binary.SerdeErrBox.roomFor4 hl maxP 20 ∧
                        WNear.Binary.ParseStr.roomRun maxP hl cap [] (List.drop (j + 1) bs) ∧
                          WNear.Binary.VecFromElem.roomFor
                              (hl +
                                WNear.Binary.ScratchGrow.growthPages cap 0
                                    (WNear.Binary.ParseStrSuccess.appendChunks
                                      (List.drop (j + 1) bs) []) *
                                  65536)
                              maxP (UInt32.ofNat (↑a).toUTF8.toList.length) ∧
                            WNear.Binary.SerdeValueReuse.valueCost cfg F cap bs (↑a).toUTF8.toList
                                  rest (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) j ≤
                                K (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) ∧
                              ∀ (hl' : ℕ),
                                hl ≤ hl' →
                                  hl' ≤
                                      hl +
                                        (WNear.Binary.ScratchGrow.growthPages cap 0
                                              (WNear.Binary.ParseStrSuccess.appendChunks
                                                (List.drop (j + 1) bs) []) +
                                            (WNear.Binary.AllocNewCell.cellPages
                                                (WNear.Binary.AllocAlloc.wordsOf
                                                  (UInt32.ofNat (↑a).toUTF8.toList.length))
                                                1).toNat) *
                                          65536 →
                                    Bsaved (bs.length - rest.length) hl'
                                      (max
                                        (WNear.Binary.ScratchGrow.endFreeBound F cap 0
                                          (WNear.Binary.ParseStrSuccess.appendChunks
                                            (List.drop (j + 1) bs) []))
                                        1)
                                      (WNear.Binary.ScratchGrow.endState cap 0
                                          (WNear.Binary.ParseStrSuccess.appendChunks
                                            (List.drop (j + 1) bs) [])).1
```

## Bridge.Functions.StateRead

`WNear.Binary.StateRead.pre219` (hash `c2b7e3ca7f9cfa1e`)

```lean
def WNear.Binary.StateRead.pre219 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n g ta : ℕ) (A : ℕ → ℕ)
  (gt : Wasm.GlobalType) (s out idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (ob : List UInt8)
  (h : Wasm.NearState) (args : List Wasm.Value) : Iris.IProp GF :=
  fun args =>
    iprop(⌜args = [Wasm.Value.i32 out]⌝ ∗
        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
          WNear.Binary.ReadRegister.ifaceR n ta A ∗
            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                WNear.Binary.AllocInv.heapInv n maxP len live 1 ∗
                  n ↦[wms][ out.toNat ] ob ∗
                    n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗ NearLogic.mhostPt h)
```

## Bridge.Functions.StateReadLenF

`WNear.Binary.StateReadLenF.f219_spec_lenF` (hash `00000000f898d6d9`)

```lean
theorem WNear.Binary.StateReadLenF.f219_spec_lenF {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hout : out.toNat + 40 ≤ 2 ^ 32) (idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (ob : List UInt8)
  (hob : ob.length = 40) (h : Wasm.NearState) (hd4 pre b0 b1 c0 : List UInt8) (hhd : hd4.length = 4)
  (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hc0 : c0.length = 8) (hL : Wasm.Memory.decodeLE hd4 = pre.length)
  (hL0 : 0 < pre.length)
  (hv : h.storage WNear.Binary.StateRead.stateKey = some (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0))
  (hv28 : (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0).length < 2 ^ 28)
  (hroom1 :
    WNear.Binary.VecFromElem.roomFor len maxP
      (UInt32.ofNat (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0).length))
  (hroom2 :
    ∀ (len' : ℕ),
      len' = len ∨
          len' =
            WNear.Binary.VecFromElem.grownLen len
              (UInt32.ofNat (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0).length) →
        WNear.Binary.VecFromElem.roomFor len' maxP (UInt32.ofNat pre.length))
  (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen WNear.Binary.StateRead.stateKey.length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage WNear.Binary.StateRead.stateKey =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.Binary.StateRead.stateKey))
  (hproof :
    NearLogic.ProofBudget h st
      (NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.Binary.StateRead.stateKey)
        (h.storage WNear.Binary.StateRead.stateKey)))
  (hreg :
    Wasm.Near.withinLimit h.config.maxRegisterLen (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0).length = true) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f219 Cg
      (WNear.Binary.StateReadLenF.pre219F n g ta A gt s out idx maxP len live F ob h)
      (fun x =>
        105 * cfg.regularOpCost +
                (40 * cfg.regularOpCost +
                    (249 * cfg.regularOpCost + NearLogic.storageReadUse h WNear.Binary.StateRead.stateKey 5) +
                  WNear.Binary.StorageReadWrapF.costSF cfg F h (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0)) +
              WNear.Binary.BorshContractF.cost161 cfg F (UInt32.ofNat pre.length) +
            726 * cfg.regularOpCost +
          334 * cfg.regularOpCost)
      (WNear.Binary.StateReadLenF.post219LF n g ta A gt s out idx maxP len live F pre b0 b1 c0
        (WNear.Binary.StateRead.stateBytes hd4 pre b0 b1 c0).length h
        (NearLogic.StorageReadPost h WNear.Binary.StateRead.stateKey 0 st))
```

`WNear.Binary.StateReadLenF.f219_spec_model_lenF` (hash `00000000e2105a11`)

```lean
theorem WNear.Binary.StateReadLenF.f219_spec_model_lenF {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (sp out : UInt32) (hs : 592 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hout : out.toNat + 40 ≤ 2 ^ 32) (idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (hF : WNear.Binary.VecWithCap.okG F) (ob : List UInt8)
  (hob : ob.length = 40) (h : Wasm.NearState) (s : WNear.State) (hv : h.storage WNear.stateKey = some (WNear.header s))
  (hroom1 : WNear.Binary.VecFromElem.roomFor len maxP 29)
  (hroom2 :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len 29 → WNear.Binary.VecFromElem.roomFor len' maxP 1)
  (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink :
    h.storage WNear.stateKey =
      NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey))
  (hproof :
    NearLogic.ProofBudget h st
      (NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
        (h.storage WNear.stateKey)))
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) :
  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n maxP mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f219 Cg
      (WNear.Binary.StateReadLenF.pre219F n g ta A gt sp out idx maxP len live F ob h)
      (fun x =>
        105 * cfg.regularOpCost +
                (40 * cfg.regularOpCost +
                    (249 * cfg.regularOpCost + NearLogic.storageReadUse h WNear.Binary.StateRead.stateKey 5) +
                  WNear.Binary.StorageReadWrapF.costSF cfg F h (WNear.header s)) +
              WNear.Binary.BorshContractF.cost161 cfg F 1 +
            726 * cfg.regularOpCost +
          334 * cfg.regularOpCost)
      (WNear.Binary.StateReadLenF.postModelLF n g ta A gt sp out idx maxP len live F s h
        (NearLogic.StorageReadPost h WNear.Binary.StateRead.stateKey 0 st))
```

`WNear.Binary.StateReadLenF.pre219F` (hash `14646a1be868fece`)

```lean
def WNear.Binary.StateReadLenF.pre219F {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n g ta : ℕ)
  (A : ℕ → ℕ) (gt : Wasm.GlobalType) (s out idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (ob : List UInt8)
  (h : Wasm.NearState) (args : List Wasm.Value) : Iris.IProp GF :=
  fun args =>
    iprop(⌜args = [Wasm.Value.i32 out]⌝ ∗
        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
          WNear.Binary.ReadRegister.ifaceR n ta A ∗
            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                WNear.Binary.AllocInv.heapInv n maxP len live F ∗
                  n ↦[wms][ out.toNat ] ob ∗
                    n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗ NearLogic.mhostPt h)
```

## Bridge.Functions.StorageReadNoneF

`WNear.Binary.StorageReadWrapF.f548_noneF_host` (hash `0000000087670af0`)

```lean
theorem WNear.Binary.StorageReadWrapF.f548_noneF_host {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hout : out.toNat + 12 ≤ 2 ^ 32)
  (key : List UInt8) (idx : UInt32) (maxP len : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (ob : List UInt8)
  (hob : ob.length = 12) (h : Wasm.NearState) (st : Near.TrieOverlay.State) (hkl : key.length = kl.toNat)
  (hpos : 0 < kl.toNat) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen key.length = true)
  (hb : Near.TrieConstruction.build st.entries = Except.ok st.base)
  (hz : NearLogic.zeroHash ∉ List.map Prod.fst st.base.witness)
  (hlink : h.storage key = NearLogic.viewVal st (Near.TrieOverlay.contractKey h.context.currentAccountId key)) {bud : ℕ}
  (hproof : NearLogic.ProofBudget h st bud)
  (hbud : NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId key) (h.storage key) ≤ bud)
  (hsk : h.storage key = none) :
  WNear.Binary.StorageReadWrapF.srCodeF e inst mi A n maxP mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f548 Cg
      (WNear.Binary.StorageReadWrapF.pre548F n g ta A gt s out kp kl key idx maxP len live F ob h)
      (fun x =>
        40 * cfg.regularOpCost + (249 * cfg.regularOpCost + NearLogic.storageReadUse h key kl.toNat) +
          20 * cfg.regularOpCost)
      (WNear.Binary.StorageReadWrapF.post548NoneF n g ta A gt s out kp key idx maxP len live F
        (NearLogic.StorageReadPost h key 0 st))
```

## Bridge.Functions.StrCost

`WNear.Binary.ParseStr.roomRun` (hash `c05bf4890a5c29a3`)

```lean
def WNear.Binary.ParseStr.roomRun (maxP hl : ℕ) (cap : UInt32) (acc l : List UInt8) : Prop :=
  WNear.Binary.ParseStr.roomRun._unary maxP ⟨hl, ⟨cap, ⟨acc, l⟩⟩⟩
```

## Bridge.Functions.VecFromElem

`WNear.Binary.VecFromElem.roomFor` (hash `033ff23814a30ab9`)

```lean
def WNear.Binary.VecFromElem.roomFor (len maxP : ℕ) (size : UInt32) : Prop :=
  len % 65536 = 0 ∧
    0 < len ∧
      len +
              (WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf size)
                    1).toNat *
                65536 +
            65536 ≤
          2 ^ 32 ∧
        (len +
              (WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf size)
                    1).toNat *
                65536) /
            65536 ≤
          maxP
```

## Bridge.Methods.FtBalanceOfModel

`WNear.Binary.FtBalanceOfMethod.account_lookup_and_step` (hash `0000000011997b72`)

```lean
theorem WNear.Binary.FtBalanceOfMethod.account_lookup_and_step (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : WNear.RawStorage) (s : WNear.State) (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (hs : s.WF)
  (h : Wasm.NearState) (he : NearLogic.eraseP h = NearLogic.eraseP (WNear.Binary.hostOf ctx raw))
  (a : NearInterface.AccountId) :
  ∃ reg,
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (List.length a.bytes)) ++ a.bytes)) =
        Option.map (fun p => WasmLogic.storeBytes (Wasm.Value.i64 p.1) 8 ++ WasmLogic.storeBytes (Wasm.Value.i64 p.2) 8)
          reg ∧
      (WNear.wnear cfg).step ctx (some s) (WNear.Call.ftBalanceOf (WNear.AccountId.ofNear a)) =
        if 0 < WNear.Binary.FtTotalSupplyMethod.deficit ctx s then
          Except.error
            {
              failure :=
                NearInterface.ModelFailure.lackBalanceForState (WNear.Binary.FtTotalSupplyMethod.deficit ctx s),
              logs := [] }
        else
          Except.ok
            { state := s, ret := WNear.Ret.u128 ((Option.map (fun p => p.1.toNat + 2 ^ 64 * p.2.toNat) reg).getD 0),
              logs := [], promises := [] }
```

## NearInterface.Model

`NearInterface.ContractModel` (hash `349cee7a0e610b6d`)

```lean
inductive NearInterface.ContractModel : Type 1
| NearInterface.ContractModel.mk (State Call Ret Panic Promise : Type) (encodeState : State → NearInterface.RawStorage)
  (Inv : State → Prop) (Parses : String → Wasm.Near.Bytes → Call → Prop) (encodeRet : Ret → Wasm.Near.ReturnData)
  (encodeReceipts : NearInterface.Gas → List Promise → List NearInterface.RawReceipt)
  (panicFailure : Panic → NearInterface.Failure)
  (step : NearInterface.Context → Option State → Call → NearInterface.StepResult Panic State Ret Promise)
  (gas : NearInterface.Context → Option State → Call → NearInterface.Gas)
  (proofBound : NearInterface.Context → Option State → Call → ℕ) : NearInterface.ContractModel
```

`NearInterface.ContractModel.ModelFailure.toFailure` (hash `c6c4a85579466f8f`)

```lean
def NearInterface.ContractModel.ModelFailure.toFailure (M : NearInterface.ContractModel) :
  NearInterface.ModelFailure M.Panic → NearInterface.Failure :=
  fun x =>
    match x with
    | NearInterface.ModelFailure.panic p => M.panicFailure p
    | NearInterface.ModelFailure.balanceExceeded => NearInterface.Failure.balanceExceeded
    | NearInterface.ModelFailure.lackBalanceForState deficit =>
      NearInterface.Failure.lackBalanceForState deficit
    | NearInterface.ModelFailure.logLimit error => NearInterface.Failure.other error.message
    | NearInterface.ModelFailure.receiptInvalid message => NearInterface.Failure.other message
```

`NearInterface.ContractModel.ParsesFunctional` (hash `e204fc1a79346714`)

```lean
def NearInterface.ContractModel.ParsesFunctional (M : NearInterface.ContractModel) : Prop :=
  ∀ (method : String) (args : Wasm.Near.Bytes) (c c' : M.Call),
    M.Parses method args c → M.Parses method args c' → c = c'
```

`NearInterface.ContractModel.Represents` (hash `20341de58f81fa7d`)

```lean
def NearInterface.ContractModel.Represents (M : NearInterface.ContractModel) (raw : NearInterface.RawStorage) :
  Option M.State → Prop :=
  fun x =>
    match x with
    | none => raw = ∅
    | some s => M.Inv s ∧ raw = M.encodeState s
```

`NearInterface.Failed` (hash `b9a17449971bea9c`)

```lean
inductive NearInterface.Failed (Panic : Type) : Type
| NearInterface.Failed.mk {Panic : Type} (failure : NearInterface.ModelFailure Panic) (logs : List String) :
  NearInterface.Failed Panic
```

`NearInterface.ModelFailure` (hash `123ec05bbd86d494`)

```lean
inductive NearInterface.ModelFailure (Panic : Type) : Type
| NearInterface.ModelFailure.panic {Panic : Type} (p : Panic) : NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.balanceExceeded {Panic : Type} : NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.lackBalanceForState {Panic : Type} (deficit : NearInterface.Balance) :
  NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.logLimit {Panic : Type} (error : Wasm.Near.HostError) : NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.receiptInvalid {Panic : Type} (message : String) : NearInterface.ModelFailure Panic
```

`NearInterface.Outcome` (hash `8a0717d03380c7a4`)

```lean
inductive NearInterface.Outcome (State Ret Promise : Type) : Type
| NearInterface.Outcome.mk {State Ret Promise : Type} (state : State) (ret : Ret) (logs : List String)
  (promises : List Promise) : NearInterface.Outcome State Ret Promise
```

`NearInterface.StepResult` (hash `98f034d930bb6e84`)

```lean
def NearInterface.StepResult (Panic State Ret Promise : Type) : Type :=
  Except (NearInterface.Failed Panic) (NearInterface.Outcome State Ret Promise)
```

`NearInterface.StepResult.logs` (hash `775de7047fd2bda4`)

```lean
def NearInterface.StepResult.logs {Panic State Ret Promise : Type} :
  NearInterface.StepResult Panic State Ret Promise → List String :=
  fun x =>
    match x with
    | Except.ok o => o.logs
    | Except.error f => f.logs
```

`NearInterface.logLimitError` (hash `abd90ad08d8f8dab`)

```lean
def NearInterface.logLimitError (cfg : Wasm.Near.RuntimeConfig) (logs : List String) :
  Option (Wasm.Near.HostError × List String) :=
  NearInterface.logLimitError.go cfg 0 [] logs
```

`NearInterface.logLimitError.go` (hash `65eb75879978768e`)

```lean
def NearInterface.logLimitError.go (cfg : Wasm.Near.RuntimeConfig) (total : ℕ) (kept : List String) :
  List String → Option (Wasm.Near.HostError × List String) :=
  fun a =>
    List.brecOn (motive := fun a => ℕ → List String → Option (Wasm.Near.HostError × List String))
      a (NearInterface.logLimitError.go._f cfg) total kept
```

`NearInterface.returnDataGas` (hash `1543dfe90219aad2`)

```lean
def NearInterface.returnDataGas (ctx : NearInterface.Context) (bytes : ℕ) : NearInterface.Gas :=
  have fee := ctx.protocol.fees.actionFees.newDataReceiptByte;
  (List.map (fun r => (fee.send (decide (r = ctx.current)) + fee.execution) * bytes)
      ctx.outputDataReceivers).sum
```

## NearInterface.Refines

`NearInterface.Matches` (hash `37564aad8bda2995`)

```lean
def NearInterface.Matches (M : NearInterface.ContractModel) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
  (r : NearInterface.Observation) : NearInterface.StepResult M.Panic M.State M.Ret M.Promise → Prop :=
  fun x =>
    match x with
    | Except.ok o =>
      have receipts := M.encodeReceipts (ctx.prepaidGas - r.usedGas) o.promises;
      r.outcome = Except.ok (M.encodeRet o.ret) ∧
        r.storage = M.encodeState o.state ∧
          r.balance = ctx.balance + ctx.attached - NearInterface.receiptDeposits receipts ∧
            r.storageUsage =
                ctx.storageUsage - NearInterface.storageUsageOf ctx.protocol raw +
                  NearInterface.storageUsageOf ctx.protocol (M.encodeState o.state) ∧
              r.logs = o.logs ∧ r.receipts = receipts
    | Except.error f =>
      r.outcome = Except.error (NearInterface.ContractModel.ModelFailure.toFailure M f.failure) ∧
        r.storage = raw ∧
          r.balance = ctx.balance ∧
            r.storageUsage = ctx.storageUsage ∧ r.logs = f.logs ∧ r.receipts = []
```

`NearInterface.Refines` (hash `e8d3ec6936af5ac7`)

```lean
def NearInterface.Refines (R : NearInterface.RuntimeInterface) (protocol : Wasm.Near.RuntimeConfig) (code : R.Code)
  (M : NearInterface.ContractModel) : Prop :=
  ∀ (raw : NearInterface.RawStorage) (st : Option M.State) (ctx : NearInterface.Context),
    M.Represents raw st →
      ctx.WF raw →
        ctx.protocol = protocol →
          have r := R.exec code raw ctx;
          (∀ (msg : String),
              r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
            (∀ (c : M.Call),
                M.Parses ctx.method ctx.args c →
                  have res := M.step ctx st c;
                  (M.gas ctx st c ≤ ctx.gasLimit →
                      ctx.ProofRoom (M.proofBound ctx st c) →
                        NearInterface.Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
                    (NearInterface.Matches M ctx raw r res ∨
                      NearInterface.ResourceFailure r ∧
                        NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)) ∧
              ((¬∃ c, M.Parses ctx.method ctx.args c) → NearInterface.RolledBack ctx raw r)
```

`NearInterface.Refines.failure_rollback` (hash `00000000e8d827ab`)

```lean
theorem NearInterface.Refines.failure_rollback {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) {f : NearInterface.Failure}
  (hfail : (R.exec code raw ctx).outcome = Except.error f) : NearInterface.RolledBack ctx raw (R.exec code raw ctx)
```

`NearInterface.Refines.gas_bound` (hash `000000001e0678ca`)

```lean
theorem NearInterface.Refines.gas_bound {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) {c : M.Call} (hparse : M.Parses ctx.method ctx.args c)
  (hgas : M.gas ctx st c ≤ ctx.gasLimit) (hproof : ctx.ProofRoom (M.proofBound ctx st c)) :
  (R.exec code raw ctx).usedGas ≤ M.gas ctx st c
```

`NearInterface.Refines.invalid_input` (hash `00000000ec18a34f`)

```lean
theorem NearInterface.Refines.invalid_input {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (hinvalid : ¬∃ c, M.Parses ctx.method ctx.args c) :
  NearInterface.RolledBack ctx raw (R.exec code raw ctx)
```

`NearInterface.Refines.no_execution_issue` (hash `00000000bc1f4254`)

```lean
theorem NearInterface.Refines.no_execution_issue {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (msg : String) :
  (R.exec code raw ctx).outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)
```

`NearInterface.Refines.transfer` (hash `0000000051c57a82`)

```lean
theorem NearInterface.Refines.transfer {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig} {code : R.Code}
  {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State} {ctx : NearInterface.Context}
  (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
  (hprot : ctx.protocol = protocol) {c : M.Call} (hparse : M.Parses ctx.method ctx.args c)
  (hgas : M.gas ctx st c ≤ ctx.gasLimit) (hproof : ctx.ProofRoom (M.proofBound ctx st c)) :
  NearInterface.Matches M ctx raw (R.exec code raw ctx) (M.step ctx st c)
```

`NearInterface.ResourceFailure` (hash `3c862ca5a53f7623`)

```lean
def NearInterface.ResourceFailure (r : NearInterface.Observation) : Prop :=
  r.outcome = Except.error NearInterface.Failure.outOfGas ∨
    r.outcome = Except.error NearInterface.Failure.storageProofExceeded
```

`NearInterface.RolledBack` (hash `f4582bb96b6fbc5a`)

```lean
def NearInterface.RolledBack (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
  (r : NearInterface.Observation) : Prop :=
  (∃ f, r.outcome = Except.error f) ∧
    r.storage = raw ∧
      r.balance = ctx.balance ∧ r.storageUsage = ctx.storageUsage ∧ r.receipts = []
```

## Proofs.Authorization

`WNear.balance_authorization` (hash `00000000890f2136`)

```lean
theorem WNear.balance_authorization : WNear.BalanceAuthorization
```

`WNear.registration_authorization` (hash `00000000e0341f1b`)

```lean
theorem WNear.registration_authorization : WNear.RegistrationAuthorization
```

## Proofs.Availability

`WNear.deposit_available` (hash `00000000cf8a7a6c`)

```lean
theorem WNear.deposit_available : WNear.DepositAvailable
```

`WNear.deposit_available_at_boundary` (hash `000000005177d310`)

```lean
theorem WNear.deposit_available_at_boundary : WNear.DepositAvailableAtBoundary
```

`WNear.withdraw_available` (hash `0000000005c62657`)

```lean
theorem WNear.withdraw_available : WNear.WithdrawAvailable
```

`WNear.withdraw_available_at_boundary` (hash `000000008b8f064c`)

```lean
theorem WNear.withdraw_available_at_boundary : WNear.WithdrawAvailableAtBoundary
```

`WNear.withdraw_available_binary` (hash `00000000e8f4a189`)

```lean
theorem WNear.withdraw_available_binary {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {cfg : WNear.Config} (href : NearInterface.Refines R protocol code (WNear.wnear cfg))
  {s : WNear.State} {ctx : NearInterface.Context} {amount : ℕ} (hs : WNear.Inv cfg s) (hwf : ctx.WF (WNear.encode s))
  (hprot : ctx.protocol = protocol) (hparse : WNear.Parses ctx.method ctx.args (WNear.Call.nearWithdraw amount))
  (hreg : WNear.AccountId.ofNear ctx.predecessor ∈ s.registered)
  (hamt : amount ≤ s.balance (WNear.AccountId.ofNear ctx.predecessor)) (hdep : ctx.attached = 1)
  (hbound : amount + 1 < WNear.u128Bound) (hbal : amount ≤ ctx.balance)
  (hrent :
    NearInterface.stakeDeficit ctx.protocol
        (WNear.usageAfter ctx (some s)
          (have __src :=
            s.setBalance (WNear.AccountId.ofNear ctx.predecessor)
              (s.balance (WNear.AccountId.ofNear ctx.predecessor) - amount);
          { registered := __src.registered, balance := __src.balance, totalSupply := s.totalSupply - amount,
            accountStorageUsage := __src.accountStorageUsage }))
        (ctx.balance - amount) ctx.locked =
      0)
  (hlog :
    NearInterface.logLimitError ctx.protocol
        [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
            toString (WNear.AccountId.ofNear ctx.predecessor)] =
      none)
  (hreceipts :
    NearInterface.ReceiptValidation.callReceiptsError ctx.protocol ctx.current ctx.signer ctx.signerPk
        (WNear.encodeReceipts [WNear.Promise.transfer (WNear.AccountId.ofNear ctx.predecessor) (amount + 1)]) =
      none)
  (hgas : WNear.gasBound ctx (WNear.Call.nearWithdraw amount) ≤ ctx.gasLimit)
  (hproof : ctx.ProofRoom (WNear.proofBound ctx)) :
  (R.exec code (WNear.encode s) ctx).outcome = Except.ok (Wasm.Near.ReturnData.receiptIndex 0) ∧
    (R.exec code (WNear.encode s) ctx).storage =
      WNear.encode
        (have __src :=
          s.setBalance (WNear.AccountId.ofNear ctx.predecessor)
            (s.balance (WNear.AccountId.ofNear ctx.predecessor) - amount);
        { registered := __src.registered, balance := __src.balance, totalSupply := s.totalSupply - amount,
          accountStorageUsage := __src.accountStorageUsage })
```

## Proofs.Conservation

`WNear.conservation` (hash `00000000e13d24ac`)

```lean
theorem WNear.conservation : WNear.Conservation
```

## Proofs.Invariants

`WNear.inv_preserved` (hash `000000006db6f3fb`)

```lean
theorem WNear.inv_preserved : WNear.InvPreserved
```

## Proofs.Refinement

`WNear.PinnedProtocolAvailable` (hash `ee46fca246f4283e`)

```lean
def WNear.PinnedProtocolAvailable : Prop :=
  ∃ protocol, Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol
```

`WNear.deployed_code_size` (hash `00000000aeeae656`)

```lean
theorem WNear.deployed_code_size : WNear.Binary.wNearBytes.size ≤ 185625
```

`WNear.ftBalanceOf_accepted_obligation` (hash `000000006933a460`)

```lean
theorem WNear.ftBalanceOf_accepted_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of") (c : WNear.Call)
  (hparse : (WNear.wnear cfg).Parses ctx.method ctx.args c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.ftBalanceOf_no_issue_obligation` (hash `00000000285557a9`)

```lean
theorem WNear.ftBalanceOf_no_issue_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of") (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
```

`WNear.ftBalanceOf_obligation` (hash `000000003723e7af`)

```lean
theorem WNear.ftBalanceOf_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "ft_balance_of"
```

`WNear.ftBalanceOf_rejected_obligation` (hash `00000000b628b177`)

```lean
theorem WNear.ftBalanceOf_rejected_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hreject : ¬∃ c, (WNear.wnear cfg).Parses ctx.method ctx.args c) :
  NearInterface.RolledBack ctx raw
    (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx)
```

`WNear.ftResolveTransfer_obligation` (hash `000000009b74f93c`)

```lean
theorem WNear.ftResolveTransfer_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "ft_resolve_transfer"
```

`WNear.ftTransferCall_obligation` (hash `00000000d9ec6e5a`)

```lean
theorem WNear.ftTransferCall_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "ft_transfer_call"
```

`WNear.ftTransfer_obligation` (hash `00000000804dc4db`)

```lean
theorem WNear.ftTransfer_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "ft_transfer"
```

`WNear.nearWithdraw_obligation` (hash `0000000075abe891`)

```lean
theorem WNear.nearWithdraw_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "near_withdraw"
```

`WNear.pinned_costs_obligation` (hash `000000000b377d6a`)

```lean
theorem WNear.pinned_costs_obligation (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  WNear.Binary.FtTotalSupplyMethod.CostsV86 protocol
```

`WNear.pinned_deposit_costs_obligation` (hash `00000000cd73be4c`)

```lean
theorem WNear.pinned_deposit_costs_obligation (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  WNear.Binary.NearDepositGas.CostsDepositV86 protocol
```

`WNear.pinned_limits_obligation` (hash `00000000cc6e9626`)

```lean
theorem WNear.pinned_limits_obligation (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  WNear.Binary.FtTotalSupplyMethod.LimitsV86 protocol
```

`WNear.pinned_new_costs_obligation` (hash `000000007f713b64`)

```lean
theorem WNear.pinned_new_costs_obligation (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  WNear.Binary.NewMethod.CostsNewV86 protocol
```

`WNear.pinned_runtime_obligation` (hash `00000000cede916f`)

```lean
theorem WNear.pinned_runtime_obligation (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  WNear.Binary.WProtocol protocol
```

`WNear.refines_wnear` (hash `000000001848be87`)

```lean
theorem WNear.refines_wnear (cfg : WNear.Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hcfg : cfg.WF)
  (hcode : Wasm.Binary.decode WNear.Binary.wNearBytes = Except.ok code)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  NearInterface.Refines Near.Boundary.nearRuntime protocol
    { code := { module := code, size := WNear.Binary.wNearBytes.size, hash := "" }, codeOf := codeOf } (WNear.wnear cfg)
```

`WNear.refines_wnear_exported` (hash `00000000bfff3c66`)

```lean
theorem WNear.refines_wnear_exported (cfg : WNear.Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hcfg : cfg.WF)
  (hcode : Wasm.Binary.decode WNear.Binary.wNearBytes = Except.ok code)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (hmethod : ctx.method ∈ WNear.exportedMethods) :
  have r :=
    Near.Boundary.nearRuntime.exec
      { code := { module := code, size := WNear.Binary.wNearBytes.size, hash := "" }, codeOf := codeOf } raw ctx;
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    (∀ (c : (WNear.wnear cfg).Call),
        (WNear.wnear cfg).Parses ctx.method ctx.args c →
          have res := (WNear.wnear cfg).step ctx st c;
          ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
              ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
                NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
            (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
              NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)) ∧
      ((¬∃ c, (WNear.wnear cfg).Parses ctx.method ctx.args c) → NearInterface.RolledBack ctx raw r)
```

`WNear.storageBalanceOf_obligation` (hash `00000000e4a9ffa1`)

```lean
theorem WNear.storageBalanceOf_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "storage_balance_of"
```

`WNear.storageDeposit_obligation` (hash `00000000628b9004`)

```lean
theorem WNear.storageDeposit_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "storage_deposit"
```

`WNear.storageUnregister_obligation` (hash `00000000840e7fa7`)

```lean
theorem WNear.storageUnregister_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "storage_unregister"
```

`WNear.storageWithdraw_obligation` (hash `000000003c5299e0`)

```lean
theorem WNear.storageWithdraw_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) :
  WNear.Binary.Exported.MethodClause cfg WNear.Binary.wNearBytes.size codeOf protocol "storage_withdraw"
```

`WNear.withdraw_available_wasm` (hash `000000005107b7ad`)

```lean
theorem WNear.withdraw_available_wasm (cfg : WNear.Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hcfg : cfg.WF)
  (hcode : Wasm.Binary.decode WNear.Binary.wNearBytes = Except.ok code)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) {s : WNear.State}
  {ctx : NearInterface.Context} {amount : ℕ} (hs : WNear.Inv cfg s) (hwf : ctx.WF (WNear.encode s))
  (hprot : ctx.protocol = protocol) (hparse : WNear.Parses ctx.method ctx.args (WNear.Call.nearWithdraw amount))
  (hreg : WNear.AccountId.ofNear ctx.predecessor ∈ s.registered)
  (hamt : amount ≤ s.balance (WNear.AccountId.ofNear ctx.predecessor)) (hdep : ctx.attached = 1)
  (hbound : amount + 1 < WNear.u128Bound) (hbal : amount ≤ ctx.balance)
  (hrent :
    NearInterface.stakeDeficit ctx.protocol
        (WNear.usageAfter ctx (some s)
          (have __src :=
            s.setBalance (WNear.AccountId.ofNear ctx.predecessor)
              (s.balance (WNear.AccountId.ofNear ctx.predecessor) - amount);
          { registered := __src.registered, balance := __src.balance, totalSupply := s.totalSupply - amount,
            accountStorageUsage := __src.accountStorageUsage }))
        (ctx.balance - amount) ctx.locked =
      0)
  (hlog :
    NearInterface.logLimitError ctx.protocol
        [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
            toString (WNear.AccountId.ofNear ctx.predecessor)] =
      none)
  (hreceipts :
    NearInterface.ReceiptValidation.callReceiptsError ctx.protocol ctx.current ctx.signer ctx.signerPk
        (WNear.encodeReceipts [WNear.Promise.transfer (WNear.AccountId.ofNear ctx.predecessor) (amount + 1)]) =
      none)
  (hgas : WNear.gasBound ctx (WNear.Call.nearWithdraw amount) ≤ ctx.gasLimit)
  (hproof : ctx.ProofRoom (WNear.proofBound ctx)) :
  have r :=
    Near.Boundary.nearRuntime.exec
      { code := { module := code, size := WNear.Binary.wNearBytes.size, hash := "" }, codeOf := codeOf }
      (WNear.encode s) ctx;
  r.outcome = Except.ok (Wasm.Near.ReturnData.receiptIndex 0) ∧
    r.storage =
      WNear.encode
        (have __src :=
          s.setBalance (WNear.AccountId.ofNear ctx.predecessor)
            (s.balance (WNear.AccountId.ofNear ctx.predecessor) - amount);
        { registered := __src.registered, balance := __src.balance, totalSupply := s.totalSupply - amount,
          accountStorageUsage := __src.accountStorageUsage })
```

## Proofs.Storage

`WNear.project_encode` (hash `00000000f97dfa6f`)

```lean
theorem WNear.project_encode : WNear.ProjectEncode
```

`WNear.storage_coverage` (hash `00000000fdfdf849`)

```lean
theorem WNear.storage_coverage : WNear.StorageCoverage
```

## Proofs.Views

`WNear.balance_of_correct` (hash `0000000074f20d71`)

```lean
theorem WNear.balance_of_correct : WNear.BalanceOfCorrect
```

`WNear.init_once` (hash `0000000075320071`)

```lean
theorem WNear.init_once : WNear.InitOnce
```

`WNear.total_supply_correct` (hash `0000000029008582`)

```lean
theorem WNear.total_supply_correct : WNear.TotalSupplyCorrect
```

`WNear.views_pure` (hash `0000000008a46ce5`)

```lean
theorem WNear.views_pure : WNear.ViewsPure
```

`WNear.views_total` (hash `00000000d6d9bb0c`)

```lean
theorem WNear.views_total : WNear.ViewsTotal
```

## Spec.Authorization

`WNear.BalanceAuthorization` (hash `b3fe59e56bbdb9cd`)

```lean
def WNear.BalanceAuthorization : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env call = Except.ok o →
        ∀ (a : WNear.AccountId),
          a ≠ env.predecessor →
            o.state.balance a < s.balance a →
              ∃ sender amount,
                call = WNear.Call.ftResolveTransfer sender a amount ∧
                  s.balance a - o.state.balance a ≤ amount
```

`WNear.RegistrationAuthorization` (hash `bfa31c9d6941c45e`)

```lean
def WNear.RegistrationAuthorization : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env call = Except.ok o →
        ∀ a ∈ s.registered, a ∉ o.state.registered → a = env.predecessor
```

## Spec.Availability

`WNear.DepositAvailable` (hash `275c18a892b057eb`)

```lean
def WNear.DepositAvailable : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env),
    WNear.Inv cfg s →
      0 < env.attachedDeposit →
        s.totalSupply + env.attachedDeposit < WNear.u128Bound →
          env.predecessor ∈ s.registered ∨ s.storageMin ≤ env.attachedDeposit →
            ∃ o,
              WNear.step cfg (some s) env WNear.Call.nearDeposit = Except.ok o ∧
                env.predecessor ∈ o.state.registered ∧
                  (o.state.balance env.predecessor +
                        if env.predecessor ∈ s.registered then 0 else s.storageMin) =
                      s.balance env.predecessor + env.attachedDeposit ∧
                    o.promises = []
```

`WNear.DepositAvailableAtBoundary` (hash `65529199857b7a14`)

```lean
def WNear.DepositAvailableAtBoundary : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (ctx : NearInterface.Context),
    have env := WNear.Env.ofContext ctx;
    WNear.Inv cfg s →
      0 < ctx.attached →
        s.totalSupply + ctx.attached < WNear.u128Bound →
          env.predecessor ∈ s.registered ∨ s.storageMin ≤ ctx.attached →
            ∃ o,
              WNear.step (WNear.Config.ofRuntime ctx.protocol) (some s) env
                    WNear.Call.nearDeposit =
                  Except.ok o ∧
                env.predecessor ∈ o.state.registered ∧
                  (o.state.balance env.predecessor +
                        if env.predecessor ∈ s.registered then 0 else s.storageMin) =
                      s.balance env.predecessor + ctx.attached ∧
                    o.promises = [] ∧
                      have deficit :=
                        NearInterface.stakeDeficit ctx.protocol
                          (WNear.usageAfter ctx (some s) o.state) (ctx.balance + ctx.attached)
                          ctx.locked;
                      NearInterface.logLimitError ctx.protocol o.logs = none →
                        WNear.contractStep ctx (some s) WNear.Call.nearDeposit =
                          if 0 < deficit then
                            Except.error
                              { failure := NearInterface.ModelFailure.lackBalanceForState deficit,
                                logs := o.logs }
                          else
                            Except.ok
                              { state := o.state, ret := o.ret, logs := o.logs, promises := [] }
```

`WNear.WithdrawAvailable` (hash `434fc06075b1c6be`)

```lean
def WNear.WithdrawAvailable : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (amount : ℕ),
    WNear.Inv cfg s →
      env.predecessor ∈ s.registered →
        amount ≤ s.balance env.predecessor →
          env.attachedDeposit = 1 →
            amount + 1 < WNear.u128Bound →
              WNear.step cfg (some s) env (WNear.Call.nearWithdraw amount) =
                Except.ok
                  {
                    state :=
                      have __src :=
                        s.setBalance env.predecessor (s.balance env.predecessor - amount);
                      { registered := __src.registered, balance := __src.balance,
                        totalSupply := s.totalSupply - amount,
                        accountStorageUsage := __src.accountStorageUsage },
                    promises := [WNear.Promise.transfer env.predecessor (amount + 1)],
                    ret := WNear.Ret.promise 0,
                    logs :=
                      [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
                          toString env.predecessor] }
```

`WNear.WithdrawAvailableAtBoundary` (hash `ce6d8bc4ad971d17`)

```lean
def WNear.WithdrawAvailableAtBoundary : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (ctx : NearInterface.Context) (amount : ℕ),
    have a := WNear.AccountId.ofNear ctx.predecessor;
    have s' :=
      have __src := s.setBalance a (s.balance a - amount);
      { registered := __src.registered, balance := __src.balance,
        totalSupply := s.totalSupply - amount, accountStorageUsage := __src.accountStorageUsage };
    WNear.Inv cfg s →
      a ∈ s.registered →
        amount ≤ s.balance a →
          ctx.attached = 1 →
            amount + 1 < WNear.u128Bound →
              amount ≤ ctx.balance →
                NearInterface.stakeDeficit ctx.protocol (WNear.usageAfter ctx (some s) s')
                      (ctx.balance - amount) ctx.locked =
                    0 →
                  NearInterface.logLimitError ctx.protocol
                        [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
                            toString a] =
                      none →
                    NearInterface.ReceiptValidation.callReceiptsError ctx.protocol ctx.current
                          ctx.signer ctx.signerPk
                          (WNear.encodeReceipts [WNear.Promise.transfer a (amount + 1)]) =
                        none →
                      WNear.contractStep ctx (some s) (WNear.Call.nearWithdraw amount) =
                        Except.ok
                          { state := s', ret := WNear.Ret.promise 0,
                            logs :=
                              [toString "Withdraw " ++ toString amount ++
                                    toString " NEAR from " ++
                                  toString a],
                            promises := [WNear.Promise.transfer a (amount + 1)] }
```

## Spec.Conservation

`WNear.Conservation` (hash `b91c36f2bfeb20d5`)

```lean
def WNear.Conservation : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env call = Except.ok o →
        ↑o.state.totalSupply - ↑s.totalSupply +
            ↑s.storageMin * (↑o.state.registered.card - ↑s.registered.card) ≤
          ↑env.attachedDeposit - ↑o.nearOut
```

## Spec.Contract

`WNear.wnear` (hash `997da11be2c01ee4`)

```lean
def WNear.wnear (cfg : WNear.Config) : NearInterface.ContractModel :=
  { State := WNear.State, Call := WNear.Call, Ret := WNear.Ret, Panic := WNear.Panic,
    Promise := WNear.Promise, encodeState := WNear.encode, Inv := WNear.Inv cfg,
    Parses := WNear.Parses, encodeRet := WNear.encodeRet,
    encodeReceipts := fun x => WNear.encodeReceipts, panicFailure := WNear.Panic.failure,
    step := WNear.contractStep, gas := fun ctx x c => WNear.gasBound ctx c,
    proofBound := fun ctx x x_1 => WNear.proofBound ctx }
```

`WNear.wnear_parsesFunctional` (hash `00000000fee36cb6`)

```lean
theorem WNear.wnear_parsesFunctional (cfg : WNear.Config) : (WNear.wnear cfg).ParsesFunctional
```

## Spec.Exports

`WNear.exportedMethods` (hash `bd3fd7cbc3b6baf6`)

```lean
def WNear.exportedMethods : List String :=
  ["storage_minimum_balance", "near_deposit", "near_withdraw", "new", "ft_transfer",
    "ft_transfer_call", "ft_total_supply", "ft_balance_of", "ft_resolve_transfer",
    "storage_deposit", "storage_withdraw", "storage_unregister", "storage_balance_bounds",
    "storage_balance_of", "ft_metadata"]
```

`WNear.funcExportNames` (hash `18dcbdb5f054dc17`)

```lean
def WNear.funcExportNames (m : Wasm.Module) : List String :=
  List.filterMap
    (fun e =>
      match e.desc with
      | Wasm.ExportDesc.func i => some e.name
      | x => none)
    m.exports.toList
```

## Spec.Invariants

`WNear.Config.WF` (hash `cdf8f2c7b4098ab6`)

```lean
def WNear.Config.WF (cfg : WNear.Config) : Prop :=
  cfg.measuredAccountStorageUsage < WNear.u64Bound
```

`WNear.Inv` (hash `9c58883e2b30905f`)

```lean
inductive WNear.Inv (cfg : WNear.Config) (s : WNear.State) : Prop
| WNear.Inv.mk {cfg : WNear.Config} {s : WNear.State} (toWF : s.WF) (supply : s.supply = s.totalSupply)
  (usage : s.accountStorageUsage = cfg.measuredAccountStorageUsage) : WNear.Inv cfg s
```

`WNear.InvPreserved` (hash `9055243458cf8585`)

```lean
def WNear.InvPreserved : Prop :=
  ∀ (cfg : WNear.Config) (st : Option WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    cfg.WF →
      (∀ (s : WNear.State), st = some s → WNear.Inv cfg s) →
        WNear.step cfg st env call = Except.ok o → WNear.Inv cfg o.state
```

## Spec.Storage

`WNear.ProjectEncode` (hash `f83de85fe675beb6`)

```lean
def WNear.ProjectEncode : Prop :=
  ∀ (s : WNear.State), s.WF → WNear.project (WNear.encode s) = some s
```

`WNear.StorageCoverage` (hash `a4c035b02fb893e8`)

```lean
def WNear.StorageCoverage : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State),
    WNear.Inv cfg s →
      WNear.storageUsage cfg (WNear.encode s) ≤
        cfg.recordBytes (WNear.stateKey, WNear.header s) +
          s.registered.card * s.accountStorageUsage
```

## Spec.Views

`WNear.BalanceOfCorrect` (hash `fb181a48e89a6bec`)

```lean
def WNear.BalanceOfCorrect : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (a : WNear.AccountId)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env (WNear.Call.ftBalanceOf a) = Except.ok o →
        o.ret = WNear.Ret.u128 (s.balance a)
```

`WNear.InitOnce` (hash `380260cbce064460`)

```lean
def WNear.InitOnce : Prop :=
  (∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env),
      env.attachedDeposit = 0 →
        WNear.step cfg (some s) env WNear.Call.new =
          Except.error WNear.Panic.alreadyInitialized) ∧
    ∀ (cfg : WNear.Config) (env : WNear.Env) (call : WNear.Call),
      call ≠ WNear.Call.new → ∃ p, WNear.step cfg none env call = Except.error p
```

`WNear.TotalSupplyCorrect` (hash `5460da1e157c6d7c`)

```lean
def WNear.TotalSupplyCorrect : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env WNear.Call.ftTotalSupply = Except.ok o →
        o.ret = WNear.Ret.u128 s.supply
```

`WNear.ViewsPure` (hash `c14c5058c68f8efd`)

```lean
def WNear.ViewsPure : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    call.isView = true →
      WNear.step cfg (some s) env call = Except.ok o → o.state = s ∧ o.promises = [] ∧ o.logs = []
```

`WNear.ViewsTotal` (hash `c5873a3d24413009`)

```lean
def WNear.ViewsTotal : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call),
    call.isView = true → ∃ o, WNear.step cfg (some s) env call = Except.ok o
```
