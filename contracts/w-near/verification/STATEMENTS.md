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

`WNear.Binary.Exported.Clauses` (hash `a8eb8e27197807bc`)

```lean
def WNear.Binary.Exported.Clauses (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) : Prop :=
  ∀ method ∈ WNear.exportedMethods,
    WNear.Binary.Exported.MethodClause cfg size codeOf protocol method
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

`WNear.Binary.Exported.all_clauses` (hash `0000000038e9b91c`)

```lean
theorem WNear.Binary.Exported.all_clauses (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625)
  (hr : WNear.Binary.Exported.Remaining cfg size codeOf protocol) :
  WNear.Binary.Exported.Clauses cfg size codeOf protocol
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

## Bridge.Functions.BalanceOf297ArrayParser

`WNear.Binary.BalanceOf297AbsentCall.f65_arr_model_room` (hash `000000004d522f6e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.f65_arr_model_room {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 38 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (j k mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hsp : 448 ≤ sp.toNat) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hroom : WNear.Binary.ParseStr.roomRun 2048 mlen 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (mlen +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hroom6 :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) mlen
      2048) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n 2048 mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs (↑a).toUTF8.toList rest j))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        ∃ hl',
                          ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
                            WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl'
                              (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) F))
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

## Bridge.Functions.BalanceOf297CopiedBody

`WNear.Binary.BalanceOf297AbsentCall.array_absent_body` (hash `00000000236dae53`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_body {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ)
  (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32) (len : ℕ) (a : WNear.AccountId)
  (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (halloc :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0
                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        len live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body` (hash `00000000ea618213`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (halloc :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0
                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        len live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

## Bridge.Functions.BalanceOf297CopiedCall

`WNear.Binary.BalanceOf297AbsentCall.array_parser_call_through_cleanup` (hash `00000000f700e87e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_parser_call_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut jsonRest : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom : WNear.Binary.ParseStr.roomRun 2048 len 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (len +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) len
      2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                  A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                    A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                      A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                        WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                          A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                            WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                    (1000 * cfg.regularOpCost +
                                                        (45 * cfg.regularOpCost +
                                                          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                                                              cfg.regularOpCost +
                                                            WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs
                                                              (↑a).toUTF8.toList jsonRest j)) +
                                                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                        (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1)
                                                          F)
                                                        h S a R) ∗
                                                  g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                    WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                      WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                        WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                          n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                            NearLogic.mhostPt h ∗
                                                              WNear.Binary.AllocInv.heapInv n 2048 len
                                                                  ((ip.toNat, ic.toNat) :: live) F ∗
                                                                n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                                  n ↦[wms][ ip.toNat ] bs ∗
                                                                    n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                      n ↦[wms][ 1062392 ]
                                                                          WNear.Binary.ParseStr.escTable ∗
                                                                        n ↦[wms][ 1071704 ]
                                                                            WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                          n ↦[wms][ 1062712 ]
                                                                              WNear.Binary.SerdeEsc.hexTable ∗
                                                                            n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                              n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                    WasmLogic.bytes32 oldC ∗
                                                                                  n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                                    n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                                      n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                          WasmLogic.bytes32 oldD ∗
                                                                                        n ↦[wms][ (s + 48).toNat ]
                                                                                            WasmLogic.bytes32 ip ∗
                                                                                          n ↦[wms][ (s + 48).toNat + 4 ]
                                                                                              WasmLogic.bytes32 ic ∗
                                                                                            n ↦[wms][
                                                                                                (s + 48).toNat + 8 ]
                                                                                                WasmLogic.bytes32
                                                                                                  (UInt32.ofNat
                                                                                                    bs.length) ∗
                                                                                              n ↦[wms][ (s + 60).toNat ]
                                                                                                  contractTail ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 8).toNat ] ob ∗
                                                                                                  WNear.Binary.ToVec.tvData
                                                                                                      n ta ptr0 (A 759)
                                                                                                      (A 353) ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                            144).toNat ]
                                                                                                        out ∗
                                                                                                      n ↦[wms][
                                                                                                          s.toNat ]
                                                                                                          head ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)
      [Wasm.Value.i32 (s + 88), Wasm.Value.i32 ip, Wasm.Value.i32 (UInt32.ofNat bs.length)]
      (List.take 115 (List.drop 35 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_parser_call_through_cleanup` (hash `0000000026f530eb`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_parser_call_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut jsonRest : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom : WNear.Binary.ParseStr.roomRun 2048 len 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (len +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) len
      2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                  A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                    A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                      A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                        WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                          A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                            WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                    (1000 * cfg.regularOpCost +
                                                        (45 * cfg.regularOpCost +
                                                          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                                                              cfg.regularOpCost +
                                                            WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs
                                                              (↑a).toUTF8.toList jsonRest j)) +
                                                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                        (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1)
                                                          F)
                                                        h S a R) ∗
                                                  g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                    WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                      WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                        WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                          n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                            NearLogic.mhostPt h ∗
                                                              WNear.Binary.AllocInv.heapInv n 2048 len
                                                                  ((ip.toNat, ic.toNat) :: live) F ∗
                                                                n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                                  n ↦[wms][ ip.toNat ] bs ∗
                                                                    n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                      n ↦[wms][ 1062392 ]
                                                                          WNear.Binary.ParseStr.escTable ∗
                                                                        n ↦[wms][ 1071704 ]
                                                                            WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                          n ↦[wms][ 1062712 ]
                                                                              WNear.Binary.SerdeEsc.hexTable ∗
                                                                            n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                              n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                    WasmLogic.bytes32 oldC ∗
                                                                                  n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                                    n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                                      n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                          WasmLogic.bytes32 oldD ∗
                                                                                        n ↦[wms][ (s + 48).toNat ]
                                                                                            WasmLogic.bytes32 ip ∗
                                                                                          n ↦[wms][ (s + 48).toNat + 4 ]
                                                                                              WasmLogic.bytes32 ic ∗
                                                                                            n ↦[wms][
                                                                                                (s + 48).toNat + 8 ]
                                                                                                WasmLogic.bytes32
                                                                                                  (UInt32.ofNat
                                                                                                    bs.length) ∗
                                                                                              n ↦[wms][ (s + 60).toNat ]
                                                                                                  contractTail ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 8).toNat ] ob ∗
                                                                                                  WNear.Binary.ToVec.tvData
                                                                                                      n ta ptr0 (A 759)
                                                                                                      (A 353) ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                            144).toNat ]
                                                                                                        out ∗
                                                                                                      n ↦[wms][
                                                                                                          s.toNat ]
                                                                                                          head ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)
      [Wasm.Value.i32 (s + 88), Wasm.Value.i32 ip, Wasm.Value.i32 (UInt32.ofNat bs.length)]
      (List.take 115 (List.drop 35 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297CopiedParser

`WNear.Binary.BalanceOf297AbsentCall.f65_arr_copied_room` (hash `00000000d47b22c3`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.f65_arr_copied_room {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ)
  (type : Wasm.FuncType) (htype : type.results = []) (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 38 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId) (rest : List UInt8) (j k mlen F : ℕ)
  (live : List (ℕ × ℕ)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hroom : WNear.Binary.ParseStr.roomRun 2048 mlen 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (mlen +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hroom6 :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) mlen
      2048) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n 2048 mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs (↑a).toUTF8.toList rest j))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        ∃ hl',
                          ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
                            WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl'
                              (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) F))
```

## Bridge.Functions.BalanceOf297CopiedRoom

`WNear.Binary.BalanceOf297AbsentCall.copied_result_room` (hash `0000000055c11672`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_result_room {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (n hl F : ℕ) (live : List (ℕ × ℕ)) (out p c L : UInt32) (bs : List UInt8) (q : ℕ) (a : WNear.AccountId)
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs q a + 6) hl 2048) :
  n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
      n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
        n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
          n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 L ∗
            WNear.Binary.SerdeScratchValueDrop.cleanValue n 2048 hl live F 0 bs (↑a).toUTF8.toList q p c L ⊢
    ∃ hl',
      ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
        WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl'
          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs q F)
```

## Bridge.Functions.BalanceOf297DerefCompose

`WNear.Binary.BalanceOf297AbsentCall.array_deref_parser_through_cleanup` (hash `00000000287dc473`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24)
  (hptr : ip.toNat + bs.length < 2 ^ 32) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom : WNear.Binary.ParseStr.roomRun 2048 len 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (len +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) len
      2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                  A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                    A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                      A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                        WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                          A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                            WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                    (100 * cfg.regularOpCost +
                                                      (1000 * cfg.regularOpCost +
                                                          (45 * cfg.regularOpCost +
                                                            ((700 +
                                                                  96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                                                                cfg.regularOpCost +
                                                              WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs
                                                                (↑a).toUTF8.toList jsonRest j)) +
                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs
                                                            (j + 1) F)
                                                          h S a R)) ∗
                                                  g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                    WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                      WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                        WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                          n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                            NearLogic.mhostPt h ∗
                                                              WNear.Binary.AllocInv.heapInv n 2048 len
                                                                  ((ip.toNat, ic.toNat) :: live) F ∗
                                                                n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                                  n ↦[wms][ ip.toNat ] bs ∗
                                                                    n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                      n ↦[wms][ 1062392 ]
                                                                          WNear.Binary.ParseStr.escTable ∗
                                                                        n ↦[wms][ 1071704 ]
                                                                            WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                          n ↦[wms][ 1062712 ]
                                                                              WNear.Binary.SerdeEsc.hexTable ∗
                                                                            n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                              n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                    WasmLogic.bytes32 oldC ∗
                                                                                  n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                                    n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                                      n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                          WasmLogic.bytes32 oldD ∗
                                                                                        n ↦[wms][ (s + 24).toNat ]
                                                                                            derefOut ∗
                                                                                          n ↦[wms][ (s + 48).toNat ]
                                                                                              WasmLogic.bytes32 ip ++
                                                                                                (WasmLogic.bytes32 ic ++
                                                                                                  WasmLogic.bytes32
                                                                                                    (UInt32.ofNat
                                                                                                      bs.length)) ∗
                                                                                            n ↦[wms][ (s + 60).toNat ]
                                                                                                contractTail ∗
                                                                                              n ↦[wms][ (s + 8).toNat ]
                                                                                                  ob ∗
                                                                                                WNear.Binary.ToVec.tvData
                                                                                                    n ta ptr0 (A 759)
                                                                                                    (A 353) ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 144).toNat ]
                                                                                                      out ∗
                                                                                                    n ↦[wms][ s.toNat ]
                                                                                                        head ∗
                                                                                                      ▷ ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 129 (List.drop 21 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.deref_copied_parser_through_cleanup` (hash `00000000fef420a9`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.deref_copied_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24)
  (hptr : ip.toNat + bs.length < 2 ^ 32) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom : WNear.Binary.ParseStr.roomRun 2048 len 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (len +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) len
      2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                  A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                    A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                      A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                        WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                          A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                            WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                    (100 * cfg.regularOpCost +
                                                      (1000 * cfg.regularOpCost +
                                                          (45 * cfg.regularOpCost +
                                                            ((700 +
                                                                  96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                                                                cfg.regularOpCost +
                                                              WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs
                                                                (↑a).toUTF8.toList jsonRest j)) +
                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs
                                                            (j + 1) F)
                                                          h S a R)) ∗
                                                  g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                    WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                      WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                        WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                          n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                            NearLogic.mhostPt h ∗
                                                              WNear.Binary.AllocInv.heapInv n 2048 len
                                                                  ((ip.toNat, ic.toNat) :: live) F ∗
                                                                n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                                  n ↦[wms][ ip.toNat ] bs ∗
                                                                    n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                      n ↦[wms][ 1062392 ]
                                                                          WNear.Binary.ParseStr.escTable ∗
                                                                        n ↦[wms][ 1071704 ]
                                                                            WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                          n ↦[wms][ 1062712 ]
                                                                              WNear.Binary.SerdeEsc.hexTable ∗
                                                                            n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                              n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                    WasmLogic.bytes32 oldC ∗
                                                                                  n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                                    n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                                      n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                          WasmLogic.bytes32 oldD ∗
                                                                                        n ↦[wms][ (s + 24).toNat ]
                                                                                            derefOut ∗
                                                                                          n ↦[wms][ (s + 48).toNat ]
                                                                                              WasmLogic.bytes32 ip ++
                                                                                                (WasmLogic.bytes32 ic ++
                                                                                                  WasmLogic.bytes32
                                                                                                    (UInt32.ofNat
                                                                                                      bs.length)) ∗
                                                                                            n ↦[wms][ (s + 60).toNat ]
                                                                                                contractTail ∗
                                                                                              n ↦[wms][ (s + 8).toNat ]
                                                                                                  ob ∗
                                                                                                WNear.Binary.ToVec.tvData
                                                                                                    n ta ptr0 (A 759)
                                                                                                    (A 353) ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 144).toNat ]
                                                                                                      out ∗
                                                                                                    n ↦[wms][ s.toNat ]
                                                                                                        head ∗
                                                                                                      ▷ ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 129 (List.drop 21 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297DerefSetup

`WNear.Binary.BalanceOf297AbsentCall.deref_and_parser_setup` (hash `00000000a9a4c4ac`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.deref_and_parser_setup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[779]? = some (A 779))
  (hd : d + 1 < lim.maxCallDepth) (Cg R : ℕ) (s x1 : UInt32) (x2 : UInt64) (x3 ip ic il : UInt32) (old : List UInt8)
  (hold : old.length = 8) (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : WasmLogic.Post Wasm.NearState GF) :
  inst ↪[inst] mi ∗
      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
        NearLogic.credits Cg (100 * cfg.regularOpCost + R) ∗
          n ↦[wms][ (s + 24).toNat ] old ∗
            n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ++ (WasmLogic.bytes32 ic ++ WasmLogic.bytes32 il) ∗
              ▷
                (NearLogic.credits Cg R ∗
                    n ↦[wms][ (s + 24).toNat ] WasmLogic.bytes32 ip ∗
                      n ↦[wms][ (s + 24).toNat + 4 ] WasmLogic.bytes32 il ∗
                        n ↦[wms][ (s + 48).toNat ]
                          WasmLogic.bytes32 ip ++ (WasmLogic.bytes32 ic ++ WasmLogic.bytes32 il) -∗
                  Φ.normal [Wasm.Value.i32 (s + 88), Wasm.Value.i32 ip, Wasm.Value.i32 il]
                    (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 14 (List.drop 21 WNear.Binary.f297.body)) Φ
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

## Bridge.Functions.BalanceOf297ExpectCompose

`WNear.Binary.BalanceOf297AbsentCall.array_expect_deref_parser_through_cleanup` (hash `00000000506e1321`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_expect_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail optTail oldVec jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
  (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12)
  (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom : WNear.Binary.ParseStr.roomRun 2048 len 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (len +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) len
      2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                    A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                      A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                        A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                          WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                            A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                              WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                      (100 * cfg.regularOpCost +
                                                        (100 * cfg.regularOpCost +
                                                          (1000 * cfg.regularOpCost +
                                                              (45 * cfg.regularOpCost +
                                                                ((700 +
                                                                      96 *
                                                                        WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                                                                    cfg.regularOpCost +
                                                                  WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs
                                                                    (↑a).toUTF8.toList jsonRest j)) +
                                                            WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                              (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs
                                                                (j + 1) F)
                                                              h S a R))) ∗
                                                    g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                      WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                        WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                          WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                            n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                              NearLogic.mhostPt h ∗
                                                                WNear.Binary.AllocInv.heapInv n 2048 len
                                                                    ((ip.toNat, ic.toNat) :: live) F ∗
                                                                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 ip ∗
                                                                    n ↦[wms][ (s + 88).toNat + 4 ]
                                                                        WasmLogic.bytes32 ic ∗
                                                                      n ↦[wms][ (s + 88).toNat + 8 ]
                                                                          WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                                                                        n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                          n ↦[wms][ ip.toNat ] bs ∗
                                                                            n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                              n ↦[wms][ 1062392 ]
                                                                                  WNear.Binary.ParseStr.escTable ∗
                                                                                n ↦[wms][ 1071704 ]
                                                                                    WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                  n ↦[wms][ 1062712 ]
                                                                                      WNear.Binary.SerdeEsc.hexTable ∗
                                                                                    n ↦[wms][ (s + 104).toNat ]
                                                                                        stateTail ∗
                                                                                      n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                        n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                            WasmLogic.bytes32 oldC ∗
                                                                                          n ↦[wms][ (s + 140).toNat ]
                                                                                              destTail ∗
                                                                                            n ↦[wms][ (s + 32).toNat ]
                                                                                                oldB ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 32).toNat + 8 ]
                                                                                                  WasmLogic.bytes32
                                                                                                    oldD ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 24).toNat ]
                                                                                                    derefOut ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 48).toNat ]
                                                                                                      oldVec ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 60).toNat ]
                                                                                                        contractTail ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              8).toNat ]
                                                                                                          ob ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 137 (List.drop 13 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.expect_deref_parser_through_cleanup` (hash `000000002f009e4e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.expect_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail optTail oldVec jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
  (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12)
  (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom : WNear.Binary.ParseStr.roomRun 2048 len 0 [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (len +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK (WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a + 6) len
      2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                    A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                      A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                        A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                          WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                            A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                              WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                      (100 * cfg.regularOpCost +
                                                        (100 * cfg.regularOpCost +
                                                          (1000 * cfg.regularOpCost +
                                                              (45 * cfg.regularOpCost +
                                                                ((700 +
                                                                      96 *
                                                                        WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                                                                    cfg.regularOpCost +
                                                                  WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs
                                                                    (↑a).toUTF8.toList jsonRest j)) +
                                                            WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                              (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs
                                                                (j + 1) F)
                                                              h S a R))) ∗
                                                    g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                      WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                        WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                          WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                            n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                              NearLogic.mhostPt h ∗
                                                                WNear.Binary.AllocInv.heapInv n 2048 len
                                                                    ((ip.toNat, ic.toNat) :: live) F ∗
                                                                  n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 ip ∗
                                                                    n ↦[wms][ (s + 88).toNat + 4 ]
                                                                        WasmLogic.bytes32 ic ∗
                                                                      n ↦[wms][ (s + 88).toNat + 8 ]
                                                                          WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                                                                        n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                          n ↦[wms][ ip.toNat ] bs ∗
                                                                            n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                              n ↦[wms][ 1062392 ]
                                                                                  WNear.Binary.ParseStr.escTable ∗
                                                                                n ↦[wms][ 1071704 ]
                                                                                    WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                  n ↦[wms][ 1062712 ]
                                                                                      WNear.Binary.SerdeEsc.hexTable ∗
                                                                                    n ↦[wms][ (s + 104).toNat ]
                                                                                        stateTail ∗
                                                                                      n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                        n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                            WasmLogic.bytes32 oldC ∗
                                                                                          n ↦[wms][ (s + 140).toNat ]
                                                                                              destTail ∗
                                                                                            n ↦[wms][ (s + 32).toNat ]
                                                                                                oldB ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 32).toNat + 8 ]
                                                                                                  WasmLogic.bytes32
                                                                                                    oldD ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 24).toNat ]
                                                                                                    derefOut ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 48).toNat ]
                                                                                                      oldVec ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 60).toNat ]
                                                                                                        contractTail ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              8).toNat ]
                                                                                                          ob ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 137 (List.drop 13 WNear.Binary.f297.body)) Φ
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

## Bridge.Functions.BalanceOf297InitialRoom

`WNear.Binary.BalanceOf297AbsentCall.initial_input_and_copy_room` (hash `000000008f8d5c67`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_input_and_copy_room (bs : List UInt8) (a : WNear.AccountId) (q len : ℕ)
  (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 24)
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs q a +
        6)
      len 2048) :
  WNear.Binary.ReadRegister.RegOk 2048 len (some bs) ∧
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop q bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length)
```

## Bridge.Functions.BalanceOf297InitialRoomCompose

`WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_room` (hash `0000000035983043`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_room {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        len live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_room` (hash `000000000e5ce251`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_room {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        len live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

## Bridge.Functions.BalanceOf297InputCompose

`WNear.Binary.BalanceOf297AbsentCall.array_input_parser_through_cleanup` (hash `0000000050074eaa`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_input_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (halloc :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0
                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
      A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
        WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
          WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
            WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                  A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                    A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                      WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                  WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                    A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                      A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                        A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                          A 545 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                            A 456 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                              WNear.Binary.DropVec.dropCode inst mi A ∗
                                                A 68 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                  WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                    inst ↪[inst] mi ∗
                                                      NearLogic.credits Cg
                                                          (100 * cfg.regularOpCost +
                                                              WNear.Binary.EnvInput.cost527 cfg h0 +
                                                            (100 * cfg.regularOpCost +
                                                              (100 * cfg.regularOpCost +
                                                                (1000 * cfg.regularOpCost +
                                                                    (45 * cfg.regularOpCost +
                                                                      ((700 +
                                                                            96 *
                                                                              WNear.Binary.SerdeRead.wsLen
                                                                                (List.drop k bs)) *
                                                                          cfg.regularOpCost +
                                                                        WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0
                                                                          bs (↑a).toUTF8.toList jsonRest j)) +
                                                                  WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                    cfg
                                                                    (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                      bs (j + 1) 1)
                                                                    h S a R)))) ∗
                                                        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                          WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                  NearLogic.mhostPt h0 ∗
                                                                    WNear.Binary.AllocInv.heapInv n 2048 len live 1 ∗
                                                                      n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                        n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                          n ↦[wms][ 1062392 ]
                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                            n ↦[wms][ 1071704 ]
                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                              n ↦[wms][ 1062712 ]
                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                                  n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                    n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                        WasmLogic.bytes32 oldC ∗
                                                                                      n ↦[wms][ (s + 140).toNat ]
                                                                                          destTail ∗
                                                                                        n ↦[wms][ (s + 32).toNat ]
                                                                                            oldB ∗
                                                                                          n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldD ∗
                                                                                            n ↦[wms][ (s + 24).toNat ]
                                                                                                derefOut ∗
                                                                                              n ↦[wms][ (s + 48).toNat ]
                                                                                                  oldVec ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 60).toNat ]
                                                                                                    contractTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 8).toNat ]
                                                                                                      ob ∗
                                                                                                    WNear.Binary.ToVec.tvData
                                                                                                        n ta ptr0
                                                                                                        (A 759)
                                                                                                        (A 353) ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              144).toNat ]
                                                                                                          out ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) [Wasm.Value.i32 (s + 88)]
      (List.take 138 (List.drop 12 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.input_copied_parser_through_cleanup` (hash `000000006a30e338`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.input_copied_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (halloc :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0
                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
      A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
        WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
          WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
            WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                  A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                    A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                      WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                  WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                    A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                      A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                        A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                          A 545 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                            A 456 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                              WNear.Binary.DropVec.dropCode inst mi A ∗
                                                A 68 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                  WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                    inst ↪[inst] mi ∗
                                                      NearLogic.credits Cg
                                                          (100 * cfg.regularOpCost +
                                                              WNear.Binary.EnvInput.cost527 cfg h0 +
                                                            (100 * cfg.regularOpCost +
                                                              (100 * cfg.regularOpCost +
                                                                (1000 * cfg.regularOpCost +
                                                                    (45 * cfg.regularOpCost +
                                                                      ((700 +
                                                                            96 *
                                                                              WNear.Binary.SerdeRead.wsLen
                                                                                (List.drop k bs)) *
                                                                          cfg.regularOpCost +
                                                                        WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0
                                                                          bs (↑a).toUTF8.toList jsonRest j)) +
                                                                  WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                    cfg
                                                                    (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                      bs (j + 1) 1)
                                                                    h S a R)))) ∗
                                                        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                          WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                  NearLogic.mhostPt h0 ∗
                                                                    WNear.Binary.AllocInv.heapInv n 2048 len live 1 ∗
                                                                      n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                        n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                          n ↦[wms][ 1062392 ]
                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                            n ↦[wms][ 1071704 ]
                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                              n ↦[wms][ 1062712 ]
                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                                  n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                    n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                        WasmLogic.bytes32 oldC ∗
                                                                                      n ↦[wms][ (s + 140).toNat ]
                                                                                          destTail ∗
                                                                                        n ↦[wms][ (s + 32).toNat ]
                                                                                            oldB ∗
                                                                                          n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldD ∗
                                                                                            n ↦[wms][ (s + 24).toNat ]
                                                                                                derefOut ∗
                                                                                              n ↦[wms][ (s + 48).toNat ]
                                                                                                  oldVec ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 60).toNat ]
                                                                                                    contractTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 8).toNat ]
                                                                                                      ob ∗
                                                                                                    WNear.Binary.ToVec.tvData
                                                                                                        n ta ptr0
                                                                                                        (A 759)
                                                                                                        (A 353) ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              144).toNat ]
                                                                                                          out ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) [Wasm.Value.i32 (s + 88)]
      (List.take 138 (List.drop 12 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297InputExpect

`WNear.Binary.BalanceOf297AbsentCall.input_expect` (hash `00000000d8b9779a`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.input_expect {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ)
  (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[157]? = some (A 157)) (hd : d + 1 < lim.maxCallDepth) (Cg R : ℕ)
  (s x1 : UInt32) (x2 : UInt64) (x3 ip ic il : UInt32) (old : List UInt8) (hold : old.length = 12) (hp : ip ≠ 0)
  (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : WasmLogic.Post Wasm.NearState GF) :
  inst ↪[inst] mi ∗
      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
        NearLogic.credits Cg (100 * cfg.regularOpCost + R) ∗
          n ↦[wms][ (s + 48).toNat ] old ∗
            n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 ip ∗
              n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 ic ∗
                n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 il ∗
                  ▷
                    (NearLogic.credits Cg R ∗
                        n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 ip ∗
                          n ↦[wms][ (s + 88).toNat + 4 ] WasmLogic.bytes32 ic ∗
                            n ↦[wms][ (s + 88).toNat + 8 ] WasmLogic.bytes32 il ∗
                              n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ∗
                                n ↦[wms][ (s + 48).toNat + 4 ] WasmLogic.bytes32 ic ∗
                                  n ↦[wms][ (s + 48).toNat + 8 ] WasmLogic.bytes32 il -∗
                      Φ.normal [] (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 8 (List.drop 13 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297InputSetup

`WNear.Binary.BalanceOf297AbsentCall.array_input_setup_through_cleanup` (hash `0000000042f9bc38`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_input_setup_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (halloc :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0
                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
      A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
        WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
          WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
            WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                  A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                    A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                      WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                  WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                    A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                      A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                        A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                          A 545 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                            A 456 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                              WNear.Binary.DropVec.dropCode inst mi A ∗
                                                A 68 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                  WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                    inst ↪[inst] mi ∗
                                                      NearLogic.credits Cg
                                                          (3 * cfg.regularOpCost +
                                                            (100 * cfg.regularOpCost +
                                                                WNear.Binary.EnvInput.cost527 cfg h0 +
                                                              (100 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                  (1000 * cfg.regularOpCost +
                                                                      (45 * cfg.regularOpCost +
                                                                        ((700 +
                                                                              96 *
                                                                                WNear.Binary.SerdeRead.wsLen
                                                                                  (List.drop k bs)) *
                                                                            cfg.regularOpCost +
                                                                          WNear.Binary.SerdeStruct78Esc.costArray cfg 1
                                                                            0 bs (↑a).toUTF8.toList jsonRest j)) +
                                                                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                      cfg
                                                                      (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                        bs (j + 1) 1)
                                                                      h S a R))))) ∗
                                                        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                          WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                  NearLogic.mhostPt h0 ∗
                                                                    WNear.Binary.AllocInv.heapInv n 2048 len live 1 ∗
                                                                      n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                        n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                          n ↦[wms][ 1062392 ]
                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                            n ↦[wms][ 1071704 ]
                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                              n ↦[wms][ 1062712 ]
                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                                  n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                    n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                        WasmLogic.bytes32 oldC ∗
                                                                                      n ↦[wms][ (s + 140).toNat ]
                                                                                          destTail ∗
                                                                                        n ↦[wms][ (s + 32).toNat ]
                                                                                            oldB ∗
                                                                                          n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldD ∗
                                                                                            n ↦[wms][ (s + 24).toNat ]
                                                                                                derefOut ∗
                                                                                              n ↦[wms][ (s + 48).toNat ]
                                                                                                  oldVec ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 60).toNat ]
                                                                                                    contractTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 8).toNat ]
                                                                                                      ob ∗
                                                                                                    WNear.Binary.ToVec.tvData
                                                                                                        n ta ptr0
                                                                                                        (A 759)
                                                                                                        (A 353) ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              144).toNat ]
                                                                                                          out ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 141 (List.drop 9 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.input_setup_through_cleanup` (hash `0000000075ba2409`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.input_setup_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (halloc :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.VecFromElem.roomFor
          (len' +
            WNear.Binary.ScratchGrow.growthPages 0 0
                (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
              65536)
          2048 (UInt32.ofNat (↑a).toUTF8.toList.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
      A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
        WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
          WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
            WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                  A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                    A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                      WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                  WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                    A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                      A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                        A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                          A 545 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                            A 456 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                              WNear.Binary.DropVec.dropCode inst mi A ∗
                                                A 68 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                  WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                    inst ↪[inst] mi ∗
                                                      NearLogic.credits Cg
                                                          (3 * cfg.regularOpCost +
                                                            (100 * cfg.regularOpCost +
                                                                WNear.Binary.EnvInput.cost527 cfg h0 +
                                                              (100 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                  (1000 * cfg.regularOpCost +
                                                                      (45 * cfg.regularOpCost +
                                                                        ((700 +
                                                                              96 *
                                                                                WNear.Binary.SerdeRead.wsLen
                                                                                  (List.drop k bs)) *
                                                                            cfg.regularOpCost +
                                                                          WNear.Binary.SerdeStruct78Esc.costArray cfg 1
                                                                            0 bs (↑a).toUTF8.toList jsonRest j)) +
                                                                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                      cfg
                                                                      (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                        bs (j + 1) 1)
                                                                      h S a R))))) ∗
                                                        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                          WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                  NearLogic.mhostPt h0 ∗
                                                                    WNear.Binary.AllocInv.heapInv n 2048 len live 1 ∗
                                                                      n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                        n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                          n ↦[wms][ 1062392 ]
                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                            n ↦[wms][ 1071704 ]
                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                              n ↦[wms][ 1062712 ]
                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                                  n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                    n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                        WasmLogic.bytes32 oldC ∗
                                                                                      n ↦[wms][ (s + 140).toNat ]
                                                                                          destTail ∗
                                                                                        n ↦[wms][ (s + 32).toNat ]
                                                                                            oldB ∗
                                                                                          n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldD ∗
                                                                                            n ↦[wms][ (s + 24).toNat ]
                                                                                                derefOut ∗
                                                                                              n ↦[wms][ (s + 48).toNat ]
                                                                                                  oldVec ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 60).toNat ]
                                                                                                    contractTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 8).toNat ]
                                                                                                      ob ∗
                                                                                                    WNear.Binary.ToVec.tvData
                                                                                                        n ta ptr0
                                                                                                        (A 759)
                                                                                                        (A 353) ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              144).toNat ]
                                                                                                          out ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 141 (List.drop 9 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ObjectCompose

`WNear.Binary.BalanceOf297AbsentCall.object_absent_body` (hash `000000006df5ec57`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_body {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ)
  (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32) (len : ℕ) (a : WNear.AccountId)
  (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (N : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs) (hbase : len = WNear.Binary.InitialState.memLen)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                          NearLogic.credits Cg
                                                              (475 * cfg.regularOpCost +
                                                                (3 * cfg.regularOpCost +
                                                                  (100 * cfg.regularOpCost +
                                                                      WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                    (100 * cfg.regularOpCost +
                                                                      (100 * cfg.regularOpCost +
                                                                        (1000 * cfg.regularOpCost +
                                                                            WNear.Binary.SerdeObjectNoEsc.parserCost cfg
                                                                              1 bs jsonRest N +
                                                                          WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                            cfg 2 h S a R)))))) ∗
                                                            g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                              WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                  n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                    ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                      ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                        WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                            n 0 0 0 k3 ∗
                                                                          WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                            n ↦[wms][ 1050188 + 36 ]
                                                                                WNear.Binary.Interface.dataWord
                                                                                  (1050188 + 36) ∗
                                                                              ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                                WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                    idx ta (A 578) ∗
                                                                                  n ↦[wms][ 1049788 ]
                                                                                      WNear.Binary.StateRead.stateKey ∗
                                                                                    NearLogic.mhostPt h0 ∗
                                                                                      WNear.Binary.AllocInv.heapInv n
                                                                                          2048 len live 1 ∗
                                                                                        n ↦[wms][ (s + 88).toNat ]
                                                                                            oldOpt ∗
                                                                                          n ↦[wms][ (s + 100).toNat ]
                                                                                              optTail ∗
                                                                                            n ↦[wms][ 1062392 ]
                                                                                                WNear.Binary.ParseStr.escTable ∗
                                                                                              n ↦[wms][ 1071704 ]
                                                                                                  WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                                n ↦[wms][ 1062712 ]
                                                                                                    WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                  WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                                      n ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                            104).toNat ]
                                                                                                        stateTail ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              128).toNat ]
                                                                                                          oldA ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.object_deref_parser_through_cleanup` (hash `00000000bc4ef69f`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut jsonRest derefOut : List UInt8) (N : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24)
  (hptr : ip.toNat + bs.length < 2 ^ 32) (hnb : 92 ∉ bs)
  (hL :
    len = WNear.Binary.InitialState.memLen ∨
      len = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                  A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                    A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                      A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                        WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                          A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                            WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                              A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                  A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                    A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                      A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                        WNear.Binary.DropVec.dropCode inst mi A ∗
                                          A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                            WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                              inst ↪[inst] mi ∗
                                                WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                  NearLogic.credits Cg
                                                      (100 * cfg.regularOpCost +
                                                        (1000 * cfg.regularOpCost +
                                                            WNear.Binary.SerdeObjectNoEsc.parserCost cfg F bs jsonRest
                                                              N +
                                                          WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                            (max F 1 + 1) h S a R)) ∗
                                                    g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                      WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                        WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                          WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                            n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                              NearLogic.mhostPt h ∗
                                                                WNear.Binary.AllocInv.heapInv n 2048 len
                                                                    ((ip.toNat, ic.toNat) :: live) F ∗
                                                                  n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                                    n ↦[wms][ ip.toNat ] bs ∗
                                                                      n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                        n ↦[wms][ 1062392 ]
                                                                            WNear.Binary.ParseStr.escTable ∗
                                                                          n ↦[wms][ 1071704 ]
                                                                              WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                            n ↦[wms][ 1062712 ]
                                                                                WNear.Binary.SerdeEsc.hexTable ∗
                                                                              WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                  n ∗
                                                                                n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                                  n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                    n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                        WasmLogic.bytes32 oldC ∗
                                                                                      n ↦[wms][ (s + 140).toNat ]
                                                                                          destTail ∗
                                                                                        n ↦[wms][ (s + 32).toNat ]
                                                                                            oldB ∗
                                                                                          n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldD ∗
                                                                                            n ↦[wms][ (s + 24).toNat ]
                                                                                                derefOut ∗
                                                                                              n ↦[wms][ (s + 48).toNat ]
                                                                                                  WasmLogic.bytes32
                                                                                                      ip ++
                                                                                                    (WasmLogic.bytes32
                                                                                                        ic ++
                                                                                                      WasmLogic.bytes32
                                                                                                        (UInt32.ofNat
                                                                                                          bs.length)) ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 60).toNat ]
                                                                                                    contractTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 8).toNat ]
                                                                                                      ob ∗
                                                                                                    WNear.Binary.ToVec.tvData
                                                                                                        n ta ptr0
                                                                                                        (A 759)
                                                                                                        (A 353) ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              144).toNat ]
                                                                                                          out ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 129 (List.drop 21 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.object_expect_deref_parser_through_cleanup` (hash `00000000b92632c5`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_expect_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail optTail oldVec jsonRest derefOut : List UInt8) (N : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
  (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12)
  (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32) (hnb : 92 ∉ bs)
  (hL :
    len = WNear.Binary.InitialState.memLen ∨
      len = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
            A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
              A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                    A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                      A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                        A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                          WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                            A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                              WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                  A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                    A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                      A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                        A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                          WNear.Binary.DropVec.dropCode inst mi A ∗
                                            A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                              WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                inst ↪[inst] mi ∗
                                                  WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                    NearLogic.credits Cg
                                                        (100 * cfg.regularOpCost +
                                                          (100 * cfg.regularOpCost +
                                                            (1000 * cfg.regularOpCost +
                                                                WNear.Binary.SerdeObjectNoEsc.parserCost cfg F bs
                                                                  jsonRest N +
                                                              WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                                (max F 1 + 1) h S a R))) ∗
                                                      g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                        WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                          WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                            WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                              n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                NearLogic.mhostPt h ∗
                                                                  WNear.Binary.AllocInv.heapInv n 2048 len
                                                                      ((ip.toNat, ic.toNat) :: live) F ∗
                                                                    n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 ip ∗
                                                                      n ↦[wms][ (s + 88).toNat + 4 ]
                                                                          WasmLogic.bytes32 ic ∗
                                                                        n ↦[wms][ (s + 88).toNat + 8 ]
                                                                            WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                                                                          n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                            n ↦[wms][ ip.toNat ] bs ∗
                                                                              n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                                n ↦[wms][ 1062392 ]
                                                                                    WNear.Binary.ParseStr.escTable ∗
                                                                                  n ↦[wms][ 1071704 ]
                                                                                      WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                    n ↦[wms][ 1062712 ]
                                                                                        WNear.Binary.SerdeEsc.hexTable ∗
                                                                                      WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                          n ∗
                                                                                        n ↦[wms][ (s + 104).toNat ]
                                                                                            stateTail ∗
                                                                                          n ↦[wms][ (s + 128).toNat ]
                                                                                              oldA ∗
                                                                                            n ↦[wms][
                                                                                                (s + 128).toNat + 8 ]
                                                                                                WasmLogic.bytes32 oldC ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 140).toNat ]
                                                                                                  destTail ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 32).toNat ]
                                                                                                    oldB ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 32).toNat +
                                                                                                        8 ]
                                                                                                      WasmLogic.bytes32
                                                                                                        oldD ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 24).toNat ]
                                                                                                        derefOut ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              48).toNat ]
                                                                                                          oldVec ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 137 (List.drop 13 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.object_input_parser_through_cleanup` (hash `000000007c626cff`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_input_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (N : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4)
  (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs)
  (hbase : len = WNear.Binary.InitialState.memLen) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
      A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
        WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
          WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
            WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                  A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                    A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                      WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                  WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                    A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                      A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                        A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                          A 545 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                            A 456 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                              WNear.Binary.DropVec.dropCode inst mi A ∗
                                                A 68 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                  WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                    inst ↪[inst] mi ∗
                                                      WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                        NearLogic.credits Cg
                                                            (100 * cfg.regularOpCost +
                                                                WNear.Binary.EnvInput.cost527 cfg h0 +
                                                              (100 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                  (1000 * cfg.regularOpCost +
                                                                      WNear.Binary.SerdeObjectNoEsc.parserCost cfg 1 bs
                                                                        jsonRest N +
                                                                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                      cfg 2 h S a R)))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                            WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                              WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                  n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                    NearLogic.mhostPt h0 ∗
                                                                      WNear.Binary.AllocInv.heapInv n 2048 len live 1 ∗
                                                                        n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                          n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                            n ↦[wms][ 1062392 ]
                                                                                WNear.Binary.ParseStr.escTable ∗
                                                                              n ↦[wms][ 1071704 ]
                                                                                  WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                n ↦[wms][ 1062712 ]
                                                                                    WNear.Binary.SerdeEsc.hexTable ∗
                                                                                  WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                      n ∗
                                                                                    n ↦[wms][ (s + 104).toNat ]
                                                                                        stateTail ∗
                                                                                      n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                        n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                            WasmLogic.bytes32 oldC ∗
                                                                                          n ↦[wms][ (s + 140).toNat ]
                                                                                              destTail ∗
                                                                                            n ↦[wms][ (s + 32).toNat ]
                                                                                                oldB ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 32).toNat + 8 ]
                                                                                                  WasmLogic.bytes32
                                                                                                    oldD ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 24).toNat ]
                                                                                                    derefOut ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 48).toNat ]
                                                                                                      oldVec ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 60).toNat ]
                                                                                                        contractTail ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              8).toNat ]
                                                                                                          ob ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) [Wasm.Value.i32 (s + 88)]
      (List.take 138 (List.drop 12 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.object_input_setup_through_cleanup` (hash `00000000717af782`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_input_setup_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (N : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4)
  (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs)
  (hbase : len = WNear.Binary.InitialState.memLen) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
      A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
        WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
          WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
            WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                  A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                    A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                      WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                  WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                    A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                      A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                        A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                          A 545 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                            A 456 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                              WNear.Binary.DropVec.dropCode inst mi A ∗
                                                A 68 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                  WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                    inst ↪[inst] mi ∗
                                                      WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                        NearLogic.credits Cg
                                                            (3 * cfg.regularOpCost +
                                                              (100 * cfg.regularOpCost +
                                                                  WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                (100 * cfg.regularOpCost +
                                                                  (100 * cfg.regularOpCost +
                                                                    (1000 * cfg.regularOpCost +
                                                                        WNear.Binary.SerdeObjectNoEsc.parserCost cfg 1
                                                                          bs jsonRest N +
                                                                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                        cfg 2 h S a R))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                            WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                              WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                  n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                    NearLogic.mhostPt h0 ∗
                                                                      WNear.Binary.AllocInv.heapInv n 2048 len live 1 ∗
                                                                        n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                          n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                            n ↦[wms][ 1062392 ]
                                                                                WNear.Binary.ParseStr.escTable ∗
                                                                              n ↦[wms][ 1071704 ]
                                                                                  WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                n ↦[wms][ 1062712 ]
                                                                                    WNear.Binary.SerdeEsc.hexTable ∗
                                                                                  WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                      n ∗
                                                                                    n ↦[wms][ (s + 104).toNat ]
                                                                                        stateTail ∗
                                                                                      n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                        n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                            WasmLogic.bytes32 oldC ∗
                                                                                          n ↦[wms][ (s + 140).toNat ]
                                                                                              destTail ∗
                                                                                            n ↦[wms][ (s + 32).toNat ]
                                                                                                oldB ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 32).toNat + 8 ]
                                                                                                  WasmLogic.bytes32
                                                                                                    oldD ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 24).toNat ]
                                                                                                    derefOut ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 48).toNat ]
                                                                                                      oldVec ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 60).toNat ]
                                                                                                        contractTail ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              8).toNat ]
                                                                                                          ob ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 141 (List.drop 9 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.object_parser_through_cleanup` (hash `0000000015deb43d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut jsonRest : List UInt8) (N : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8)
  (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
  (hinput : bs.length + tail.length = ic.toNat) (hparserOut : parserOut.length = 16) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState)
  (S : WNear.State) (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32) (hnb : 92 ∉ bs)
  (hL :
    len = WNear.Binary.InitialState.memLen ∨
      len = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) =
      bs.length) :
  (WNear.Binary.SerdeObjectNoEsc.parserCode n inst mi A ∗
      A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                            (1000 * cfg.regularOpCost +
                                                WNear.Binary.SerdeObjectNoEsc.parserCost cfg F bs jsonRest N +
                                              WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg (max F 1 + 1) h
                                                S a R) ∗
                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                            WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                              WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                  n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                    NearLogic.mhostPt h ∗
                                                      WNear.Binary.AllocInv.heapInv n 2048 len
                                                          ((ip.toNat, ic.toNat) :: live) F ∗
                                                        n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                          n ↦[wms][ ip.toNat ] bs ∗
                                                            n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                              n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                                                n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                  n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                                                    WNear.Binary.SerdeObjectNoEsc.parserStatics n ∗
                                                                      n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                        n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                          n ↦[wms][ (s + 128).toNat + 8 ]
                                                                              WasmLogic.bytes32 oldC ∗
                                                                            n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                              n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                                n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                    WasmLogic.bytes32 oldD ∗
                                                                                  n ↦[wms][ (s + 48).toNat ]
                                                                                      WasmLogic.bytes32 ip ∗
                                                                                    n ↦[wms][ (s + 48).toNat + 4 ]
                                                                                        WasmLogic.bytes32 ic ∗
                                                                                      n ↦[wms][ (s + 48).toNat + 8 ]
                                                                                          WasmLogic.bytes32
                                                                                            (UInt32.ofNat bs.length) ∗
                                                                                        n ↦[wms][ (s + 60).toNat ]
                                                                                            contractTail ∗
                                                                                          n ↦[wms][ (s + 8).toNat ] ob ∗
                                                                                            WNear.Binary.ToVec.tvData n
                                                                                                ta ptr0 (A 759)
                                                                                                (A 353) ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 144).toNat ]
                                                                                                  out ∗
                                                                                                n ↦[wms][ s.toNat ]
                                                                                                    head ∗
                                                                                                  ▷ ∀ p c, ⋯) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)
      [Wasm.Value.i32 (s + 88), Wasm.Value.i32 ip, Wasm.Value.i32 (UInt32.ofNat bs.length)]
      (List.take 115 (List.drop 35 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ObjectParser

`WNear.Binary.SerdeObjectNoEsc.parserCode` (hash `8d8267c1869967e3`)

```lean
def WNear.Binary.SerdeObjectNoEsc.parserCode {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n inst : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) : Iris.IProp GF :=
  fun A =>
    iprop(WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
        WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
          WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
            WNear.Binary.DropVec.dropCode inst mi A ∗
              WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    inst ↪[inst] mi)
```

`WNear.Binary.SerdeObjectNoEsc.parserCost` (hash `36a97dc53ca921cf`)

```lean
def WNear.Binary.SerdeObjectNoEsc.parserCost (cfg : Wasm.Near.WasmConfig) (F : ℕ) (bs rest : List UInt8) (N : ℕ) : ℕ :=
  45 * cfg.regularOpCost +
      (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)) *
        cfg.regularOpCost +
    WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
      (WNear.Binary.SerdeAcctHyp.K169 cfg bs F) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
      (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0
```

`WNear.Binary.SerdeObjectNoEsc.parserStatics` (hash `473ffc4467a2989e`)

```lean
def WNear.Binary.SerdeObjectNoEsc.parserStatics {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n : ℕ) :
  Iris.IProp GF :=
  fun n =>
    iprop(n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
        n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes)
```

`WNear.Binary.SerdeObjectNoEsc.parser_contract` (hash `0000000029614313`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.parser_contract {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta Cg : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32)
  (ob bs rest : List UInt8) (a : WNear.AccountId) (N mlen F : ℕ) (live : List (ℕ × ℕ)) (hd : d + 45 < lim.maxCallDepth)
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hnb : 92 ∉ bs)
  (hL :
    mlen = WNear.Binary.InitialState.memLen ∨
      mlen = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hend : bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) = bs.length) :
  WNear.Binary.BalanceOf297AbsentCall.ParserCallContract cfg lim d inst mi A n g ta Cg gt sp out ptr idx ob bs a mlen
    live F (WNear.Binary.SerdeObjectNoEsc.parserCost cfg F bs rest N) (max F 1 + 1)
    (WNear.Binary.SerdeObjectNoEsc.parserCode n inst mi A) (WNear.Binary.SerdeObjectNoEsc.parserStatics n)
```

## Bridge.Functions.BalanceOf297ObjectRoom

`WNear.Binary.BalanceOf297AbsentCall.object_result_room` (hash `00000000d1a15405`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_result_room {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (n hl F : ℕ) (live : List (ℕ × ℕ)) (out p c L : UInt32) (a : WNear.AccountId)
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 7 hl 2048) :
  n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
      n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
        n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
          n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 L ∗
            WNear.Binary.SerdeObjectNoEsc.cleanObject n 2048 hl live F (↑a).toUTF8.toList p c L ⊢
    ∃ hl',
      ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
        WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl' (max F 1 + 1)
```

`WNear.Binary.SerdeObjectNoEsc.f65_obj_room` (hash `000000009e8a1304`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.f65_obj_room {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 45 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (N k mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hnb : 92 ∉ bs)
  (hL :
    mlen = WNear.Binary.InitialState.memLen ∨
      mlen = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hk : k = bs.length - rest.length) (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n 2048 mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                              n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                                n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
              (WNear.Binary.SerdeAcctHyp.K169 cfg bs F) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
              (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                          n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes ∗
                            ∃ hl',
                              ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
                                WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl' (max F 1 + 1))
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

## Bridge.Functions.BalanceOf297ParserFamily

`WNear.Binary.BalanceOf297AbsentCall.ParserFamily` (hash `7213ed2d99ed5d3e`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.ParserFamily {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (gt : Wasm.GlobalType) (bs : List UInt8) (a : WNear.AccountId) (F parseGas outF : ℕ) (Cd : Iris.IProp GF) : Prop :=
  fun Cd =>
    ∀ (Cg d : ℕ) (sp out ptr idx : UInt32) (ob : List UInt8) (len : ℕ) (live : List (ℕ × ℕ)),
      d + 45 < lim.maxCallDepth →
        ob.length = 16 →
          out.toNat + 16 ≤ 2 ^ 32 →
            bs.length < 2 ^ 24 →
              ptr.toNat + bs.length < 2 ^ 32 →
                448 ≤ sp.toNat →
                  sp.toNat % 8 = 0 →
                    len = WNear.Binary.InitialState.memLen ∨
                        len =
                          WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen
                            (UInt32.ofNat bs.length) →
                      WNear.Binary.BalanceOf297AbsentCall.ParserCallContract cfg lim d inst mi A n
                        g ta Cg gt sp out ptr idx ob bs a len live F parseGas outF Cd
                        (WNear.Binary.SerdeObjectNoEsc.parserStatics n)
```

`WNear.Binary.BalanceOf297AbsentCall.provider_absent_body` (hash `00000000b1d2239f`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.provider_absent_body {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec derefOut : List UInt8)
  (parseGas outF : ℕ) (Cd : Iris.IProp GF) [Iris.BI.Persistent Cd]
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (hbase : len = WNear.Binary.InitialState.memLen) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
  (h0 h : Wasm.NearState) (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hFamily : WNear.Binary.BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
  Cd ∗
      WNear.Binary.FtTotalSupply.codeA inst mi A ∗
        WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
          A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
            WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
              WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
                WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                  A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                    A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                      A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                        A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                          WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                            A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                              A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                                A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                  WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                    A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                      WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                        A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                          A 158 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                            A 779 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                              A 545 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                                A 456 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                  WNear.Binary.DropVec.dropCode inst mi A ∗
                                                    A 68 ↪[wf]
                                                        Wasm.FuncInst.wasm WNear.Binary.types[0]! inst
                                                          WNear.Binary.f68 ∗
                                                      WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                        inst ↪[inst] mi ∗
                                                          WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                            NearLogic.credits Cg
                                                                (475 * cfg.regularOpCost +
                                                                  (3 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                        WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                      (100 * cfg.regularOpCost +
                                                                        (100 * cfg.regularOpCost +
                                                                          (1000 * cfg.regularOpCost + parseGas +
                                                                            WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                              cfg outF h S a R)))))) ∗
                                                              g ↦[wg]
                                                                  { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                                WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                  WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                    n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                      ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                        ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                          WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                              n 0 0 0 k3 ∗
                                                                            WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                              n ↦[wms][ 1050188 + 36 ]
                                                                                  WNear.Binary.Interface.dataWord
                                                                                    (1050188 + 36) ∗
                                                                                ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                                  WNear.Binary.AllocFirstFit.vt n
                                                                                      1057464 idx ta (A 578) ∗
                                                                                    n ↦[wms][ 1049788 ]
                                                                                        WNear.Binary.StateRead.stateKey ∗
                                                                                      NearLogic.mhostPt h0 ∗
                                                                                        WNear.Binary.AllocInv.heapInv n
                                                                                            2048 len live 1 ∗
                                                                                          n ↦[wms][ (s + 88).toNat ]
                                                                                              oldOpt ∗
                                                                                            n ↦[wms][ (s + 100).toNat ]
                                                                                                optTail ∗
                                                                                              n ↦[wms][ 1062392 ]
                                                                                                  WNear.Binary.ParseStr.escTable ∗
                                                                                                n ↦[wms][ 1071704 ]
                                                                                                    WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                                  n ↦[wms][ 1062712 ]
                                                                                                      WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                    WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                                        n ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              104).toNat ]
                                                                                                          stateTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.provider_deref_parser_through_cleanup` (hash `00000000ea474376`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.provider_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail parserOut derefOut : List UInt8) (parseGas outF : ℕ) (Cd : Iris.IProp GF) [Iris.BI.Persistent Cd]
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24)
  (hptr : ip.toNat + bs.length < 2 ^ 32)
  (hL :
    len = WNear.Binary.InitialState.memLen ∨
      len = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hFamily : WNear.Binary.BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
  Cd ∗
      WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
        WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
          WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                  WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                    A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                      A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                        A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                          WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                            A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                              WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                  A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                    A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                      A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                        A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                          WNear.Binary.DropVec.dropCode inst mi A ∗
                                            A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                              WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                inst ↪[inst] mi ∗
                                                  WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                    NearLogic.credits Cg
                                                        (100 * cfg.regularOpCost +
                                                          (1000 * cfg.regularOpCost + parseGas +
                                                            WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                                                              outF h S a R)) ∗
                                                      g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                        WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                          WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                            WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                              n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                NearLogic.mhostPt h ∗
                                                                  WNear.Binary.AllocInv.heapInv n 2048 len
                                                                      ((ip.toNat, ic.toNat) :: live) F ∗
                                                                    n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                                      n ↦[wms][ ip.toNat ] bs ∗
                                                                        n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                          n ↦[wms][ 1062392 ]
                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                            n ↦[wms][ 1071704 ]
                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                              n ↦[wms][ 1062712 ]
                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                    n ∗
                                                                                  n ↦[wms][ (s + 104).toNat ]
                                                                                      stateTail ∗
                                                                                    n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                                      n ↦[wms][ (s + 128).toNat + 8 ]
                                                                                          WasmLogic.bytes32 oldC ∗
                                                                                        n ↦[wms][ (s + 140).toNat ]
                                                                                            destTail ∗
                                                                                          n ↦[wms][ (s + 32).toNat ]
                                                                                              oldB ∗
                                                                                            n ↦[wms][
                                                                                                (s + 32).toNat + 8 ]
                                                                                                WasmLogic.bytes32 oldD ∗
                                                                                              n ↦[wms][ (s + 24).toNat ]
                                                                                                  derefOut ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 48).toNat ]
                                                                                                    WasmLogic.bytes32
                                                                                                        ip ++
                                                                                                      (WasmLogic.bytes32
                                                                                                          ic ++
                                                                                                        WasmLogic.bytes32
                                                                                                          (UInt32.ofNat
                                                                                                            bs.length)) ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 60).toNat ]
                                                                                                      contractTail ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 8).toNat ]
                                                                                                        ob ∗
                                                                                                      WNear.Binary.ToVec.tvData
                                                                                                          n ta ptr0
                                                                                                          (A 759)
                                                                                                          (A 353) ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 129 (List.drop 21 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.provider_expect_deref_parser_through_cleanup` (hash `0000000002c570b7`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.provider_expect_deref_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (bs tail optTail oldVec derefOut : List UInt8) (parseGas outF : ℕ) (Cd : Iris.IProp GF) [Iris.BI.Persistent Cd]
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
  (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12)
  (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
  (hL :
    len = WNear.Binary.InitialState.memLen ∨
      len = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hFamily : WNear.Binary.BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
  Cd ∗
      WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
        WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
          WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                  A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                    WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                            WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                          A 456 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                            WNear.Binary.DropVec.dropCode inst mi A ∗
                                              A 68 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                  inst ↪[inst] mi ∗
                                                    WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                      NearLogic.credits Cg
                                                          (100 * cfg.regularOpCost +
                                                            (100 * cfg.regularOpCost +
                                                              (1000 * cfg.regularOpCost + parseGas +
                                                                WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                  cfg outF h S a R))) ∗
                                                        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                          WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                                n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                                  NearLogic.mhostPt h ∗
                                                                    WNear.Binary.AllocInv.heapInv n 2048 len
                                                                        ((ip.toNat, ic.toNat) :: live) F ∗
                                                                      n ↦[wms][ (s + 88).toNat ] WasmLogic.bytes32 ip ∗
                                                                        n ↦[wms][ (s + 88).toNat + 4 ]
                                                                            WasmLogic.bytes32 ic ∗
                                                                          n ↦[wms][ (s + 88).toNat + 8 ]
                                                                              WasmLogic.bytes32
                                                                                (UInt32.ofNat bs.length) ∗
                                                                            n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                              n ↦[wms][ ip.toNat ] bs ∗
                                                                                n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                                                  n ↦[wms][ 1062392 ]
                                                                                      WNear.Binary.ParseStr.escTable ∗
                                                                                    n ↦[wms][ 1071704 ]
                                                                                        WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                      n ↦[wms][ 1062712 ]
                                                                                          WNear.Binary.SerdeEsc.hexTable ∗
                                                                                        WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                            n ∗
                                                                                          n ↦[wms][ (s + 104).toNat ]
                                                                                              stateTail ∗
                                                                                            n ↦[wms][ (s + 128).toNat ]
                                                                                                oldA ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 128).toNat + 8 ]
                                                                                                  WasmLogic.bytes32
                                                                                                    oldC ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 140).toNat ]
                                                                                                    destTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 32).toNat ]
                                                                                                      oldB ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 32).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldD ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              24).toNat ]
                                                                                                          derefOut ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 137 (List.drop 13 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.provider_input_parser_through_cleanup` (hash `0000000072846e22`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.provider_input_parser_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec derefOut : List UInt8)
  (parseGas outF : ℕ) (Cd : Iris.IProp GF) [Iris.BI.Persistent Cd]
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4)
  (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24)
  (hbase : len = WNear.Binary.InitialState.memLen) (hob : ob.length = 16) (hstateTail : stateTail.length = 24)
  (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4) (hA : oldA.length = 8)
  (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hFamily : WNear.Binary.BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
  Cd ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                          NearLogic.credits Cg
                                                              (100 * cfg.regularOpCost +
                                                                  WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                (100 * cfg.regularOpCost +
                                                                  (100 * cfg.regularOpCost +
                                                                    (1000 * cfg.regularOpCost + parseGas +
                                                                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                        cfg outF h S a R)))) ∗
                                                            g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                              WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                                WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                  WNear.Binary.AllocFirstFit.vt n 1057464 idx ta
                                                                      (A 578) ∗
                                                                    n ↦[wms][ 1049788 ]
                                                                        WNear.Binary.StateRead.stateKey ∗
                                                                      NearLogic.mhostPt h0 ∗
                                                                        WNear.Binary.AllocInv.heapInv n 2048 len live
                                                                            1 ∗
                                                                          n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                            n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                              n ↦[wms][ 1062392 ]
                                                                                  WNear.Binary.ParseStr.escTable ∗
                                                                                n ↦[wms][ 1071704 ]
                                                                                    WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                  n ↦[wms][ 1062712 ]
                                                                                      WNear.Binary.SerdeEsc.hexTable ∗
                                                                                    WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                        n ∗
                                                                                      n ↦[wms][ (s + 104).toNat ]
                                                                                          stateTail ∗
                                                                                        n ↦[wms][ (s + 128).toNat ]
                                                                                            oldA ∗
                                                                                          n ↦[wms][
                                                                                              (s + 128).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldC ∗
                                                                                            n ↦[wms][ (s + 140).toNat ]
                                                                                                destTail ∗
                                                                                              n ↦[wms][ (s + 32).toNat ]
                                                                                                  oldB ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 32).toNat + 8 ]
                                                                                                    WasmLogic.bytes32
                                                                                                      oldD ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 24).toNat ]
                                                                                                      derefOut ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 48).toNat ]
                                                                                                        oldVec ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              60).toNat ]
                                                                                                          contractTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) [Wasm.Value.i32 (s + 88)]
      (List.take 138 (List.drop 12 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.BalanceOf297AbsentCall.provider_input_setup_through_cleanup` (hash `000000007622c678`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.provider_input_setup_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec derefOut : List UInt8)
  (parseGas outF : ℕ) (Cd : Iris.IProp GF) [Iris.BI.Persistent Cd]
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4)
  (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8) (hlen : bs.length < 2 ^ 24)
  (hbase : len = WNear.Binary.InitialState.memLen) (hob : ob.length = 16) (hstateTail : stateTail.length = 24)
  (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4) (hA : oldA.length = 8)
  (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk 2048 len (some bs)) (S : WNear.State) (st : Near.TrieOverlay.State)
  (hv : h.storage WNear.stateKey = some (WNear.header S)) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hFamily : WNear.Binary.BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
  Cd ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
                                                          NearLogic.credits Cg
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost + parseGas +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg outF h S a R))))) ∗
                                                            g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                                              WNear.Binary.EnvInput.ifaceI n ta A ∗
                                                                WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                  WNear.Binary.AllocFirstFit.vt n 1057464 idx ta
                                                                      (A 578) ∗
                                                                    n ↦[wms][ 1049788 ]
                                                                        WNear.Binary.StateRead.stateKey ∗
                                                                      NearLogic.mhostPt h0 ∗
                                                                        WNear.Binary.AllocInv.heapInv n 2048 len live
                                                                            1 ∗
                                                                          n ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                                                            n ↦[wms][ (s + 100).toNat ] optTail ∗
                                                                              n ↦[wms][ 1062392 ]
                                                                                  WNear.Binary.ParseStr.escTable ∗
                                                                                n ↦[wms][ 1071704 ]
                                                                                    WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                  n ↦[wms][ 1062712 ]
                                                                                      WNear.Binary.SerdeEsc.hexTable ∗
                                                                                    WNear.Binary.SerdeObjectNoEsc.parserStatics
                                                                                        n ∗
                                                                                      n ↦[wms][ (s + 104).toNat ]
                                                                                          stateTail ∗
                                                                                        n ↦[wms][ (s + 128).toNat ]
                                                                                            oldA ∗
                                                                                          n ↦[wms][
                                                                                              (s + 128).toNat + 8 ]
                                                                                              WasmLogic.bytes32 oldC ∗
                                                                                            n ↦[wms][ (s + 140).toNat ]
                                                                                                destTail ∗
                                                                                              n ↦[wms][ (s + 32).toNat ]
                                                                                                  oldB ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 32).toNat + 8 ]
                                                                                                    WasmLogic.bytes32
                                                                                                      oldD ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 24).toNat ]
                                                                                                      derefOut ∗
                                                                                                    n ↦[wms][
                                                                                                        (s + 48).toNat ]
                                                                                                        oldVec ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              60).toNat ]
                                                                                                          contractTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 141 (List.drop 9 WNear.Binary.f297.body)) Φ
```

`WNear.Binary.SerdeObjectNoEsc.parser_family` (hash `0000000020e1fe86`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.parser_family {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (gt : Wasm.GlobalType) (bs rest : List UInt8) (a : WNear.AccountId)
  (N F : ℕ) (hnb : 92 ∉ bs) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hend : bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) = bs.length) :
  WNear.Binary.BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a F
    (WNear.Binary.SerdeObjectNoEsc.parserCost cfg F bs rest N) (max F 1 + 1)
    (WNear.Binary.SerdeObjectNoEsc.parserCode n inst mi A)
```

## Bridge.Functions.BalanceOf297ParserFixed

`WNear.Binary.BalanceOf297AbsentCall.okAtFixed` (hash `697ae1c8310062ab`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.okAtFixed {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n : ℕ)
  (out : UInt32) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (hl F : ℕ) : Iris.IProp GF :=
  fun F =>
    iprop(∃ p cap,
        ⌜p ≠ 0 ∧ (↑a).utf8ByteSize ≤ cap.toNat⌝ ∗
          n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
            n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
              n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 cap ∗
                n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ∗
                  n ↦[wms][ p.toNat ] (↑a).toUTF8.toList ∗
                    WNear.Binary.AllocInv.block n (p.toNat + (↑a).utf8ByteSize)
                        (cap.toNat - (↑a).utf8ByteSize) ∗
                      WNear.Binary.AllocInv.heapInv n 2048 hl ((p.toNat, cap.toNat) :: live) F)
```

`WNear.Binary.BalanceOf297AbsentCall.okAt_expose` (hash `000000007d267d9d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.okAt_expose {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (n : ℕ) (out : UInt32) (a : WNear.AccountId) (live : List (ℕ × ℕ)) :
  WNear.Binary.FromSliceSpec.okAt n out a live ⊢ ∃ hl F, WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl F
```

`WNear.Binary.BalanceOf297AbsentCall.parser_fixed_resources` (hash `00000000c926493a`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_fixed_resources {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (n : ℕ) (out : UInt32) (a : WNear.AccountId) (ip ic : UInt32)
  (live : List (ℕ × ℕ)) (hl F : ℕ) :
  WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a ((ip.toNat, ic.toNat) :: live) hl F ⊢
    ∃ p c rest,
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

## Bridge.Functions.BalanceOf297ParserFixedCompose

`WNear.Binary.BalanceOf297AbsentCall.parser_fixed_through_cleanup` (hash `0000000079fb1e4a`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_fixed_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic il idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState)
  (S : WNear.State) (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom : WNear.Binary.LookupMapOps.HeapRoomK 6 len 2048) (hacc : h.storageAccounting = some st)
  (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true) (hcanon : NearLogic.Canon st)
  (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                                  WNear.Binary.LookupMapGet.cost399None cfg (F + 1 + 1) 1
                                                    (UInt32.ofNat (↑a).utf8ByteSize) h
                                                    (WNear.accountsPrefix ++
                                                      (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++
                                                        (↑a).toUTF8.toList)) +
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
                                                  WNear.Binary.BalanceOf297AbsentCall.okAtFixed n (s + 88) a
                                                      ((ip.toNat, ic.toNat) :: live) len F ∗
                                                    n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                      n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                        n ↦[wms][ (s + 128).toNat + 8 ] WasmLogic.bytes32 oldC ∗
                                                          n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                            n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                              n ↦[wms][ (s + 32).toNat + 8 ] WasmLogic.bytes32 oldD ∗
                                                                n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ∗
                                                                  n ↦[wms][ (s + 48).toNat + 4 ] WasmLogic.bytes32 ic ∗
                                                                    n ↦[wms][ (s + 48).toNat + 8 ]
                                                                        WasmLogic.bytes32 il ∗
                                                                      n ↦[wms][ (s + 60).toNat ] contractTail ∗
                                                                        WNear.Binary.AllocInv.block n ip.toNat
                                                                            ic.toNat ∗
                                                                          n ↦[wms][ (s + 8).toNat ] ob ∗
                                                                            WNear.Binary.ToVec.tvData n ta ptr0 (A 759)
                                                                                (A 353) ∗
                                                                              n ↦[wms][ (s + 144).toNat ] out ∗
                                                                                n ↦[wms][ s.toNat ] head ∗
                                                                                  ▷
                                                                                    ∀ p c,
                                                                                      (NearLogic.credits Cg R ∗
                                                                                          g ↦[wg]
                                                                                              { type := gt,
                                                                                                value :=
                                                                                                  Wasm.Value.i32
                                                                                                    (s + 160) } ∗
                                                                                            (∃ hl,
                                                                                                WNear.Binary.AllocInv.heapInv
                                                                                                  n 2048 hl live
                                                                                                  (⋯ + 1 + 1)) ∗
                                                                                              ∃ h1,
                                                                                                ⌜NearLogic.StorageReadPost
                                                                                                      h WNear.stateKey 0
                                                                                                      st h1⌝ ∗
                                                                                                  ∃ st1 h2, ⋯) -∗
                                                                                        Φ.normal []
                                                                                          (WNear.Binary.BalanceOf297AbsentCall.frame
                                                                                            inst mi s
                                                                                            (UInt32.ofNat
                                                                                              (↑a).utf8ByteSize)
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

## Bridge.Functions.BalanceOf297ParserProvider

`WNear.Binary.BalanceOf297AbsentCall.ParserCallContract` (hash `f6f25a88e6ff2bc8`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.ParserCallContract {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta Cg : ℕ)
  (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId) (len : ℕ)
  (live : List (ℕ × ℕ)) (F parseGas outF : ℕ) (Cd Fr : Iris.IProp GF) : Prop :=
  fun Fr =>
    Cd ⊢
      NearLogic.MFunSpec cfg lim d WNear.Binary.types[31]! inst mi WNear.Binary.f65 Cg
        (fun args =>
          iprop(⌜args =
                  [Wasm.Value.i32 out, Wasm.Value.i32 ptr,
                    Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
              g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
                WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                  WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                    WNear.Binary.AllocInv.heapInv n 2048 len live F ∗
                      n ↦[wms][ out.toNat ] ob ∗
                        n ↦[wms][ ptr.toNat ] bs ∗
                          n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                            n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                              n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗ Fr))
        (fun x => parseGas) fun x rs =>
        iprop(⌜rs = []⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  n ↦[wms][ ptr.toNat ] bs ∗
                    n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                      n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                        n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                          Fr ∗
                            ∃ hl',
                              ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
                                WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live hl'
                                  outF)
```

`WNear.Binary.BalanceOf297AbsentCall.parser_provider_through_cleanup` (hash `000000001bad4f34`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_provider_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic idx : UInt32) (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (F : ℕ) (bs tail parserOut : List UInt8)
  (parseGas outF : ℕ) (Cd Fr : Iris.IProp GF) [Iris.BI.Persistent Cd]
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
  (hparserOut : parserOut.length = 16) (hob : ob.length = 16) (hstateTail : stateTail.length = 24)
  (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4) (hA : oldA.length = 8)
  (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF)
  (hParser :
    WNear.Binary.BalanceOf297AbsentCall.ParserCallContract cfg lim (d + 1) inst mi A n g ta Cg gt s (s + 88) ip idx
      parserOut bs a len ((ip.toNat, ic.toNat) :: live) F parseGas outF Cd Fr) :
  (Cd ∗
      A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
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
                                            (1000 * cfg.regularOpCost + parseGas +
                                              WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg outF h S a R) ∗
                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                            WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                              WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                                  n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                    NearLogic.mhostPt h ∗
                                                      WNear.Binary.AllocInv.heapInv n 2048 len
                                                          ((ip.toNat, ic.toNat) :: live) F ∗
                                                        n ↦[wms][ (s + 88).toNat ] parserOut ∗
                                                          n ↦[wms][ ip.toNat ] bs ∗
                                                            n ↦[wms][ ip.toNat + bs.length ] tail ∗
                                                              n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                                                n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                  n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                                                    Fr ∗
                                                                      n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                                        n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                                          n ↦[wms][ (s + 128).toNat + 8 ]
                                                                              WasmLogic.bytes32 oldC ∗
                                                                            n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                                              n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                                n ↦[wms][ (s + 32).toNat + 8 ]
                                                                                    WasmLogic.bytes32 oldD ∗
                                                                                  n ↦[wms][ (s + 48).toNat ]
                                                                                      WasmLogic.bytes32 ip ∗
                                                                                    n ↦[wms][ (s + 48).toNat + 4 ]
                                                                                        WasmLogic.bytes32 ic ∗
                                                                                      n ↦[wms][ (s + 48).toNat + 8 ]
                                                                                          WasmLogic.bytes32
                                                                                            (UInt32.ofNat bs.length) ∗
                                                                                        n ↦[wms][ (s + 60).toNat ]
                                                                                            contractTail ∗
                                                                                          n ↦[wms][ (s + 8).toNat ] ob ∗
                                                                                            WNear.Binary.ToVec.tvData n
                                                                                                ta ptr0 (A 759)
                                                                                                (A 353) ∗
                                                                                              n ↦[wms][
                                                                                                  (s + 144).toNat ]
                                                                                                  out ∗
                                                                                                n ↦[wms][ s.toNat ]
                                                                                                    head ∗
                                                                                                  ▷ ∀ p c, ⋯) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3)
      [Wasm.Value.i32 (s + 88), Wasm.Value.i32 ip, Wasm.Value.i32 (UInt32.ofNat bs.length)]
      (List.take 115 (List.drop 35 WNear.Binary.f297.body)) Φ
```

## Bridge.Functions.BalanceOf297ParserPublicCompose

`WNear.Binary.BalanceOf297AbsentCall.ParserPostBudget` (hash `dfa42ab5f7b55f4f`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.ParserPostBudget {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (n : ℕ) (out : UInt32) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (h : Wasm.NearState)
  (S : WNear.State) (R K : ℕ) : Iris.IProp GF :=
  fun K =>
    iprop(∀ len F,
        WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live len F -∗
          ⌜WNear.Binary.LookupMapOps.HeapRoomK 6 len 2048 ∧
                WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg F h S a R ≤ K⌝ ∗
            WNear.Binary.BalanceOf297AbsentCall.okAtFixed n out a live len F)
```

`WNear.Binary.BalanceOf297AbsentCall.parser_result_through_cleanup` (hash `00000000866d75e2`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.parser_result_through_cleanup {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 28 < lim.maxCallDepth) (Cg R K : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64)
  (x3 ip ic il idx : UInt32) (a : WNear.AccountId) (live : List (ℕ × ℕ))
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat)
  (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8) (h : Wasm.NearState)
  (S : WNear.State) (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
      A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
        A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
          A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
            WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
              A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                  A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                    A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                      A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                        A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                          A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                            WNear.Binary.DropVec.dropCode inst mi A ∗
                              A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                  inst ↪[inst] mi ∗
                                    NearLogic.credits Cg K ∗
                                      g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
                                        WNear.Binary.ReadRegister.ifaceR n ta A ∗
                                          WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                            WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                                              n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                                NearLogic.mhostPt h ∗
                                                  WNear.Binary.FromSliceSpec.okAt n (s + 88) a
                                                      ((ip.toNat, ic.toNat) :: live) ∗
                                                    WNear.Binary.BalanceOf297AbsentCall.ParserPostBudget cfg n (s + 88)
                                                        a ((ip.toNat, ic.toNat) :: live) h S R K ∗
                                                      n ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                        n ↦[wms][ (s + 128).toNat ] oldA ∗
                                                          n ↦[wms][ (s + 128).toNat + 8 ] WasmLogic.bytes32 oldC ∗
                                                            n ↦[wms][ (s + 140).toNat ] destTail ∗
                                                              n ↦[wms][ (s + 32).toNat ] oldB ∗
                                                                n ↦[wms][ (s + 32).toNat + 8 ] WasmLogic.bytes32 oldD ∗
                                                                  n ↦[wms][ (s + 48).toNat ] WasmLogic.bytes32 ip ∗
                                                                    n ↦[wms][ (s + 48).toNat + 4 ]
                                                                        WasmLogic.bytes32 ic ∗
                                                                      n ↦[wms][ (s + 48).toNat + 8 ]
                                                                          WasmLogic.bytes32 il ∗
                                                                        n ↦[wms][ (s + 60).toNat ] contractTail ∗
                                                                          WNear.Binary.AllocInv.block n ip.toNat
                                                                              ic.toNat ∗
                                                                            n ↦[wms][ (s + 8).toNat ] ob ∗
                                                                              WNear.Binary.ToVec.tvData n ta ptr0
                                                                                  (A 759) (A 353) ∗
                                                                                n ↦[wms][ (s + 144).toNat ] out ∗
                                                                                  n ↦[wms][ s.toNat ] head ∗
                                                                                    ▷
                                                                                      ∀ F p c,
                                                                                        (NearLogic.credits Cg R ∗
                                                                                            g ↦[wg]
                                                                                                { type := gt,
                                                                                                  value :=
                                                                                                    Wasm.Value.i32
                                                                                                      (s + 160) } ∗
                                                                                              (∃ hl,
                                                                                                  WNear.Binary.AllocInv.heapInv
                                                                                                    n 2048 hl live ⋯) ∗
                                                                                                ∃ h1,
                                                                                                  ⌜NearLogic.StorageReadPost
                                                                                                        h WNear.stateKey
                                                                                                        0 st h1⌝ ∗
                                                                                                    ⋯) -∗
                                                                                          Φ.normal []
                                                                                            (WNear.Binary.BalanceOf297AbsentCall.frame
                                                                                              inst mi s
                                                                                              (UInt32.ofNat
                                                                                                (↑a).utf8ByteSize)
                                                                                              (WNear.Binary.VecFromElem.pair64
                                                                                                p c)
                                                                                              (s + 40))) ⊢
    NearLogic.mwpi cfg lim d (WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3) []
      (List.take 114 (List.drop 36 WNear.Binary.f297.body)) Φ
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

## Bridge.Functions.BalanceOf297ParserRoom

`WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_memory` (hash `0000000058dad58c`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_memory {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest)) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
  (h0 h : Wasm.NearState) (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        WNear.Binary.InitialState.memLen
                                                                                        live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_memory` (hash `000000001a0e13b5`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_memory {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
  (h0 h : Wasm.NearState) (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        WNear.Binary.InitialState.memLen
                                                                                        live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_parser_pages_le` (hash `000000003f90d3b2`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_parser_pages_le (bs : List UInt8) (a : WNear.AccountId) (q : ℕ)
  (rest : List UInt8) (hmodel : NearInterface.Json.stringBody (List.drop q bs) [] = some (some ↑a, rest))
  (hlen : bs.length < 2 ^ 24) : WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs q a ≤ 6
```

`WNear.Binary.BalanceOf297AbsentCall.initial_memory_room` (hash `00000000a410e1dc`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_memory_room (bs : List UInt8) (hlen : bs.length < 2 ^ 24) :
  WNear.Binary.LookupMapOps.HeapRoomK
    ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat + 131)
    WNear.Binary.InitialState.memLen 2048
```

`WNear.Binary.BalanceOf297AbsentCall.initial_parser_and_body_room` (hash `00000000421498ac`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_parser_and_body_room (bs : List UInt8) (a : WNear.AccountId) (q len : ℕ)
  (rest : List UInt8) (hlen : bs.length < 2 ^ 24)
  (hmodel : NearInterface.Json.stringBody (List.drop q bs) [] = some (some ↑a, rest))
  (hr :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat + 131)
      len 2048) :
  WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs q a +
        6)
      len 2048 ∧
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop q bs)
```

`WNear.Binary.BalanceOf297AbsentCall.input_pages_le` (hash `00000000463a1238`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.input_pages_le (bs : List UInt8) (hlen : bs.length < 2 ^ 24) :
  (WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat ≤ 257
```

## Bridge.Functions.BalanceOf297Prologue

`WNear.Binary.BalanceOf297AbsentCall.prologue297` (hash `00000000fe4e65f4`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.prologue297 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType)
  (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32) (hs : 752 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 : UInt32)
  (rest : List Wasm.Instr) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      NearLogic.credits Cg (475 * cfg.regularOpCost + R) ∗
        g ↦[wg] { type := gt, value := Wasm.Value.i32 s } ∗
          WNear.Binary.VecFromElem.stk n (s.toNat - 240) 80 ∗
            WNear.Binary.SetupPanicHook.hookCells n 0 old 0 ∗
              n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                  ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                    WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells n 0 0 0 k3 ∗
                      WNear.Binary.FtTotalSupply.vtab n ta A ∗
                        n ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                          ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                            (NearLogic.credits Cg R -∗
                              g ↦[wg] { type := gt, value := Wasm.Value.i32 (s - 160) } -∗
                                WNear.Binary.VecFromElem.stk n (s.toNat - 240) 80 -∗
                                  WNear.Binary.EnvInput.ifaceI n ta A -∗
                                    NearLogic.mwpi cfg lim d
                                      {
                                        locals :=
                                          #[Wasm.Value.i32 (s - 160), Wasm.Value.i32 x1, Wasm.Value.i64 x2,
                                            Wasm.Value.i32 x3],
                                        inst := inst, mi := mi }
                                      [] rest Φ) ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] (WNear.Binary.BalanceOf297AbsentCall.body297Prologue ++ rest) Φ
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

## Bridge.Functions.EnvInput

`WNear.Binary.EnvInput.f527_spec` (hash `0000000081911030`)

```lean
theorem WNear.Binary.EnvInput.f527_spec {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (e : ℕ) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (s out : UInt32) (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hout : out.toNat + 12 ≤ 2 ^ 32) (idx : UInt32)
  (maxP len : ℕ) (live : List (ℕ × ℕ)) (ob : List UInt8) (hob : ob.length = 12) (h : Wasm.NearState)
  (hlim : Wasm.Near.withinLimit h.config.maxRegisterLen h.context.input.length = true)
  (hok : WNear.Binary.ReadRegister.RegOk maxP len (some h.context.input)) :
  WNear.Binary.EnvInput.inCode e inst mi A n maxP mx ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f527 Cg
      (WNear.Binary.EnvInput.pre527 n g ta A gt s out idx maxP len live ob h)
      (fun x => WNear.Binary.EnvInput.cost527 cfg h)
      (WNear.Binary.EnvInput.post527 n g ta A gt s out idx maxP len live h)
```

## Bridge.Functions.FromSliceEsc

`WNear.Binary.FromSliceEsc.f65_arr_copied` (hash `00000000fd9468c4`)

```lean
theorem WNear.Binary.FromSliceEsc.f65_arr_copied {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 38 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8)
  (value : String) (rest : List UInt8) (j k maxP mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hsp : 448 ≤ sp.toNat) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hroom : WNear.Binary.ParseStr.roomRun maxP mlen 0 [] (List.drop (j + 1) bs))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (mlen +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeFromTrait.code66 n maxP inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗
        WNear.Binary.ParseStr.code646 n maxP inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n maxP mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs value.toUTF8.toList rest j))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        ∃ p c len,
                          n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                            n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                              n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                                n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                                  WNear.Binary.SerdeScratchValueDrop.cleanValue n maxP mlen live F 0 bs
                                    value.toUTF8.toList (j + 1) p c len)
```

## Bridge.Functions.FromSliceModel

`WNear.Binary.FromSliceModel.f65_arr_model` (hash `000000002ba24b14`)

```lean
theorem WNear.Binary.FromSliceModel.f65_arr_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 38 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8)
  (value : String) (rest : List UInt8) (j k maxP mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hsp : 448 ≤ sp.toNat) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hr : WNear.Binary.SerdeErrBox.roomFor4 mlen maxP 20)
  (hroom : WNear.Binary.ParseStr.roomRun maxP mlen 0 [] (List.drop (j + 1) bs))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (mlen +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeFromTrait.code66 n maxP inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗
        WNear.Binary.ParseStr.code646 n maxP inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n maxP mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStruct78Model.costArray cfg F 0 bs value.toUTF8.toList rest j))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        ∃ p c len,
                          n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                            n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                              n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                                n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                                  WNear.Binary.SerdeScratchValueDrop.cleanValue n maxP mlen live F 0 bs
                                    value.toUTF8.toList (j + 1) p c len)
```

`WNear.Binary.FromSliceModel.f65_arr_model_bound` (hash `0000000078be717e`)

```lean
theorem WNear.Binary.FromSliceModel.f65_arr_model_bound {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 38 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8)
  (value : String) (rest : List UInt8) (j k maxP mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hsp : 448 ≤ sp.toNat) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hr : WNear.Binary.SerdeErrBox.roomFor4 mlen maxP 20)
  (hroom : WNear.Binary.ParseStr.roomRun maxP mlen 0 [] (List.drop (j + 1) bs))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (mlen +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeFromTrait.code66 n maxP inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗
        WNear.Binary.ParseStr.code646 n maxP inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n maxP mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStruct78Esc.costArray cfg F 0 bs value.toUTF8.toList rest j))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        ∃ p c len,
                          n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                            n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                              n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                                n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                                  WNear.Binary.SerdeScratchValueDrop.cleanValue n maxP mlen live F 0 bs
                                    value.toUTF8.toList (j + 1) p c len)
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

## Bridge.Functions.ReadRegister

`WNear.Binary.ReadRegister.RegOk` (hash `36916c5f3486419f`)

```lean
def WNear.Binary.ReadRegister.RegOk (maxP len : ℕ) : Option (List UInt8) → Prop :=
  fun x =>
    match x with
    | none => True
    | some data =>
      0 < data.length ∧
        data.length < 2 ^ 28 ∧
          WNear.Binary.VecFromElem.roomFor len maxP (UInt32.ofNat data.length)
```

## Bridge.Functions.ScratchGrow

`WNear.Binary.ScratchGrow.roomRes` (hash `379cc68a65804101`)

```lean
def WNear.Binary.ScratchGrow.roomRes (hl maxP : ℕ) (cap len k : UInt32) : Prop :=
  ¬WNear.Binary.ScratchGrow.fits cap len k →
    WNear.Binary.VecFromElem.roomFor hl maxP (WNear.Binary.VecGrow.growCap cap (len + k))
```

## Bridge.Functions.SerdeFromTraitModel

`WNear.Binary.SerdeFromTraitModel.f66_arr_model` (hash `000000004f15011a`)

```lean
theorem WNear.Binary.SerdeFromTraitModel.f66_arr_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 37 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8)
  (value : String) (rest : List UInt8) (j k maxP mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 432 ≤ sp.toNat) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hr : WNear.Binary.SerdeErrBox.roomFor4 mlen maxP 20)
  (hroom : WNear.Binary.ParseStr.roomRun maxP mlen 0 [] (List.drop (j + 1) bs))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (mlen +
        WNear.Binary.ScratchGrow.growthPages 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeFromTrait.code66 n maxP inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗
        WNear.Binary.ParseStr.code646 n maxP inst mi A ∗ WNear.Binary.DropVec.dropCode inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f66 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 rd]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 432) 432 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n maxP mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      WNear.Binary.ArgsLeaves.sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
                        n ↦[wms][ ptr.toNat ] bs ∗
                          n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                            n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                              n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable))
      (fun x =>
        (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
          WNear.Binary.SerdeStruct78Model.costArray cfg F 0 bs value.toUTF8.toList rest j)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 432) 432 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                WNear.Binary.ArgsLeaves.sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
                  n ↦[wms][ ptr.toNat ] bs ∗
                    n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                      n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                        n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                          ∃ p c len,
                            n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                              n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                                n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                                  n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                                    WNear.Binary.SerdeScratchValueDrop.cleanValue n maxP mlen live F 0 bs
                                      value.toUTF8.toList (j + 1) p c len)
```

## Bridge.Functions.SerdeIgnReuse

`WNear.Binary.SerdeIgnReuse.ignoreHyp` (hash `00000000a27b4c30`)

```lean
theorem WNear.Binary.SerdeIgnReuse.ignoreHyp {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ)
  (n g ta Cg maxP : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (gt : Wasm.GlobalType) (idx de ptr : UInt32)
  (bs : List UInt8) (live : List (ℕ × ℕ)) (B Bsaved : WNear.Binary.SerdeStructObjKeyState.Bounds)
  (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hnb : 92 ∉ bs)
  (hmono : ∀ (i j hl F : ℕ) (cap : UInt32), i ≤ j → B i hl F cap → B j hl F cap)
  (hmonoSaved : ∀ (i j hl F : ℕ) (cap : UInt32), i ≤ j → Bsaved i hl F cap → Bsaved j hl F cap) (Cd : Iris.IProp GF)
  [Iris.BI.Persistent Cd]
  (hcode :
    Cd ⊢
      WNear.Binary.SerdeEnds.endCode n maxP inst mi A ∗
        A 89 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[32]! inst WNear.Binary.f89 ∗
          A 81 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[32]! inst WNear.Binary.f81 ∗
            WNear.Binary.SerdeIgnValue.code81 inst mi A) :
  WNear.Binary.SerdeStructObjState.IgnoreHyp cfg lim inst mi n g Cg gt de ptr bs WNear.IgnoreShallow.ign1R
    (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
    (WNear.Binary.SerdeStructObjKeyState.member n maxP ta (A 578) idx de live B Bsaved) Cd
```

## Bridge.Functions.SerdeObjectNoEsc

`WNear.Binary.SerdeObjectNoEsc.before` (hash `6a9af4b41315b91d`)

```lean
def WNear.Binary.SerdeObjectNoEsc.before (L F0 : ℕ) : WNear.Binary.SerdeStructObjKeyState.Bounds :=
  fun x hl F cap => hl = L ∧ F ≤ F0 ∧ cap = 0
```

`WNear.Binary.SerdeObjectNoEsc.f228_obj_initial_room` (hash `000000002a83f5e0`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.f228_obj_initial_room {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 42 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32)
  (ob bs : List UInt8) (i : ℕ) (live : List (ℕ × ℕ)) (L F0 : ℕ) (hnb : 92 ∉ bs)
  (hL :
    L = WNear.Binary.InitialState.memLen ∨
      L = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
  (hi : i ≤ bs.length) (N : ℕ) (a : WNear.AccountId) (rF : List UInt8)
  (hb0 : bs[i + WNear.Binary.SerdeRead.wsLen (List.drop i bs)]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) bs) =
      some (some a, rF)) :
  WNear.Binary.SerdeStructObjModelState.code n 2048 inst mi A ∗ WNear.Binary.SerdeIgnValue.code81 inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f228 Cg
      (fun args =>
        iprop(⌜args =
                [Wasm.Value.i32 out, Wasm.Value.i32 de, Wasm.Value.i32 x2, Wasm.Value.i32 x3, Wasm.Value.i32 x4,
                  Wasm.Value.i32 x5]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
                n ↦[wms][ out.toNat ] ob ∗
                  WNear.Binary.SerdeRead.rd n de ptr bs i ∗
                    n ↦[wms][ de.toNat + 24 ] [128] ∗
                      WNear.Binary.SerdeStructObjKeyState.member n 2048 ta (A 578) idx de live
                        (WNear.Binary.SerdeObjectNoEsc.before L F0) (WNear.Binary.SerdeObjectNoEsc.saved L F0)
                        (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) none))
      (fun x =>
        WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
          (WNear.Binary.SerdeAcctHyp.K169 cfg bs F0) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
          (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N i)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
              n ↦[wms][ de.toNat + 24 ] [128] ∗
                ∃ p cap,
                  n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                    n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                      n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 cap ∗
                        n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ∗
                          ⌜p ≠ 0⌝ ∗
                            WNear.Binary.SerdeStructObjKeyState.member n 2048 ta (A 578) idx de live
                                (WNear.Binary.SerdeObjectNoEsc.before L F0) (WNear.Binary.SerdeObjectNoEsc.saved L F0)
                                (bs.length - rF.length) (some (a, p, cap)) ∗
                              WNear.Binary.SerdeRead.rd n de ptr bs (bs.length - rF.length))
```

`WNear.Binary.SerdeObjectNoEsc.f228_obj_noesc` (hash `00000000c655cd01`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.f228_obj_noesc {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 42 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32)
  (ob bs : List UInt8) (i maxP : ℕ) (live : List (ℕ × ℕ)) (L F0 : ℕ) (hnb : 92 ∉ bs)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK 132 L maxP) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
  (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
  (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length) (N : ℕ) (a : WNear.AccountId) (rF : List UInt8)
  (hb0 : bs[i + WNear.Binary.SerdeRead.wsLen (List.drop i bs)]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) bs) =
      some (some a, rF)) :
  WNear.Binary.SerdeStructObjModelState.code n maxP inst mi A ∗ WNear.Binary.SerdeIgnValue.code81 inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f228 Cg
      (fun args =>
        iprop(⌜args =
                [Wasm.Value.i32 out, Wasm.Value.i32 de, Wasm.Value.i32 x2, Wasm.Value.i32 x3, Wasm.Value.i32 x4,
                  Wasm.Value.i32 x5]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
                n ↦[wms][ out.toNat ] ob ∗
                  WNear.Binary.SerdeRead.rd n de ptr bs i ∗
                    n ↦[wms][ de.toNat + 24 ] [128] ∗
                      WNear.Binary.SerdeStructObjKeyState.member n maxP ta (A 578) idx de live
                        (WNear.Binary.SerdeObjectNoEsc.before L F0) (WNear.Binary.SerdeObjectNoEsc.saved L F0)
                        (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) none))
      (fun x =>
        WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
          (WNear.Binary.SerdeAcctHyp.K169 cfg bs F0) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
          (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N i)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
              n ↦[wms][ de.toNat + 24 ] [128] ∗
                ∃ p cap,
                  n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                    n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                      n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 cap ∗
                        n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ∗
                          ⌜p ≠ 0⌝ ∗
                            WNear.Binary.SerdeStructObjKeyState.member n maxP ta (A 578) idx de live
                                (WNear.Binary.SerdeObjectNoEsc.before L F0) (WNear.Binary.SerdeObjectNoEsc.saved L F0)
                                (bs.length - rF.length) (some (a, p, cap)) ∗
                              WNear.Binary.SerdeRead.rd n de ptr bs (bs.length - rF.length))
```

`WNear.Binary.SerdeObjectNoEsc.initial_room` (hash `00000000b146adc5`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.initial_room (bs : List UInt8) (L : ℕ) (hlen : bs.length < 2 ^ 24)
  (hL :
    L = WNear.Binary.InitialState.memLen ∨
      L = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length)) :
  WNear.Binary.LookupMapOps.HeapRoomK 132 L 2048
```

`WNear.Binary.SerdeObjectNoEsc.key_conditions` (hash `00000000e199b544`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.key_conditions (cfg : Wasm.Near.WasmConfig) (maxP : ℕ) (bs : List UInt8)
  (B : WNear.Binary.SerdeStructObjKeyState.Bounds) (hnb : 92 ∉ bs)
  (htransport : ∀ (i j hl F : ℕ) (cap : UInt32), B i hl F cap → B j hl F cap)
  (hroom :
    ∀ (i hl F : ℕ) (cap : UInt32),
      B i hl F cap → hl % 65536 = 0 → 0 < hl → WNear.Binary.SerdeErrBox.roomFor4 hl maxP 20) :
  WNear.Binary.SerdeStructObjKeyState.KeyConditions cfg maxP bs B (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
```

`WNear.Binary.SerdeObjectNoEsc.keys_before` (hash `00000000da6881a8`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.keys_before (cfg : Wasm.Near.WasmConfig) (L F0 maxP : ℕ) (bs : List UInt8) (hnb : 92 ∉ bs)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK 132 L maxP) :
  WNear.Binary.SerdeStructObjKeyState.KeyConditions cfg maxP bs (WNear.Binary.SerdeObjectNoEsc.before L F0)
    (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
```

`WNear.Binary.SerdeObjectNoEsc.keys_saved` (hash `000000005da2b8a5`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.keys_saved (cfg : Wasm.Near.WasmConfig) (L F0 maxP : ℕ) (bs : List UInt8) (hnb : 92 ∉ bs)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK 132 L maxP) :
  WNear.Binary.SerdeStructObjKeyState.KeyConditions cfg maxP bs (WNear.Binary.SerdeObjectNoEsc.saved L F0)
    (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
```

`WNear.Binary.SerdeObjectNoEsc.noesc_parts` (hash `000000004c799ae5`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.noesc_parts (bs : List UInt8) (q : ℕ) (s : String) (rest : List UInt8) (hnb : 92 ∉ bs)
  (hmodel : NearInterface.Json.stringBody (List.drop q bs) [] = some (some s, rest)) :
  WNear.Binary.ParseStr.borrowed (List.drop q bs) ∧
    WNear.Binary.ParseStrSuccess.appendChunks (List.drop q bs) [] = [] ∧
      s.toUTF8.toList = WNear.Binary.SerdeKeyNoEsc.keyBody bs q
```

`WNear.Binary.SerdeObjectNoEsc.saved` (hash `a430ea7e6367246f`)

```lean
def WNear.Binary.SerdeObjectNoEsc.saved (L F0 : ℕ) : WNear.Binary.SerdeStructObjKeyState.Bounds :=
  fun x hl F cap => L ≤ hl ∧ hl ≤ L + 65536 ∧ F ≤ max F0 1 ∧ cap = 0
```

`WNear.Binary.SerdeObjectNoEsc.saved_room` (hash `0000000054ca58e6`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.saved_room (L F0 maxP i hl F : ℕ) (cap : UInt32)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK 132 L maxP) (hb : WNear.Binary.SerdeObjectNoEsc.saved L F0 i hl F cap)
  (ha : hl % 65536 = 0) (hp : 0 < hl) : WNear.Binary.LookupMapOps.HeapRoomK 131 hl maxP
```

`WNear.Binary.SerdeObjectNoEsc.values` (hash `0000000024ca94ae`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.values (cfg : Wasm.Near.WasmConfig) (L F0 maxP : ℕ) (bs : List UInt8) (hnb : 92 ∉ bs)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK 132 L maxP) :
  WNear.Binary.SerdeStructObjValueState.ValueConditions cfg maxP bs (WNear.Binary.SerdeObjectNoEsc.before L F0)
    (WNear.Binary.SerdeObjectNoEsc.saved L F0) (WNear.Binary.SerdeAcctHyp.K169 cfg bs F0)
```

## Bridge.Functions.SerdeObjectParserGas

`WNear.Binary.SerdeObjectNoEsc.ignored_linear` (hash `000000005d811e8b`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.ignored_linear (cfg : Wasm.Near.WasmConfig) (bs : List UInt8) :
  WNear.Binary.SerdeCost.Lin81 cfg.regularOpCost (WNear.Binary.SerdeIgnReuse.cost81 cfg bs) WNear.IgnoreShallow.ign1R bs
    166 470
```

`WNear.Binary.SerdeObjectNoEsc.parser_cost_linear` (hash `000000009b5f3f07`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.parser_cost_linear (cfg : Wasm.Near.WasmConfig) (F : ℕ) (bs rest : List UInt8)
  (a : WNear.AccountId) (N : ℕ) (hnb : 92 ∉ bs) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest)) :
  WNear.Binary.SerdeObjectNoEsc.parserCost cfg F bs rest N ≤
    (2215 + 470 * bs.length) * cfg.regularOpCost + WNear.Binary.SerdeAcctHyp.x169 cfg F
```

## Bridge.Functions.SerdeObjectParserNoEsc

`WNear.Binary.SerdeObjectNoEsc.cleanObject` (hash `16d1a2294d4fad3d`)

```lean
def WNear.Binary.SerdeObjectNoEsc.cleanObject {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (n maxP L : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (bytes : List UInt8) (p cap len : UInt32) : Iris.IProp GF :=
  fun len =>
    iprop(⌜cap = UInt32.ofNat bytes.length ∧ len = UInt32.ofNat bytes.length ∧ p ≠ 0⌝ ∗
        n ↦[wms][ p.toNat ] bytes ∗
          ∃ hl,
            ⌜L ≤ hl ∧ hl ≤ L + 65536⌝ ∗
              WNear.Binary.AllocInv.heapInv n maxP hl ((p.toNat, cap.toNat) :: live)
                (max F 1 + 1))
```

`WNear.Binary.SerdeObjectNoEsc.f65_obj_model` (hash `000000004b823a74`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.f65_obj_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 45 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (N k mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hnb : 92 ∉ bs)
  (hL :
    mlen = WNear.Binary.InitialState.memLen ∨
      mlen = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hk : k = bs.length - rest.length) (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗
            WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
              A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f65 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 ptr, Wasm.Value.i32 (UInt32.ofNat bs.length)]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n 2048 mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      n ↦[wms][ ptr.toNat ] bs ∗
                        n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                          n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                            n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                              n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                                n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes))
      (fun x =>
        45 * cfg.regularOpCost +
          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
            WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
              (WNear.Binary.SerdeAcctHyp.K169 cfg bs F) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
              (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0))
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 448) 448 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ ptr.toNat ] bs ∗
                  n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                          n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes ∗
                            ∃ p c len,
                              n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                                n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                                  n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                                    n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                                      WNear.Binary.SerdeObjectNoEsc.cleanObject n 2048 mlen live F (↑a).toUTF8.toList p
                                        c len)
```

`WNear.Binary.SerdeObjectNoEsc.f66_obj_model` (hash `0000000003533fe7`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.f66_obj_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 44 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (N k mlen F : ℕ) (live : List (ℕ × ℕ)) (hob : ob.length = 16)
  (hout : out.toNat + 16 ≤ 2 ^ 32) (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 432 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hnb : 92 ∉ bs)
  (hL :
    mlen = WNear.Binary.InitialState.memLen ∨
      mlen = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hk : k = bs.length - rest.length) (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length) :
  WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
      WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
        WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
          WNear.Binary.DropVec.dropCode inst mi A ∗ WNear.Binary.SerdeIgnValue.code81 inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f66 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 rd]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 432) 432 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  WNear.Binary.AllocInv.heapInv n 2048 mlen live F ∗
                    n ↦[wms][ out.toNat ] ob ∗
                      WNear.Binary.ArgsLeaves.sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
                        n ↦[wms][ ptr.toNat ] bs ∗
                          n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                            n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                              n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                                  n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes))
      (fun x =>
        (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
          WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
            (WNear.Binary.SerdeAcctHyp.K169 cfg bs F) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
            (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 432) 432 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                WNear.Binary.ArgsLeaves.sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
                  n ↦[wms][ ptr.toNat ] bs ∗
                    n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                      n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                        n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                            n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes ∗
                              ∃ p c len,
                                n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                                  n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                                    n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                                      n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                                        WNear.Binary.SerdeObjectNoEsc.cleanObject n 2048 mlen live F (↑a).toUTF8.toList
                                          p c len)
```

`WNear.Binary.SerdeObjectNoEsc.f78_obj_initial_room` (hash `00000000c5cd353e`)

```lean
theorem WNear.Binary.SerdeObjectNoEsc.f78_obj_initial_room {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 43 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8)
  (live : List (ℕ × ℕ)) (L F0 : ℕ) (hnb : 92 ∉ bs)
  (hL :
    L = WNear.Binary.InitialState.memLen ∨
      L = WNear.Binary.VecFromElem.grownLen WNear.Binary.InitialState.memLen (UInt32.ofNat bs.length))
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
  (N : ℕ) (a : WNear.AccountId) (rF : List UInt8)
  (hb0 : bs[0 + WNear.Binary.SerdeRead.wsLen (List.drop 0 bs)]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (0 + WNear.Binary.SerdeRead.wsLen (List.drop 0 bs) + 1) bs) =
      some (some a, rF)) :
  WNear.Binary.SerdeStructObjModelState.code n 2048 inst mi A ∗
      WNear.Binary.SerdeIgnValue.code81 inst mi A ∗
        A 228 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[36]! inst WNear.Binary.f228 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f78 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 de]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
                n ↦[wms][ out.toNat ] ob ∗
                  WNear.Binary.SerdeRead.rd n de ptr bs 0 ∗
                    n ↦[wms][ de.toNat + 24 ] [128] ∗
                      WNear.Binary.SerdeStructObjKeyState.member n 2048 ta (A 578) idx de live
                        (WNear.Binary.SerdeObjectNoEsc.before L F0) (WNear.Binary.SerdeObjectNoEsc.saved L F0)
                        (0 + WNear.Binary.SerdeRead.wsLen (List.drop 0 bs) + 1) none))
      (fun x =>
        40 * cfg.regularOpCost +
          WNear.Binary.SerdeStructObj.costObj cfg (WNear.Binary.SerdeKeyNoEsc.K646 cfg bs)
            (WNear.Binary.SerdeAcctHyp.K169 cfg bs F0) (WNear.Binary.SerdeIgnReuse.cost81 cfg bs)
            (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
              n ↦[wms][ de.toNat + 24 ] [128] ∗
                ∃ p cap,
                  n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                    n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                      n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 cap ∗
                        n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ∗
                          ⌜p ≠ 0⌝ ∗
                            WNear.Binary.SerdeStructObjKeyState.member n 2048 ta (A 578) idx de live
                                (WNear.Binary.SerdeObjectNoEsc.before L F0) (WNear.Binary.SerdeObjectNoEsc.saved L F0)
                                (bs.length - rF.length) (some (a, p, cap)) ∗
                              WNear.Binary.SerdeRead.rd n de ptr bs (bs.length - rF.length))
```

## Bridge.Functions.SerdeOwnedValueDrop

`WNear.Binary.SerdeValueReuse.f68_owned_value` (hash `00000000120f3e9d`)

```lean
theorem WNear.Binary.SerdeValueReuse.f68_owned_value {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 7 < lim.maxCallDepth) (Cg maxP hl : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (de capS p c len : UInt32)
  (bs bytes : List UInt8) (q : ℕ) (hde : de.toNat + 24 ≤ 2 ^ 32) :
  WNear.Binary.DropVec.dropCode inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f68 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 (de + 12)]⌝ ∗
            WNear.Binary.SerdeValueReuse.ownedValue n maxP hl live F de capS bs bytes q p c len))
      (fun x => 315 * cfg.regularOpCost) fun x rs =>
      iprop(⌜rs = []⌝ ∗
          ∃ scratch cap sl,
            n ↦[wms][ de.toNat + 12 ] WasmLogic.bytes32 scratch ∗
              n ↦[wms][ de.toNat + 16 ] WasmLogic.bytes32 cap ∗
                n ↦[wms][ de.toNat + 20 ] WasmLogic.bytes32 sl ∗
                  WNear.Binary.SerdeScratchValueDrop.cleanValue n maxP hl live F capS bs bytes q p c len)
```

`WNear.Binary.SerdeValueReuse.f68_scratch_exact` (hash `00000000f1f8a07d`)

```lean
theorem WNear.Binary.SerdeValueReuse.f68_scratch_exact {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 7 < lim.maxCallDepth) (Cg maxP hl : ℕ) (live : List (ℕ × ℕ)) (F : ℕ) (v ptr cap sl : UInt32)
  (hv : v.toNat + 12 ≤ 2 ^ 32) :
  WNear.Binary.DropVec.dropCode inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f68 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 v]⌝ ∗
            n ↦[wms][ v.toNat ] WasmLogic.bytes32 ptr ∗
              n ↦[wms][ v.toNat + 4 ] WasmLogic.bytes32 cap ∗
                n ↦[wms][ v.toNat + 8 ] WasmLogic.bytes32 sl ∗
                  WNear.Binary.ScratchGrow.sbuf n maxP hl live F ptr cap []))
      (fun x => 315 * cfg.regularOpCost) fun x rs =>
      iprop(⌜rs = []⌝ ∗
          n ↦[wms][ v.toNat ] WasmLogic.bytes32 ptr ∗
            n ↦[wms][ v.toNat + 4 ] WasmLogic.bytes32 cap ∗
              n ↦[wms][ v.toNat + 8 ] WasmLogic.bytes32 sl ∗ WNear.Binary.AllocInv.heapInv n maxP hl live (F + 1))
```

## Bridge.Functions.SerdeStruct78Model

`WNear.Binary.SerdeStruct78Model.costArray` (hash `9ad5d577db2ccd50`)

```lean
def WNear.Binary.SerdeStruct78Model.costArray (cfg : Wasm.Near.WasmConfig) (F : ℕ) (capS : UInt32)
  (bs bytes rest : List UInt8) (j : ℕ) : ℕ :=
  (1300 +
        96 *
          (WNear.Binary.SerdeRead.wsLen bs +
              WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) +
            WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs))) *
      cfg.regularOpCost +
    WNear.Binary.SerdeValueReuse.valueCost cfg F capS bs bytes rest j j
```

`WNear.Binary.SerdeStruct78Model.costArray_le` (hash `0000000079c760ef`)

```lean
theorem WNear.Binary.SerdeStruct78Model.costArray_le (cfg : Wasm.Near.WasmConfig) (F : ℕ) (capS : UInt32) (bs : List UInt8)
  (value : String) (rest : List UInt8) (j : ℕ) (hq : bs[j]? = some 34)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest)) :
  WNear.Binary.SerdeStruct78Model.costArray cfg F capS bs value.toUTF8.toList rest j ≤
    WNear.Binary.SerdeStruct78Esc.costArray cfg F capS bs value.toUTF8.toList rest j
```

`WNear.Binary.SerdeStruct78Model.f78_arr_model` (hash `0000000068b517c1`)

```lean
theorem WNear.Binary.SerdeStruct78Model.f78_arr_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 36 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out de ptr idx sl ptrS capS : UInt32)
  (ob bs : List UInt8) (value : String) (rest : List UInt8) (j maxP hl : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 368 ≤ sp.toNat)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hcap : capS.toNat < 2 ^ 25)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hr : WNear.Binary.SerdeErrBox.roomFor4 hl maxP 20)
  (hroom : WNear.Binary.ParseStr.roomRun maxP hl capS [] (List.drop (j + 1) bs))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (hl +
        WNear.Binary.ScratchGrow.growthPages capS 0
            (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeEnds.endCode n maxP inst mi A ∗
      A 214 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f214 ∗
        A 169 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f169 ∗
          A 91 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[32]! inst WNear.Binary.f91 ∗
            WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗
              WNear.Binary.ParseStr.code646 n maxP inst mi A ∗
                A 228 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[36]! inst WNear.Binary.f228 ∗ inst ↪[inst] mi ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f78 Cg
      (fun args =>
        iprop(⌜args = [Wasm.Value.i32 out, Wasm.Value.i32 de]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  n ↦[wms][ out.toNat ] ob ∗
                    WNear.Binary.SerdeRead.rd n de ptr bs 0 ∗
                      n ↦[wms][ de.toNat + 24 ] [128] ∗
                        WNear.Binary.SerdeValueState.scratchPre n maxP hl live F de ptrS capS sl ∗
                          WNear.Binary.SerdeValueState.tables n))
      (fun x =>
        40 * cfg.regularOpCost + WNear.Binary.SerdeStruct78Model.costArray cfg F capS bs value.toUTF8.toList rest j)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ de.toNat + 24 ] [128] ∗
                  ∃ p c len,
                    ⌜p ≠ 0⌝ ∗
                      n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                        n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                          n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                            n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                              (WNear.Binary.SerdeValueState.tables n ∗
                                  WNear.Binary.SerdeValueReuse.ownedValue n maxP hl live F de capS bs
                                    value.toUTF8.toList (j + 1) p c len) ∗
                                WNear.Binary.SerdeRead.rd n de ptr bs
                                  (bs.length - rest.length +
                                      WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) +
                                    1))
```

## Bridge.Functions.SerdeStructArrModel

`WNear.Binary.SerdeStructArrModel.f228_arr_model` (hash `000000005f002536`)

```lean
theorem WNear.Binary.SerdeStructArrModel.f228_arr_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d : ℕ) (type : Wasm.FuncType) (htype : type.results = [])
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 35 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType) (sp out de ptr idx x2 x3 x4 x5 sl ptrS capS : UInt32)
  (ob bs : List UInt8) (value : String) (rest : List UInt8) (i j maxP hl : ℕ) (live : List (ℕ × ℕ)) (F : ℕ)
  (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
  (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 368 ≤ sp.toNat) (hi : i ≤ bs.length)
  (ho : bs[i + WNear.Binary.SerdeRead.wsLen (List.drop i bs)]? = some 91)
  (hj :
    j =
      i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hcap : capS.toNat < 2 ^ 25)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hr : WNear.Binary.SerdeErrBox.roomFor4 hl maxP 20)
  (hroom : WNear.Binary.ParseStr.roomRun maxP hl capS [] (List.drop (j + 1) bs))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (hl +
        WNear.Binary.ScratchGrow.growthPages capS 0
            (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeEnds.endCode n maxP inst mi A ∗
      A 214 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f214 ∗
        A 169 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f169 ∗
          A 91 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[32]! inst WNear.Binary.f91 ∗
            WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗ WNear.Binary.ParseStr.code646 n maxP inst mi A ⊢
    NearLogic.MFunSpec cfg lim d type inst mi WNear.Binary.f228 Cg
      (fun args =>
        iprop(⌜args =
                [Wasm.Value.i32 out, Wasm.Value.i32 de, Wasm.Value.i32 x2, Wasm.Value.i32 x3, Wasm.Value.i32 x4,
                  Wasm.Value.i32 x5]⌝ ∗
            g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
              WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
                WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                  n ↦[wms][ out.toNat ] ob ∗
                    WNear.Binary.SerdeRead.rd n de ptr bs i ∗
                      n ↦[wms][ de.toNat + 24 ] [128] ∗
                        WNear.Binary.SerdeValueState.scratchPre n maxP hl live F de ptrS capS sl ∗
                          WNear.Binary.SerdeValueState.tables n))
      (fun x =>
        (1300 +
              96 *
                (WNear.Binary.SerdeRead.wsLen (List.drop i bs) +
                    WNear.Binary.SerdeRead.wsLen
                      (List.drop (i + WNear.Binary.SerdeRead.wsLen (List.drop i bs) + 1) bs) +
                  WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs))) *
            cfg.regularOpCost +
          WNear.Binary.SerdeValueReuse.valueCost cfg F capS bs value.toUTF8.toList rest j j)
      fun x rs =>
      iprop(⌜rs = []⌝ ∗
          g ↦[wg] { type := gt, value := Wasm.Value.i32 sp } ∗
            WNear.Binary.VecFromElem.stk n (sp.toNat - 368) 368 ∗
              WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
                n ↦[wms][ de.toNat + 24 ] [128] ∗
                  ∃ p c len,
                    ⌜p ≠ 0⌝ ∗
                      n ↦[wms][ out.toNat ] WasmLogic.bytes32 0 ∗
                        n ↦[wms][ out.toNat + 4 ] WasmLogic.bytes32 p ∗
                          n ↦[wms][ out.toNat + 8 ] WasmLogic.bytes32 c ∗
                            n ↦[wms][ out.toNat + 12 ] WasmLogic.bytes32 len ∗
                              (WNear.Binary.SerdeValueState.tables n ∗
                                  WNear.Binary.SerdeValueReuse.ownedValue n maxP hl live F de capS bs
                                    value.toUTF8.toList (j + 1) p c len) ∗
                                WNear.Binary.SerdeRead.rd n de ptr bs
                                  (bs.length - rest.length +
                                      WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) +
                                    1))
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

## Bridge.Functions.SerdeValueReuse

`WNear.Binary.SerdeValueReuse.spec169_model` (hash `00000000e29224d0`)

```lean
theorem WNear.Binary.SerdeValueReuse.spec169_model {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ)
  (hm : WNear.Binary.Interface.IfaceMod mi A n g ta) (hd : d + 33 < lim.maxCallDepth) (Cg : ℕ) (gt : Wasm.GlobalType)
  (sp de ptr idx ptrS capS sl : UInt32) (ob bs : List UInt8) (value : String) (rest : List UInt8) (i j maxP hl F : ℕ)
  (live : List (ℕ × ℕ)) (hob : ob.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
  (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 304 ≤ sp.toNat) (hi : i ≤ bs.length)
  (hj : j = i + WNear.Binary.SerdeRead.wsLen (List.drop i bs)) (hq : bs[j]? = some 34) (hcap : capS.toNat < 2 ^ 25)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some value, rest))
  (hvalid : Wasm.Near.validAccountIdBytes value.toUTF8.toList = true)
  (hr : WNear.Binary.SerdeErrBox.roomFor4 hl maxP 20)
  (hroom : WNear.Binary.ParseStr.roomRun maxP hl capS [] (List.drop (j + 1) bs))
  (halloc :
    WNear.Binary.VecFromElem.roomFor
      (hl +
        WNear.Binary.ScratchGrow.growthPages capS 0
            (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []) *
          65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
  WNear.Binary.SerdeAccountId.code169 n maxP inst mi A ∗ WNear.Binary.ParseStr.code646 n maxP inst mi A ⊢
    WNear.Binary.SerdeSeqElem.Spec169 cfg lim d inst mi n g Cg gt sp de ptr ob bs i
      iprop(WNear.Binary.VecFromElem.stk n (sp.toNat - 304) 288 ∗
          WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
            WNear.Binary.SerdeValueState.scratchPre n maxP hl live F de ptrS capS sl ∗
              WNear.Binary.SerdeValueState.tables n)
      (WNear.Binary.SerdeValueReuse.valueCost cfg F capS bs value.toUTF8.toList rest i j) fun p c len =>
      iprop(WNear.Binary.VecFromElem.stk n (sp.toNat - 304) 288 ∗
          WNear.Binary.AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
            WNear.Binary.SerdeValueState.tables n ∗
              WNear.Binary.SerdeRead.rd n de ptr bs (bs.length - rest.length) ∗
                WNear.Binary.SerdeValueReuse.ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len)
```

`WNear.Binary.SerdeValueReuse.valueCost_le` (hash `00000000fafb1d35`)

```lean
theorem WNear.Binary.SerdeValueReuse.valueCost_le (cfg : Wasm.Near.WasmConfig) (F : ℕ) (cap : UInt32)
  (bs bytes rest : List UInt8) (i j : ℕ) (hq : j < bs.length)
  (hok : WNear.Binary.ParseStr.strRun (List.drop (j + 1) bs) [] = WNear.Binary.ParseStr.StrOut.ok bytes rest)
  (hu : WNear.Binary.Utf8.utf8Ok bytes = true) :
  WNear.Binary.SerdeValueReuse.valueCost cfg F cap bs bytes rest i j ≤
    (400 + WNear.Binary.AccountIdValid.cost554 bytes.length) * cfg.regularOpCost +
      WNear.Binary.SerdeDeStrEsc.costCopied cfg F cap bs bytes rest i j
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

## Bridge.Functions.StrRoom

`WNear.Binary.ParseStrRoom.roomRun_of_short_stringBody` (hash `0000000080282d01`)

```lean
theorem WNear.Binary.ParseStrRoom.roomRun_of_short_stringBody (maxP hl : ℕ) (l rest : List UInt8) (s : String)
  (hs : NearInterface.Json.stringBody l [] = some (some s, rest)) (hlen : s.toUTF8.toList.length ≤ 64)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK 131 hl maxP) : WNear.Binary.ParseStr.roomRun maxP hl 0 [] l
```

`WNear.Binary.ParseStrRoom.roomRun_short` (hash `000000000b0966f4`)

```lean
theorem WNear.Binary.ParseStrRoom.roomRun_short (maxP hl : ℕ) (cap : UInt32) (acc l bytes rest : List UInt8)
  (hc : cap.toNat ≤ 128) (hu : acc.length ≤ cap.toNat) (hb : bytes.length ≤ 64)
  (hok : WNear.Binary.ParseStr.strRun l acc = WNear.Binary.ParseStr.StrOut.ok bytes rest)
  (hr : WNear.Binary.LookupMapOps.HeapRoomK (2 * (bytes.length - acc.length) + 3) hl maxP) :
  WNear.Binary.ParseStr.roomRun maxP hl cap acc l
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

## Bridge.Methods.Code297

`WNear.Binary.BalanceOf297AbsentCall.code297` (hash `528cbfa333678ad7`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.code297 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (e inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ) (mx : Option ℕ) : Iris.IProp GF :=
  fun mx =>
    iprop(WNear.Binary.BalanceOf297AbsentCall.code297Input e inst mi A n mx ∗
        WNear.Binary.BalanceOf297AbsentCall.code297Parser inst mi A n ∗
          WNear.Binary.BalanceOf297AbsentCall.code297Lookup e inst mi A n mx ∗
            WNear.Binary.BalanceOf297AbsentCall.code297Return inst mi A n ∗
              WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi)
```

`WNear.Binary.BalanceOf297AbsentCall.code297Input` (hash `f2fe253fd633b030`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.code297Input {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (e inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ) (mx : Option ℕ) : Iris.IProp GF :=
  fun mx =>
    iprop(WNear.Binary.FtTotalSupply.codeA inst mi A ∗
        WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
          A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527)
```

`WNear.Binary.BalanceOf297AbsentCall.code297Lookup` (hash `b9797e27e9e63339`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.code297Lookup {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (e inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ) (mx : Option ℕ) : Iris.IProp GF :=
  fun mx =>
    iprop(WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
        A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
          A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
            A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
              WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293)
```

`WNear.Binary.BalanceOf297AbsentCall.code297Parser` (hash `a2a0d4502787e660`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.code297Parser {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ) : Iris.IProp GF :=
  fun n =>
    iprop(WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
        WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
          WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
            A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
              A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                  A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157)
```

`WNear.Binary.BalanceOf297AbsentCall.code297Return` (hash `9d27e08b220b4646`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.code297Return {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (inst : ℕ) (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n : ℕ) : Iris.IProp GF :=
  fun n =>
    iprop(WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
        A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
          A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
            A 779 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
              A 545 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                A 456 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                  WNear.Binary.DropVec.dropCode inst mi A ∗
                    A 68 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68)
```

`WNear.Binary.InitialState.code297_input_of` (hash `000000002e65d9b1`)

```lean
theorem WNear.Binary.InitialState.code297_input_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048 ⊢
    WNear.Binary.BalanceOf297AbsentCall.code297Input cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048)
```

`WNear.Binary.InitialState.code297_interface_of` (hash `00000000c5c433cc`)

```lean
theorem WNear.Binary.InitialState.code297_interface_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048 ⊢
    WNear.Binary.Interface.ifaceCode cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048)
```

`WNear.Binary.InitialState.code297_lookup_of` (hash `00000000fdb42a6a`)

```lean
theorem WNear.Binary.InitialState.code297_lookup_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048 ⊢
    WNear.Binary.BalanceOf297AbsentCall.code297Lookup cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048)
```

`WNear.Binary.InitialState.code297_of` (hash `000000004eff2c31`)

```lean
theorem WNear.Binary.InitialState.code297_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048 ⊢
    WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048)
```

`WNear.Binary.InitialState.code297_parser_of` (hash `00000000efc21124`)

```lean
theorem WNear.Binary.InitialState.code297_parser_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048 ⊢
    WNear.Binary.BalanceOf297AbsentCall.code297Parser 0 WNear.Binary.wInst id 0
```

`WNear.Binary.InitialState.code297_return_of` (hash `0000000047027382`)

```lean
theorem WNear.Binary.InitialState.code297_return_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048 ⊢
    WNear.Binary.BalanceOf297AbsentCall.code297Return 0 WNear.Binary.wInst id 0
```

`WNear.Binary.InitialState.startCode297` (hash `00000000f071d28b`)

```lean
theorem WNear.Binary.InitialState.startCode297 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  WasmLogic.ownCells (NearLogic.mheapOf { store := WNear.Binary.wStore cfg h }) ⊢
    |==>
      (WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
        0 ↪[inst] WNear.Binary.wInst ∗
          0 ↦[wmlength] WNear.Binary.InitialState.memLen ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗
                NearLogic.gasPt h.gas h.gasProfile h.actionProfile ∗
                  ([∗list] p ∈ WNear.Binary.InitialState.tabCells, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
                    WNear.Binary.InitialState.memR WNear.Binary.wDataMem 0 0 WNear.Binary.InitialState.memLen)
```

`WNear.Binary.InitialState.startCode297_gen` (hash `000000003fbb711e`)

```lean
theorem WNear.Binary.InitialState.startCode297_gen {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) (m : Wasm.Memory) (L : ℕ) :
  (WasmLogic.Loc.inst 0 ↦ₛ{Iris.DFrac.own 1} WasmLogic.Cell.inst WNear.Binary.wInst ∗
        WasmLogic.Loc.memLimit 0 ↦ₛ{Iris.DFrac.own 1} WasmLogic.Cell.memLimit (some 2048) ∗
          0 ↦[wmlength] WNear.Binary.InitialState.memLen ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗ NearLogic.gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ WNear.Binary.InitialState.tabCells, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
        ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
          WNear.Binary.InitialState.memR m 0 0 L ⊢
    |==>
      (WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
        0 ↪[inst] WNear.Binary.wInst ∗
          0 ↦[wmlength] WNear.Binary.InitialState.memLen ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗
                NearLogic.gasPt h.gas h.gasProfile h.actionProfile ∗
                  ([∗list] p ∈ WNear.Binary.InitialState.tabCells, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
                    WNear.Binary.InitialState.memR m 0 0 L)
```

## Bridge.Methods.ContextInputDomain

`WNear.Binary.InputDomain.InputLimitsOrdered` (hash `5706b9b03d9418f9`)

```lean
def WNear.Binary.InputDomain.InputLimitsOrdered (protocol : Wasm.Near.RuntimeConfig) : Prop :=
  protocol.wasm.limits.maxArgumentsLength ≤ protocol.wasm.limits.maxRegisterSize
```

`WNear.Binary.InputDomain.InputRegisterMismatchWitness` (hash `658bf35157d8158e`)

```lean
def WNear.Binary.InputDomain.InputRegisterMismatchWitness (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig) : Prop :=
  ∃ raw st ctx a,
    (WNear.wnear cfg).Represents raw st ∧
      ctx.WF raw ∧
        ctx.protocol = protocol ∧
          ctx.protocol.wasm.limits.maxRegisterSize < List.length ctx.args ∧
            (WNear.wnear cfg).Parses ctx.method ctx.args (WNear.Call.ftBalanceOf a) ∧
              (∃ output,
                  (WNear.wnear cfg).step ctx st (WNear.Call.ftBalanceOf a) = Except.ok output) ∧
                (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw
                      ctx).outcome =
                  Except.error (NearInterface.Failure.panic "input: register size exceeded")
```

`WNear.Binary.InputDomain.input_register_limit_trap` (hash `00000000eb594e0e`)

```lean
theorem WNear.Binary.InputDomain.input_register_limit_trap (st : Wasm.HostStore Wasm.NearState) (bound : ℕ)
  (hconfig : st.host.config.maxRegisterLen = some bound) (hlen : bound < st.host.context.input.length) :
  Wasm.Near.inputFn.invoke st [Wasm.Value.i64 0] = Wasm.HostResult.Trap st "input: register size exceeded"
```

`WNear.Binary.InputDomain.mismatch_refutes_refinement` (hash `000000006b7122b7`)

```lean
theorem WNear.Binary.InputDomain.mismatch_refutes_refinement (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (hwitness : WNear.Binary.InputDomain.InputRegisterMismatchWitness cfg size codeOf protocol) :
  ¬NearInterface.Refines Near.Boundary.nearRuntime protocol (WNear.Binary.wCode size codeOf) (WNear.wnear cfg)
```

`WNear.Binary.InputDomain.no_mismatch_witness` (hash `00000000454b62e7`)

```lean
theorem WNear.Binary.InputDomain.no_mismatch_witness (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hlimits : WNear.Binary.InputDomain.InputLimitsOrdered protocol) :
  ¬WNear.Binary.InputDomain.InputRegisterMismatchWitness cfg size codeOf protocol
```

`WNear.Binary.InputDomain.not_at_of_input_panic` (hash `00000000aaeacaf0`)

```lean
theorem WNear.Binary.InputDomain.not_at_of_input_panic (cfg : WNear.Config) (size : ℕ) (codeOf : List UInt8 → Near.ContractCode)
  (raw : WNear.RawStorage) (st : Option WNear.State) (ctx : NearInterface.Context) (a : WNear.AccountId)
  (hparse : (WNear.wnear cfg).Parses ctx.method ctx.args (WNear.Call.ftBalanceOf a))
  (hstep : ∃ output, (WNear.wnear cfg).step ctx st (WNear.Call.ftBalanceOf a) = Except.ok output)
  (hobs :
    (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome =
      Except.error (NearInterface.Failure.panic "input: register size exceeded")) :
  ¬WNear.Binary.Exported.At cfg size codeOf raw st ctx
```

`WNear.Binary.InputDomain.validated_actions_arguments` (hash `000000000340e965`)

```lean
theorem WNear.Binary.InputDomain.validated_actions_arguments (ctx : NearInterface.Context) (actions : List Near.Action)
  (method : String) (gas deposit : ℕ) (hvalid : Near.validateActions ctx.protocol.wasm.limits actions = Except.ok ())
  (hmem : Near.Action.functionCall method ctx.args gas deposit ∈ actions) :
  List.length ctx.args ≤ ctx.protocol.wasm.limits.maxArgumentsLength
```

`WNear.Binary.InputDomain.wf_arguments_bounded` (hash `00000000ce61ab3f`)

```lean
theorem WNear.Binary.InputDomain.wf_arguments_bounded (ctx : NearInterface.Context) (raw : WNear.RawStorage)
  (hwf : ctx.WF raw) : List.length ctx.args ≤ ctx.protocol.wasm.limits.maxArgumentsLength
```

`WNear.Binary.InputDomain.wf_input_fits_register` (hash `00000000f171e75e`)

```lean
theorem WNear.Binary.InputDomain.wf_input_fits_register (ctx : NearInterface.Context) (raw : WNear.RawStorage)
  (hwf : ctx.WF raw) (hlimits : WNear.Binary.InputDomain.InputLimitsOrdered ctx.protocol) :
  List.length ctx.args ≤ ctx.protocol.wasm.limits.maxRegisterSize
```

`WNear.Binary.InputDomain.wf_input_register_returns` (hash `000000006d5082c0`)

```lean
theorem WNear.Binary.InputDomain.wf_input_register_returns (ctx : NearInterface.Context) (raw : WNear.RawStorage)
  (hwf : ctx.WF raw) (hlimits : WNear.Binary.InputDomain.InputLimitsOrdered ctx.protocol)
  (st : Wasm.HostStore Wasm.NearState) (hinput : st.host.context.input = ctx.args)
  (hconfig : st.host.config.maxRegisterLen = some ctx.protocol.wasm.limits.maxRegisterSize) :
  ∃ st', Wasm.Near.inputFn.invoke st [Wasm.Value.i64 0] = Wasm.HostResult.Return [] st'
```

`WNear.Binary.InputDomain.wf_with_args` (hash `00000000c541198a`)

```lean
theorem WNear.Binary.InputDomain.wf_with_args (ctx : NearInterface.Context) (raw : WNear.RawStorage) (hwf : ctx.WF raw)
  (args : List UInt8) (hargs : args.length ≤ ctx.protocol.wasm.limits.maxArgumentsLength) :
  { method := ctx.method, args := args, current := ctx.current, predecessor := ctx.predecessor, signer := ctx.signer,
        signerPk := ctx.signerPk, attached := ctx.attached, prepaidGas := ctx.prepaidGas,
        promiseResults := ctx.promiseResults, outputDataReceivers := ctx.outputDataReceivers, balance := ctx.balance,
        locked := ctx.locked, storageUsage := ctx.storageUsage, blockHeight := ctx.blockHeight,
        timestamp := ctx.timestamp, epochHeight := ctx.epochHeight, randomSeed := ctx.randomSeed, trie := ctx.trie,
        protocol := ctx.protocol, actionHash := ctx.actionHash, existingYields := ctx.existingYields,
        chainId := ctx.chainId, validatorStake := ctx.validatorStake, validatorTotalStake := ctx.validatorTotalStake,
        storageProofSize := ctx.storageProofSize }.WF
    raw
```

## Bridge.Methods.FtBalanceOfAbsentCompose

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_model_agreement` (hash `00000000a8f8c5cc`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_model_agreement {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (modelCfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : NearInterface.RawStorage) (hwf : ctx.WF raw) (hraw : raw = WNear.encode S) (hS : S.WF)
  (hrep : NearLogic.eraseP h = NearLogic.eraseP (WNear.Binary.hostOf ctx raw))
  (hdef : ¬0 < WNear.Binary.FtTotalSupplyMethod.deficit ctx S) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.wnear modelCfg).step ctx (some S) (WNear.Call.ftBalanceOf a) =
      Except.ok { state := S, ret := WNear.Ret.u128 0, logs := [], promises := [] } ∧
    (WNear.Binary.FtTotalSupply.codeA inst mi A ∗
        WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
          A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
            WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
              WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
                WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                  A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                    A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                      A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                        A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                          WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                            A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                              A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                                A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                  WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                    A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                      WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                        A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                          A 158 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                            A 779 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                              A 545 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                                A 456 ↪[wf]
                                                    Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                  WNear.Binary.DropVec.dropCode inst mi A ∗
                                                    A 68 ↪[wf]
                                                        Wasm.FuncInst.wasm WNear.Binary.types[0]! inst
                                                          WNear.Binary.f68 ∗
                                                      WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                        inst ↪[inst] mi ∗
                                                          NearLogic.credits Cg
                                                              (475 * cfg.regularOpCost +
                                                                (3 * cfg.regularOpCost +
                                                                  (100 * cfg.regularOpCost +
                                                                      WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                    (100 * cfg.regularOpCost +
                                                                      (100 * cfg.regularOpCost +
                                                                        (1000 * cfg.regularOpCost +
                                                                            (45 * cfg.regularOpCost +
                                                                              ((700 +
                                                                                    96 *
                                                                                      WNear.Binary.SerdeRead.wsLen
                                                                                        (List.drop k bs)) *
                                                                                  cfg.regularOpCost +
                                                                                WNear.Binary.SerdeStruct78Esc.costArray
                                                                                  cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                  j)) +
                                                                          WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                            cfg
                                                                            (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                              bs (j + 1) 1)
                                                                            h S a R)))))) ∗
                                                            g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                              WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                                WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                  n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                    ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                      ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                        WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                            n 0 0 0 k3 ∗
                                                                          WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                            n ↦[wms][ 1050188 + 36 ]
                                                                                WNear.Binary.Interface.dataWord
                                                                                  (1050188 + 36) ∗
                                                                              ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                                WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                    idx ta (A 578) ∗
                                                                                  n ↦[wms][ 1049788 ]
                                                                                      WNear.Binary.StateRead.stateKey ∗
                                                                                    NearLogic.mhostPt h0 ∗
                                                                                      WNear.Binary.AllocInv.heapInv n
                                                                                          2048 len live 1 ∗
                                                                                        n ↦[wms][ (s + 88).toNat ]
                                                                                            oldOpt ∗
                                                                                          n ↦[wms][ (s + 100).toNat ]
                                                                                              optTail ∗
                                                                                            n ↦[wms][ 1062392 ]
                                                                                                WNear.Binary.ParseStr.escTable ∗
                                                                                              n ↦[wms][ 1071704 ]
                                                                                                  WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                                n ↦[wms][ 1062712 ]
                                                                                                    WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 104).toNat ]
                                                                                                      stateTail ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                            128).toNat ]
                                                                                                        oldA ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                                128).toNat +
                                                                                                            8 ]
                                                                                                          WasmLogic.bytes32
                                                                                                            oldC ∗
                                                                                                        ⋯ ⊢
      NearLogic.mwpi cfg lim d
        { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst,
          mi := mi }
        [] WNear.Binary.f297.body Φ)
```

`WNear.Binary.FtBalanceOfMethod.absent_step_zero` (hash `0000000053756772`)

```lean
theorem WNear.Binary.FtBalanceOfMethod.absent_step_zero (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : WNear.RawStorage) (s : WNear.State) (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (hs : s.WF)
  (h : Wasm.NearState) (he : NearLogic.eraseP h = NearLogic.eraseP (WNear.Binary.hostOf ctx raw)) (a : WNear.AccountId)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hdef : ¬0 < WNear.Binary.FtTotalSupplyMethod.deficit ctx s) :
  (WNear.wnear cfg).step ctx (some s) (WNear.Call.ftBalanceOf a) =
    Except.ok { state := s, ret := WNear.Ret.u128 0, logs := [], promises := [] }
```

## Bridge.Methods.FtBalanceOfArrayCase

`WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase` (hash `706ae070fa81f067`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase (st : Option WNear.State) (ctx : NearInterface.Context)
  (c : WNear.Call) : Prop :=
  ∃ S a bs rest j k,
    st = some S ∧
      c = WNear.Call.ftBalanceOf a ∧
        a ∉ S.registered ∧
          ctx.args = bs ∧
            bs.length < 2 ^ 24 ∧
              bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91 ∧
                j =
                    WNear.Binary.SerdeRead.wsLen bs + 1 +
                      WNear.Binary.SerdeRead.wsLen
                        (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) ∧
                  bs[j]? = some 34 ∧
                    bs[bs.length - rest.length +
                            WNear.Binary.SerdeRead.wsLen
                              (List.drop (bs.length - rest.length) bs)]? =
                        some 93 ∧
                      k =
                          bs.length - rest.length +
                              WNear.Binary.SerdeRead.wsLen
                                (List.drop (bs.length - rest.length) bs) +
                            1 ∧
                        k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length ∧
                          NearInterface.Json.stringBody (List.drop (j + 1) bs) [] =
                            some (some ↑a, rest)
```

`WNear.Binary.BalanceOf297AbsentCall.array_case_accepted` (hash `0000000034f51345`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_case_accepted (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (c : WNear.Call) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hcase : WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.array_case_no_issue` (hash `000000007cdce21f`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_case_no_issue (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (c : WNear.Call) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hcase : WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c) (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_case_is_array_case` (hash `00000000d4ba5150`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_case_is_array_case (st : Option WNear.State) (ctx : NearInterface.Context)
  (c : WNear.Call) (h : WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) :
  WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c
```

## Bridge.Methods.FtBalanceOfBodyGas

`WNear.Binary.BalanceOf297AbsentCall.alloc32_delta` (hash `0000000023d6edcb`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.alloc32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (size : UInt32) (hF : F ≤ 32) :
  WNear.Binary.VecWithCap.costAllocF cfg F size ≤
    WNear.Binary.VecFromElem.costAlloc cfg false size + 10270 * cfg.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.allocW32_delta` (hash `00000000a07223ca`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.allocW32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (size : UInt32) (hF : F ≤ 32) :
  WNear.Binary.AllocZeroedF.costAllocW cfg F size ≤
    WNear.Binary.VecFromElem.costAlloc cfg false size + 10270 * cfg.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.borsh_contract32_delta` (hash `00000000eb492bb4`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.borsh_contract32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (L : UInt32)
  (hF : F ≤ 32) :
  WNear.Binary.BorshContractF.cost161 cfg F L ≤ WNear.Binary.BorshContract.cost161 cfg L + 10270 * cfg.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.initialBodyCost` (hash `cf515d7165748b59`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.initialBodyCost (cfg : Wasm.Near.WasmConfig) (h0 h : Wasm.NearState)
  (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) : ℕ :=
  475 * cfg.regularOpCost +
    (3 * cfg.regularOpCost +
      (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
        (100 * cfg.regularOpCost +
          (100 * cfg.regularOpCost +
            (1000 * cfg.regularOpCost +
                (45 * cfg.regularOpCost +
                  ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) *
                      cfg.regularOpCost +
                    WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0 bs (↑a).toUTF8.toList rest
                      j)) +
              WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a 0)))))
```

`WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse` (hash `b7a21c48394075af`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse (h0 h : Wasm.NearState) (a : WNear.AccountId) (bs : List UInt8) :
  ℕ :=
  NearLogic.inputUse h0 + NearLogic.registerLenUse (NearLogic.inputHost h0 0) +
              NearLogic.readRegisterUse (NearLogic.inputHost h0 0) bs.length +
            NearLogic.storageReadUse h WNear.Binary.StateRead.stateKey 5 +
          NearLogic.registerLenUse h +
        NearLogic.readRegisterUse h 29 +
      NearLogic.storageReadUse h
        (WNear.accountsPrefix ++
          (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))
        (5 + (↑a).utf8ByteSize) +
    NearLogic.valueReturnUse h 3
```

`WNear.Binary.BalanceOf297AbsentCall.initial_body_cost_le` (hash `000000003528bb87`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_body_cost_le (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (h0 h : Wasm.NearState) (S : WNear.State) (a : WNear.AccountId)
  (bs rest : List UInt8) (j k : ℕ) (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  WNear.Binary.BalanceOf297AbsentCall.initialBodyCost p.wasm h0 h S a bs rest j k ≤
    400 * 10 ^ 9 + 100 * 10 ^ 6 * bs.length + WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse h0 h a bs
```

`WNear.Binary.BalanceOf297AbsentCall.initial_body_trie_le` (hash `000000007f1c1d67`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_body_trie_le (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
  (a : WNear.AccountId) :
  NearLogic.readNodes (NearLogic.erase (WNear.Binary.hostOf ctx raw))
          (Near.TrieOverlay.contractKey (NearLogic.erase (WNear.Binary.hostOf ctx raw)).context.currentAccountId
            WNear.Binary.StateRead.stateKey) *
        NearLogic.trieNodeMax (NearLogic.erase (WNear.Binary.hostOf ctx raw)) +
      NearLogic.readNodes (NearLogic.erase (WNear.Binary.hostOf ctx raw))
          (Near.TrieOverlay.contractKey (NearLogic.erase (WNear.Binary.hostOf ctx raw)).context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) *
        NearLogic.trieNodeMax (NearLogic.erase (WNear.Binary.hostOf ctx raw)) ≤
    WNear.trieGas ctx
```

`WNear.Binary.BalanceOf297AbsentCall.initial_host_cost_le` (hash `000000007b2beee4`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_host_cost_le (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (h : Wasm.NearState) (S : WNear.State) (a : WNear.AccountId)
  (bs : List UInt8) (hext : h.extCosts = p.wasm.extCosts) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none) :
  WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse h (NearLogic.inputHost h 0) a bs ≤
    200 * 10 ^ 9 + 10 * 10 ^ 6 * bs.length +
          NearLogic.readNodes h
              (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.Binary.StateRead.stateKey) *
            NearLogic.trieNodeMax h +
        NearLogic.readNodes h
            (Near.TrieOverlay.contractKey h.context.currentAccountId
              (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) *
          NearLogic.trieNodeMax h +
      NearLogic.valueReturnDataGas h 3
```

`WNear.Binary.BalanceOf297AbsentCall.initial_host_input_eq` (hash `00000000326ad77e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_host_input_eq (h : Wasm.NearState) (a : WNear.AccountId) (bs : List UInt8) :
  WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse h (NearLogic.inputHost h 0) a bs =
    NearLogic.inputUse h + NearLogic.registerLenUse h + NearLogic.readRegisterUse h bs.length +
              NearLogic.storageReadUse h WNear.Binary.StateRead.stateKey 5 +
            NearLogic.registerLenUse h +
          NearLogic.readRegisterUse h 29 +
        NearLogic.storageReadUse h
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))
          (5 + (↑a).utf8ByteSize) +
      NearLogic.valueReturnUse h 3
```

`WNear.Binary.BalanceOf297AbsentCall.input_cost_le` (hash `00000000f7b36ea7`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.input_cost_le (cfg : Wasm.Near.WasmConfig) (h : Wasm.NearState) (bs : List UInt8)
  (hinput : h.context.input = bs) (hlen : bs.length < 2 ^ 24) :
  WNear.Binary.EnvInput.cost527 cfg h ≤
    (2100 + 13 * bs.length) * cfg.regularOpCost + cfg.linearOpBaseCost + 257 * cfg.linearOpUnitCost +
          NearLogic.inputUse h +
        NearLogic.registerLenUse (NearLogic.inputHost h 0) +
      NearLogic.readRegisterUse (NearLogic.inputHost h 0) bs.length
```

`WNear.Binary.BalanceOf297AbsentCall.lookup_none32_cost_le` (hash `000000003fa84e32`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.lookup_none32_cost_le (cfg : Wasm.Near.WasmConfig) (F : ℕ) (L : UInt32)
  (h : Wasm.NearState) (key : List UInt8) (hF : F ≤ 32) (hL : L.toNat ≤ 64) :
  WNear.Binary.LookupMapGet.cost399None cfg F 1 L h key ≤
    30000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      NearLogic.storageReadUse h key (5 + L.toNat)
```

`WNear.Binary.BalanceOf297AbsentCall.read_register32_delta` (hash `0000000009c1230d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.read_register32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (r : UInt64) (hF : F ≤ 32) :
  WNear.Binary.ReadRegisterF.cost523F cfg F h r ≤ WNear.Binary.ReadRegister.cost523 cfg h r + 10270 * cfg.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.return32_cost_le` (hash `0000000029b1e38f`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.return32_cost_le (cfg : Wasm.Near.WasmConfig) (F : ℕ) (lo hi : UInt64)
  (hF : F ≤ 32) :
  WNear.Binary.ToVec.cost96F cfg F lo hi ≤ 31000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost)
```

`WNear.Binary.BalanceOf297AbsentCall.state_read32_cost_le` (hash `00000000bf43eae9`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_read32_cost_le (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (S : WNear.State) (hF : F ≤ 32) :
  WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S ≤
    31000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
          NearLogic.storageReadUse h WNear.Binary.StateRead.stateKey 5 +
        NearLogic.registerLenUse h +
      NearLogic.readRegisterUse h 29
```

`WNear.Binary.BalanceOf297AbsentCall.state_read32_delta` (hash `00000000db6cc41c`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.state_read32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (S : WNear.State) (hF : F ≤ 32) :
  WNear.Binary.BalanceOf297AbsentCall.cost219F cfg F h S ≤
    WNear.Binary.FtTotalSupply.cost219 cfg h S + 20540 * cfg.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.storage_register32_delta` (hash `00000000591ccb07`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.storage_register32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (v : List UInt8) (hF : F ≤ 32) :
  WNear.Binary.StorageReadWrapF.costSF cfg F h v ≤
    WNear.Binary.StorageReadWrap.costS cfg h (some v) + 10270 * cfg.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.suffix_cost_le` (hash `000000001929df53`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.suffix_cost_le (cfg : Wasm.Near.WasmConfig) (F : ℕ) (h : Wasm.NearState)
  (S : WNear.State) (a : WNear.AccountId) (hF : F ≤ 12) :
  WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg F h S a 0 ≤
    97000 * cfg.regularOpCost + 6 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
              NearLogic.storageReadUse h WNear.Binary.StateRead.stateKey 5 +
            NearLogic.registerLenUse h +
          NearLogic.readRegisterUse h 29 +
        NearLogic.storageReadUse h
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))
          (5 + (↑a).utf8ByteSize) +
      NearLogic.valueReturnUse h 3
```

`WNear.Binary.BalanceOf297AbsentCall.two_read_nodes_le` (hash `0000000051f903c1`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.two_read_nodes_le (h : Wasm.NearState) (key : List UInt8) (hk : key.length ≤ 69) :
  NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.Binary.StateRead.stateKey) *
        NearLogic.trieNodeMax h +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId key) * NearLogic.trieNodeMax h ≤
    3 * (2 * (2 + h.context.currentAccountId.length + 69) + 1) * h.extCosts.cost "touching_trie_node" +
      8 * (2 * (2 + h.context.currentAccountId.length + 69) + 1) * h.extCosts.cost "read_cached_trie_node"
```

`WNear.Binary.BalanceOf297AbsentCall.vec_zero32_delta` (hash `0000000065066d38`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.vec_zero32_delta (cfg : Wasm.Near.WasmConfig) (F : ℕ) (size : UInt32)
  (hF : F ≤ 32) :
  WNear.Binary.VecFromElemF.cost687Z cfg F size ≤
    WNear.Binary.VecFromElem.cost687 cfg 0 size + 10270 * cfg.regularOpCost
```

## Bridge.Methods.FtBalanceOfCodeCompose

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_store_code` (hash `0000000018795b9b`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_store_code {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (runtime : Wasm.Near.RuntimeConfig) (cfg : Wasm.Near.WasmConfig)
  (lim : Wasm.ExecLimits) (d : ℕ) (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32)
  (x2 : UInt64) (x3 idx : UInt32) (a : WNear.AccountId) (live : List (ℕ × ℕ))
  (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (j k : ℕ)
  (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (hob : ob.length = 16)
  (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28) (hdestTail : destTail.length = 4)
  (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
  (h0 h : Wasm.NearState) (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  ((([∗list] p ∈ WNear.Binary.InitialState.funcCells runtime h0, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
        0 ↪[inst] WNear.Binary.wInst ∗ 0 ↪[wmlimit] some 2048) ∗
      NearLogic.credits Cg
          (475 * cfg.regularOpCost +
            (3 * cfg.regularOpCost +
              (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
                (100 * cfg.regularOpCost +
                  (100 * cfg.regularOpCost +
                    (1000 * cfg.regularOpCost +
                        (45 * cfg.regularOpCost +
                          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
                            WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                        (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
        0 ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
          WNear.Binary.VecFromElem.stk 0 (s.toNat - 592) 592 ∗
            WNear.Binary.SetupPanicHook.hookCells 0 0 hookOld 0 ∗
              0 ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                0 ↦[wt][ 116 ] Wasm.Ref.func (id 565) ∗
                  0 ↦[wt][ 106 ] Wasm.Ref.func (id 564) ∗
                    WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells 0 0 0 0 k3 ∗
                      WNear.Binary.FtTotalSupply.vtab 0 0 id ∗
                        0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                          0 ↦[wt][ 44 ] Wasm.Ref.func (id 246) ∗
                            WNear.Binary.AllocFirstFit.vt 0 1057464 idx 0 (id 578) ∗
                              0 ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
                                NearLogic.mhostPt h0 ∗
                                  WNear.Binary.AllocInv.heapInv 0 2048 WNear.Binary.InitialState.memLen live 1 ∗
                                    0 ↦[wms][ (s + 88).toNat ] oldOpt ∗
                                      0 ↦[wms][ (s + 100).toNat ] optTail ∗
                                        0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                          0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                            0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                              0 ↦[wms][ (s + 104).toNat ] stateTail ∗
                                                0 ↦[wms][ (s + 128).toNat ] oldA ∗
                                                  0 ↦[wms][ (s + 128).toNat + 8 ] WasmLogic.bytes32 oldC ∗
                                                    0 ↦[wms][ (s + 140).toNat ] destTail ∗
                                                      0 ↦[wms][ (s + 32).toNat ] oldB ∗
                                                        0 ↦[wms][ (s + 32).toNat + 8 ] WasmLogic.bytes32 oldD ∗
                                                          0 ↦[wms][ (s + 24).toNat ] derefOut ∗
                                                            0 ↦[wms][ (s + 48).toNat ] oldVec ∗
                                                              0 ↦[wms][ (s + 60).toNat ] contractTail ∗
                                                                0 ↦[wms][ (s + 8).toNat ] ob ∗
                                                                  WNear.Binary.ToVec.tvData 0 0 ptr0 (id 759) (id 353) ∗
                                                                    0 ↦[wms][ (s + 144).toNat ] out ∗
                                                                      0 ↦[wms][ s.toNat ] head ∗
                                                                        ▷
                                                                          ∀ p c,
                                                                            (NearLogic.credits Cg R ∗
                                                                                (∃ ip,
                                                                                    0 ↦[wms][ (s + 24).toNat ]
                                                                                      WasmLogic.bytes32 ip) ∗
                                                                                  0 ↦[wms][ (s + 24).toNat + 4 ]
                                                                                      WasmLogic.bytes32
                                                                                        (UInt32.ofNat bs.length) ∗
                                                                                    0 ↦[wms][ 1062392 ]
                                                                                        WNear.Binary.ParseStr.escTable ∗
                                                                                      0 ↦[wms][ 1071704 ]
                                                                                          WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                        0 ↦[wms][ 1062712 ]
                                                                                            WNear.Binary.SerdeEsc.hexTable ∗
                                                                                          0 ↦[wg]
                                                                                              { type := gt,
                                                                                                value :=
                                                                                                  Wasm.Value.i32
                                                                                                    (s + 160) } ∗
                                                                                            (∃ hl,
                                                                                                WNear.Binary.AllocInv.heapInv
                                                                                                  0 2048 hl live
                                                                                                  (⋯ + 1 + 1)) ∗
                                                                                              ∃ h1,
                                                                                                ⌜NearLogic.StorageReadPost
                                                                                                      h WNear.stateKey 0
                                                                                                      st h1⌝ ∗
                                                                                                  ∃ st1 h2, ⋯) -∗
                                                                              Φ.normal []
                                                                                (WNear.Binary.BalanceOf297AbsentCall.frame
                                                                                  0 WNear.Binary.wInst s
                                                                                  (UInt32.ofNat (↑a).utf8ByteSize)
                                                                                  (WNear.Binary.VecFromElem.pair64 p c)
                                                                                  (s + 40))) ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := 0,
        mi := WNear.Binary.wInst }
      [] WNear.Binary.f297.body Φ
```

## Bridge.Methods.FtBalanceOfCopiedCase

`WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase` (hash `ec58e231dd4680de`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase (st : Option WNear.State) (ctx : NearInterface.Context)
  (c : WNear.Call) : Prop :=
  ∃ S a bs rest j k,
    st = some S ∧
      c = WNear.Call.ftBalanceOf a ∧
        a ∉ S.registered ∧
          ctx.args = bs ∧
            bs.length < 2 ^ 24 ∧
              bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91 ∧
                j =
                    WNear.Binary.SerdeRead.wsLen bs + 1 +
                      WNear.Binary.SerdeRead.wsLen
                        (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) ∧
                  bs[j]? = some 34 ∧
                    bs[bs.length - rest.length +
                            WNear.Binary.SerdeRead.wsLen
                              (List.drop (bs.length - rest.length) bs)]? =
                        some 93 ∧
                      k =
                          bs.length - rest.length +
                              WNear.Binary.SerdeRead.wsLen
                                (List.drop (bs.length - rest.length) bs) +
                            1 ∧
                        k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length ∧
                          NearInterface.Json.stringBody (List.drop (j + 1) bs) [] =
                              some (some ↑a, rest) ∧
                            ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_case_accepted` (hash `00000000c35e0873`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_case_accepted (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (c : WNear.Call) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hcase : WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_case_no_issue` (hash `000000002f6d36ca`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_case_no_issue (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (c : WNear.Call) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hcase : WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
```

## Bridge.Methods.FtBalanceOfCopiedModel

`WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_v86` (hash `00000000f688e7e8`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_v86 (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (modelSt : Option WNear.State)
  (ctx : NearInterface.Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ)
  (tr : Near.TrieOverlay.State) (bud : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hentry : WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
  (hrep : (WNear.wnear cfg).Represents raw modelSt) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_agreement_of_represents` (hash `00000000805b76bd`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_agreement_of_represents (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : WNear.RawStorage) (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId)
  (tr : Near.TrieOverlay.State) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hval : (WNear.Binary.hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
  (hnone : (WNear.Binary.hostOf ctx raw).storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a) = none)
  (h0 : Wasm.NearState) (hh0 : NearLogic.eraseP h0 = NearLogic.eraseP (WNear.Binary.hostOf ctx raw))
  (e : Wasm.NearState) :
  WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a tr h0 e →
    WNear.Binary.AgreesWith (WNear.wnear cfg) ctx raw e ((WNear.wnear cfg).step ctx st (WNear.Call.ftBalanceOf a))
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_v86` (hash `000000003c42f475`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_v86 (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (modelSt : Option WNear.State)
  (ctx : NearInterface.Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ)
  (tr : Near.TrieOverlay.State) (bud : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hentry : WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
  (hrep : (WNear.wnear cfg).Represents raw modelSt) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

## Bridge.Methods.FtBalanceOfCopiedPre

`WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_init` (hash `00000000334c8e9d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_init (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (ctx : NearInterface.Context) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hl : WNear.Binary.FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) (hargs : ctx.args = bs)
  (hrep : (WNear.wnear cfg).Represents raw (some S)) (ha : a ∉ S.registered) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx (some S) (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_init` (hash `0000000071282a14`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_init (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (ctx : NearInterface.Context) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hl : WNear.Binary.FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (hargs : ctx.args = bs)
  (hrep : (WNear.wnear cfg).Represents raw (some S)) (ha : a ∉ S.registered) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx (some S) (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_entry_at_of_ctx` (hash `00000000ce3835ec`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_entry_at_of_ctx (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : WNear.RawStorage) (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
  (hwf : ctx.WF raw) (hl : WNear.Binary.FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hargs : ctx.args = bs)
  (hlen : bs.length < 2 ^ 24) (hval : (WNear.Binary.hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
  (hnone : (WNear.Binary.hostOf ctx raw).storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a) = none) :
  WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs ctx.trie (WNear.proofBound ctx)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_entry_pre_of` (hash `00000000a12823e7`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_entry_pre_of (ctx : NearInterface.Context) (raw : WNear.RawStorage)
  (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8) (hwf : ctx.WF raw)
  (hl : WNear.Binary.FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
  (hval : (WNear.Binary.hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
  (hnone : (WNear.Binary.hostOf ctx raw).storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a) = none)
  (h : Wasm.NearState) (he : NearLogic.eraseP h = NearLogic.eraseP (WNear.Binary.hostOf ctx raw))
  (hproof : NearLogic.ProofBudget h ctx.trie (WNear.proofBound ctx)) :
  WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs ctx.trie (WNear.proofBound ctx) h
```

## Bridge.Methods.FtBalanceOfCopiedRun

`WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre` (hash `54364cd24fe8c9bf`)

```lean
inductive WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
  (st : Near.TrieOverlay.State) (bud : ℕ) (e : Wasm.NearState) : Prop
| WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre.mk {S : WNear.State} {a : WNear.AccountId} {bs : List UInt8}
  {st : Near.TrieOverlay.State} {bud : ℕ} {e : Wasm.NearState} (input : e.context.input = bs)
  (inputLimit : Wasm.Near.withinLimit e.config.maxRegisterLen bs.length = true)
  (value : e.storage WNear.stateKey = some (WNear.header S)) (accounting : e.storageAccounting = some st)
  (keyLimit : Wasm.Near.withinLimit e.config.maxStorageKeyLen 5 = true) (canonical : NearLogic.Canon st)
  (link : NearLogic.StorageLink e st) (proof : NearLogic.ProofBudget e st bud)
  (budget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey e.context.currentAccountId WNear.stateKey)
          (e.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey e.context.currentAccountId (WNear.Binary.BalanceOf297AbsentCall.copiedKey a))
          (e.storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a)) ≤
      bud)
  (accountLimit :
    Wasm.Near.withinLimit e.config.maxStorageKeyLen (WNear.Binary.BalanceOf297AbsentCall.copiedKey a).length = true)
  (absent : e.storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a) = none)
  (registerLimit : Wasm.Near.withinLimit e.config.maxRegisterLen 29 = true)
  (returnLimit : Wasm.Near.withinLimit e.config.maxReturnLen 3 = true) :
  WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs st bud e
```

`WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre.mk` (hash `0000000052bb1540`)

```lean
constant WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre.mk {S : WNear.State} {a : WNear.AccountId} {bs : List UInt8}
  {st : Near.TrieOverlay.State} {bud : ℕ} {e : Wasm.NearState} (input : e.context.input = bs)
  (inputLimit : Wasm.Near.withinLimit e.config.maxRegisterLen bs.length = true)
  (value : e.storage WNear.stateKey = some (WNear.header S)) (accounting : e.storageAccounting = some st)
  (keyLimit : Wasm.Near.withinLimit e.config.maxStorageKeyLen 5 = true) (canonical : NearLogic.Canon st)
  (link : NearLogic.StorageLink e st) (proof : NearLogic.ProofBudget e st bud)
  (budget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey e.context.currentAccountId WNear.stateKey)
          (e.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey e.context.currentAccountId (WNear.Binary.BalanceOf297AbsentCall.copiedKey a))
          (e.storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a)) ≤
      bud)
  (accountLimit :
    Wasm.Near.withinLimit e.config.maxStorageKeyLen (WNear.Binary.BalanceOf297AbsentCall.copiedKey a).length = true)
  (absent : e.storage (WNear.Binary.BalanceOf297AbsentCall.copiedKey a) = none)
  (registerLimit : Wasm.Near.withinLimit e.config.maxRegisterLen 29 = true)
  (returnLimit : Wasm.Near.withinLimit e.config.maxReturnLen 3 = true) :
  WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs st bud e
```

`WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement` (hash `20955a8546fad3ab`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : NearInterface.RawStorage) (modelSt : Option WNear.State) (a : WNear.AccountId) (tr : Near.TrieOverlay.State)
  (e0 : Wasm.NearState) : Prop :=
  ∀ (e : Wasm.NearState),
    WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a tr e0 e →
      WNear.Binary.AgreesWith (WNear.wnear cfg) ctx raw e
        ((WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a))
```

`WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt` (hash `3c67f63693cfa7e3`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : NearInterface.RawStorage) (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId)
  (bs : List UInt8) (tr : Near.TrieOverlay.State) (bud : ℕ) : Prop :=
  (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
      WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs tr bud
        (NearLogic.erase (WNear.Binary.hostOf ctx raw))) ∧
    WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs tr bud
      (NearLogic.eraseP (WNear.Binary.hostOf ctx raw))
```

`WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_with_obligations` (hash `00000000d790c0fa`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_with_obligations (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (modelSt : Option WNear.State)
  (ctx : NearInterface.Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ)
  (tr : Near.TrieOverlay.State) (bud : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hentry : WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
  (hag :
    WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement cfg ctx raw modelSt a tr
      (NearLogic.erase (WNear.Binary.hostOf ctx raw)))
  (hagP :
    WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement cfg ctx raw modelSt a tr
      (NearLogic.eraseP (WNear.Binary.hostOf ctx raw))) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.array_absent_runs` (hash `0000000058ef40de`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_runs (cfg : Wasm.Near.RuntimeConfig) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) (st : Near.TrieOverlay.State) (bud : ℕ)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  WNear.Binary.MethodRunsR cfg 297 (WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs st bud)
    (WNear.Binary.BalanceOf297AbsentCall.copiedMethodCost cfg S a bs rest j k)
    (WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a st)
```

`WNear.Binary.BalanceOf297AbsentCall.copiedKey` (hash `dc3b8033cf61cb24`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.copiedKey (a : WNear.AccountId) : List UInt8 :=
  WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)
```

`WNear.Binary.BalanceOf297AbsentCall.copiedMethodCost` (hash `d96c7cc39b13266e`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.copiedMethodCost (cfg : Wasm.Near.RuntimeConfig) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) (e : Wasm.NearState) : ℕ :=
  11 * cfg.wasm.regularOpCost +
    WNear.Binary.BalanceOf297AbsentCall.initialBodyCost cfg.wasm e (NearLogic.inputHost e 0) S a
      bs rest j k
```

`WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost` (hash `df3f324ffca05ec2`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost (a : WNear.AccountId) (st : Near.TrieOverlay.State)
  (e e' : Wasm.NearState) : Prop :=
  ∃ h1 st1 h2,
    NearLogic.StorageReadPost (NearLogic.inputHost e 0) WNear.stateKey 0 st h1 ∧
      NearLogic.StorageReadPost h1 (WNear.Binary.BalanceOf297AbsentCall.copiedKey a) 0 st1 h2 ∧
        e' = NearLogic.erase (h2.selectReturnValue [34, 48, 34])
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_with_obligations` (hash `000000002e6fd377`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_with_obligations (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (modelSt : Option WNear.State)
  (ctx : NearInterface.Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ)
  (tr : Near.TrieOverlay.State) (bud : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hentry : WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
  (hag :
    WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement cfg ctx raw modelSt a tr
      (NearLogic.erase (WNear.Binary.hostOf ctx raw)))
  (hagP :
    WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement cfg ctx raw modelSt a tr
      (NearLogic.eraseP (WNear.Binary.hostOf ctx raw))) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_runs` (hash `0000000060dcf7c8`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_runs (cfg : Wasm.Near.RuntimeConfig) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) (st : Near.TrieOverlay.State) (bud : ℕ)
  (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he : bs[bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)]? = some 93)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) :
  WNear.Binary.MethodRunsR cfg 297 (WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs st bud)
    (WNear.Binary.BalanceOf297AbsentCall.copiedMethodCost cfg S a bs rest j k)
    (WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a st)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_post_field` (hash `000000001ce26f7e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_post_field {α : Type} (f : Wasm.NearState → α)
  (hf : ∀ (x : Wasm.NearState), f (NearLogic.erase x) = f x)
  (hsel : ∀ (x : Wasm.NearState) (b : List UInt8), f (x.selectReturnValue b) = f x)
  (hreg : ∀ (x : Wasm.NearState) (i : ℕ) (v : List UInt8), f (x.setRegister i v) = f x)
  (hacc :
    ∀ (x : Wasm.NearState) (a : Option Near.TrieOverlay.State),
      f
          { storage := x.storage, storageAccounting := a, storageProofSize := x.storageProofSize,
            storageReadsFromTrie := x.storageReadsFromTrie, storageKeys := x.storageKeys, iterators := x.iterators,
            nextIteratorId := x.nextIteratorId, registers := x.registers, context := x.context,
            subsidizedAmount := x.subsidizedAmount, returnData := x.returnData, logs := x.logs,
            promiseResults := x.promiseResults, promises := x.promises, gasWeights := x.gasWeights,
            returnedPromise := x.returnedPromise, yieldResumes := x.yieldResumes, actionHash := x.actionHash,
            existingYields := x.existingYields, config := x.config, randomSeed := x.randomSeed, gas := x.gas,
            gasProfile := x.gasProfile, extCosts := x.extCosts, fees := x.fees,
            outputDataReceivers := x.outputDataReceivers, lastError := x.lastError,
            lastExecutionIssue := x.lastExecutionIssue, yieldCreateToken := x.yieldCreateToken, crypto := x.crypto,
            registerWrite := x.registerWrite, storageLog := x.storageLog, actionProfile := x.actionProfile } =
        f x)
  {a : WNear.AccountId} {tr : Near.TrieOverlay.State} {e e' : Wasm.NearState}
  (hp : WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a tr e e') : f e' = f e
```

`WNear.Binary.BalanceOf297AbsentCall.copied_post_noPromises` (hash `0000000020aebfa1`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_post_noPromises {a : WNear.AccountId} {tr : Near.TrieOverlay.State}
  {e e' : Wasm.NearState} (hp : WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a tr e e')
  (hn : WNear.Binary.NoPromises e) : WNear.Binary.NoPromises e'
```

`WNear.Binary.BalanceOf297AbsentCall.export_297` (hash `0000000014e95657`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.export_297 : WNear.Binary.wNearModule.exportFunc? "ft_balance_of" = some 297
```

`WNear.Binary.BalanceOf297AbsentCall.funcType_297` (hash `00000000a15b7ede`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.funcType_297 :
  WNear.Binary.wNearModule.funcType? 297 = some { params := [], results := [] }
```

`WNear.Binary.BalanceOf297AbsentCall.initial_body_cost_erase` (hash `0000000084791aca`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_body_cost_erase (cfg : Wasm.Near.WasmConfig) (e : Wasm.NearState)
  (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : ℕ) :
  WNear.Binary.BalanceOf297AbsentCall.initialBodyCost cfg (NearLogic.erase e)
      (NearLogic.inputHost (NearLogic.erase e) 0) S a bs rest j k =
    WNear.Binary.BalanceOf297AbsentCall.initialBodyCost cfg e (NearLogic.inputHost e 0) S a bs rest j k
```

`WNear.Binary.BalanceOf297AbsentCall.storage_read_post_erase_source` (hash `0000000076f3b9ae`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.storage_read_post_erase_source (h : Wasm.NearState) (key : List UInt8) (r : UInt64)
  (st : Near.TrieOverlay.State) (h' : Wasm.NearState) :
  NearLogic.StorageReadPost (NearLogic.erase h) key r st h' ↔ NearLogic.StorageReadPost h key r st h'
```

`WNear.Binary.BalanceOf297AbsentCall.storage_read_post_field` (hash `000000005acbec18`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.storage_read_post_field {α : Type} (f : Wasm.NearState → α)
  (hf : ∀ (x : Wasm.NearState), f (NearLogic.erase x) = f x)
  (hreg : ∀ (x : Wasm.NearState) (i : ℕ) (v : List UInt8), f (x.setRegister i v) = f x)
  (hacc :
    ∀ (x : Wasm.NearState) (a : Option Near.TrieOverlay.State),
      f
          { storage := x.storage, storageAccounting := a, storageProofSize := x.storageProofSize,
            storageReadsFromTrie := x.storageReadsFromTrie, storageKeys := x.storageKeys, iterators := x.iterators,
            nextIteratorId := x.nextIteratorId, registers := x.registers, context := x.context,
            subsidizedAmount := x.subsidizedAmount, returnData := x.returnData, logs := x.logs,
            promiseResults := x.promiseResults, promises := x.promises, gasWeights := x.gasWeights,
            returnedPromise := x.returnedPromise, yieldResumes := x.yieldResumes, actionHash := x.actionHash,
            existingYields := x.existingYields, config := x.config, randomSeed := x.randomSeed, gas := x.gas,
            gasProfile := x.gasProfile, extCosts := x.extCosts, fees := x.fees,
            outputDataReceivers := x.outputDataReceivers, lastError := x.lastError,
            lastExecutionIssue := x.lastExecutionIssue, yieldCreateToken := x.yieldCreateToken, crypto := x.crypto,
            registerWrite := x.registerWrite, storageLog := x.storageLog, actionProfile := x.actionProfile } =
        f x)
  {h h' : Wasm.NearState} {key : List UInt8} {r : UInt64} {tr : Near.TrieOverlay.State}
  (hp : NearLogic.StorageReadPost h key r tr h') : f h' = f h
```

## Bridge.Methods.FtBalanceOfInitialAdequacy

`WNear.Binary.BalanceOf297AbsentCall.array_absent_adequate` (hash `000000007508fc82`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_adequate (runtime : Wasm.Near.RuntimeConfig) (Cg : ℕ)
  (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest)) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true)
  (hgas :
    h0.gas.used +
        (475 * runtime.wasm.regularOpCost +
          (3 * runtime.wasm.regularOpCost +
            (100 * runtime.wasm.regularOpCost + WNear.Binary.EnvInput.cost527 runtime.wasm h0 +
              (100 * runtime.wasm.regularOpCost +
                (100 * runtime.wasm.regularOpCost +
                  (1000 * runtime.wasm.regularOpCost +
                      (45 * runtime.wasm.regularOpCost +
                        ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * runtime.wasm.regularOpCost +
                          WNear.Binary.SerdeStruct78Esc.costArray runtime.wasm 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost runtime.wasm
                      (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a 0)))))) ≤
      Cg)
  (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid) :
  Iris.ProgramLogic.adequate Iris.Stuckness.MaybeStuck
    (NearLogic.MCode.running runtime.wasm Wasm.Near.execLimits
      (NearLogic.entryThread
        { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
          mi := WNear.Binary.wInst }
        0 WNear.Binary.f297.body))
    { store := WNear.Binary.wStore runtime h0 } fun v σ' =>
    v = NearLogic.Ending.values [] ∧
      ∃ cs, WNear.Binary.BalanceOf297AbsentCall.endCells297 Cg h a st cs ∧ ∀ p ∈ cs, NearLogic.mlookup σ' p.1 = some p.2
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_adequate` (hash `000000008cd89b9b`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_adequate (runtime : Wasm.Near.RuntimeConfig) (Cg : ℕ)
  (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true)
  (hgas :
    h0.gas.used +
        (475 * runtime.wasm.regularOpCost +
          (3 * runtime.wasm.regularOpCost +
            (100 * runtime.wasm.regularOpCost + WNear.Binary.EnvInput.cost527 runtime.wasm h0 +
              (100 * runtime.wasm.regularOpCost +
                (100 * runtime.wasm.regularOpCost +
                  (1000 * runtime.wasm.regularOpCost +
                      (45 * runtime.wasm.regularOpCost +
                        ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * runtime.wasm.regularOpCost +
                          WNear.Binary.SerdeStruct78Esc.costArray runtime.wasm 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost runtime.wasm
                      (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a 0)))))) ≤
      Cg)
  (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid) :
  Iris.ProgramLogic.adequate Iris.Stuckness.MaybeStuck
    (NearLogic.MCode.running runtime.wasm Wasm.Near.execLimits
      (NearLogic.entryThread
        { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
          mi := WNear.Binary.wInst }
        0 WNear.Binary.f297.body))
    { store := WNear.Binary.wStore runtime h0 } fun v σ' =>
    v = NearLogic.Ending.values [] ∧
      ∃ cs, WNear.Binary.BalanceOf297AbsentCall.endCells297 Cg h a st cs ∧ ∀ p ∈ cs, NearLogic.mlookup σ' p.1 = some p.2
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_adequate_host` (hash `00000000a528acf3`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_adequate_host (runtime : Wasm.Near.RuntimeConfig) (Cg : ℕ)
  (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true)
  (hgas :
    h0.gas.used +
        (475 * runtime.wasm.regularOpCost +
          (3 * runtime.wasm.regularOpCost +
            (100 * runtime.wasm.regularOpCost + WNear.Binary.EnvInput.cost527 runtime.wasm h0 +
              (100 * runtime.wasm.regularOpCost +
                (100 * runtime.wasm.regularOpCost +
                  (1000 * runtime.wasm.regularOpCost +
                      (45 * runtime.wasm.regularOpCost +
                        ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * runtime.wasm.regularOpCost +
                          WNear.Binary.SerdeStruct78Esc.costArray runtime.wasm 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost runtime.wasm
                      (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a 0)))))) ≤
      Cg)
  (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid) :
  Iris.ProgramLogic.adequate Iris.Stuckness.MaybeStuck
    (NearLogic.MCode.running runtime.wasm Wasm.Near.execLimits (WNear.Binary.startW runtime h0 297).thread)
    { store := WNear.Binary.wStore runtime h0 } fun v σ' =>
    v = NearLogic.Ending.values [] ∧
      ∃ h1 st1 h2,
        NearLogic.StorageReadPost h WNear.stateKey 0 st h1 ∧
          NearLogic.StorageReadPost h1
              (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) 0 st1
              h2 ∧
            NearLogic.erase σ'.store.host = NearLogic.erase (h2.selectReturnValue [34, 48, 34]) ∧
              σ'.store.host.gas.used ≤ Cg
```

`WNear.Binary.BalanceOf297AbsentCall.endCells297` (hash `2d8599caed4841ac`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.endCells297 (Cg : ℕ) (h : Wasm.NearState) (a : WNear.AccountId)
  (st : Near.TrieOverlay.State) (cs : List (WasmLogic.Loc × WasmLogic.Cell Wasm.NearState)) : Prop :=
  ∃ h1 st1 h2 g p act,
    NearLogic.StorageReadPost h WNear.stateKey 0 st h1 ∧
      NearLogic.StorageReadPost h1
          (WNear.accountsPrefix ++
            (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))
          0 st1 h2 ∧
        cs =
            [(WasmLogic.Loc.host,
                WasmLogic.Cell.host (NearLogic.erase (h2.selectReturnValue [34, 48, 34]))),
              (NearLogic.gasLoc, NearLogic.gasCellOf g p act)] ∧
          g.used ≤ Cg
```

`WNear.Binary.BalanceOf297AbsentCall.endCells297_ends` (hash `000000007723e885`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.endCells297_ends {Cg : ℕ} {h : Wasm.NearState} {a : WNear.AccountId}
  {st : Near.TrieOverlay.State} {σ' : NearLogic.MStore} {cs : List (WasmLogic.Loc × WasmLogic.Cell Wasm.NearState)}
  (hc : WNear.Binary.BalanceOf297AbsentCall.endCells297 Cg h a st cs)
  (hl : ∀ p ∈ cs, NearLogic.mlookup σ' p.1 = some p.2) :
  ∃ h1 st1 h2,
    NearLogic.StorageReadPost h WNear.stateKey 0 st h1 ∧
      NearLogic.StorageReadPost h1
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) 0 st1
          h2 ∧
        NearLogic.erase σ'.store.host = NearLogic.erase (h2.selectReturnValue [34, 48, 34]) ∧
          σ'.store.host.gas.used ≤ Cg
```

`WNear.Binary.BalanceOf297AbsentCall.entryCost_297` (hash `00000000c478b2b3`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.entryCost_297 (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  Wasm.Near.entryCost cfg.wasm (Wasm.StepResult.next (WNear.Binary.startW cfg h 297)) = 11 * cfg.wasm.regularOpCost
```

`WNear.Binary.BalanceOf297AbsentCall.f297_frame` (hash `000000000fea2504`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.f297_frame : WNear.Binary.funcs[297 - 48]! = WNear.Binary.f297
```

`WNear.Binary.BalanceOf297AbsentCall.startW_thread297` (hash `000000009549854e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.startW_thread297 (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  (WNear.Binary.startW cfg h 297).thread =
    NearLogic.entryThread
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
        mi := WNear.Binary.wInst }
      0 WNear.Binary.f297.body
```

## Bridge.Methods.FtBalanceOfInitialCompose

`WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_resources` (hash `000000006271d7f2`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_resources {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (runtime : Wasm.Near.RuntimeConfig) (cfg : Wasm.Near.WasmConfig)
  (lim : Wasm.ExecLimits) (d : ℕ) (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (a : WNear.AccountId)
  (bs jsonRest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest)) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOf297AbsentCall.code297 runtime.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
      NearLogic.credits Cg
          (475 * cfg.regularOpCost +
            (3 * cfg.regularOpCost +
              (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
                (100 * cfg.regularOpCost +
                  (100 * cfg.regularOpCost +
                    (1000 * cfg.regularOpCost +
                        (45 * cfg.regularOpCost +
                          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
                            WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                        (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
        0 ↦[wg] WNear.Binary.InitialState.g0 ∗
          WNear.Binary.InitialState.frame297 0 ∗
            WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
              0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                  0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        NearLogic.mhostPt h0 ∗
                          ▷
                            ∀ p c,
                              (NearLogic.credits Cg R ∗
                                  (∃ ip, 0 ↦[wms][ (1048416 + 24).toNat ] WasmLogic.bytes32 ip) ∗
                                    0 ↦[wms][ (1048416 + 24).toNat + 4 ] WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                                      0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                        0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                          0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
                                              (∃ hl,
                                                  WNear.Binary.AllocInv.heapInv 0 2048 hl []
                                                    (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1 +
                                                                1 +
                                                              1 +
                                                            3 +
                                                          1 +
                                                        1 +
                                                      1)) ∗
                                                ∃ h1,
                                                  ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
                                                    ∃ st1 h2,
                                                      ⌜NearLogic.StorageReadPost h1
                                                            (WNear.accountsPrefix ++
                                                              (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++
                                                                (↑a).toUTF8.toList))
                                                            0 st1 h2⌝ ∗
                                                        NearLogic.mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
                                Φ.normal []
                                  (WNear.Binary.BalanceOf297AbsentCall.frame 0 WNear.Binary.wInst 1048416
                                    (UInt32.ofNat (↑a).utf8ByteSize) (WNear.Binary.VecFromElem.pair64 p c)
                                    (1048416 + 40))) ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
        mi := WNear.Binary.wInst }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_resources` (hash `000000004d9d3600`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_resources {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (runtime : Wasm.Near.RuntimeConfig) (cfg : Wasm.Near.WasmConfig)
  (lim : Wasm.ExecLimits) (d : ℕ) (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (a : WNear.AccountId)
  (bs jsonRest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOf297AbsentCall.code297 runtime.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
      NearLogic.credits Cg
          (475 * cfg.regularOpCost +
            (3 * cfg.regularOpCost +
              (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
                (100 * cfg.regularOpCost +
                  (100 * cfg.regularOpCost +
                    (1000 * cfg.regularOpCost +
                        (45 * cfg.regularOpCost +
                          ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
                            WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                      WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                        (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
        0 ↦[wg] WNear.Binary.InitialState.g0 ∗
          WNear.Binary.InitialState.frame297 0 ∗
            WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
              0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                  0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        NearLogic.mhostPt h0 ∗
                          ▷
                            ∀ p c,
                              (NearLogic.credits Cg R ∗
                                  (∃ ip, 0 ↦[wms][ (1048416 + 24).toNat ] WasmLogic.bytes32 ip) ∗
                                    0 ↦[wms][ (1048416 + 24).toNat + 4 ] WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                                      0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                        0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                          0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
                                              (∃ hl,
                                                  WNear.Binary.AllocInv.heapInv 0 2048 hl []
                                                    (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1 +
                                                                1 +
                                                              1 +
                                                            3 +
                                                          1 +
                                                        1 +
                                                      1)) ∗
                                                ∃ h1,
                                                  ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
                                                    ∃ st1 h2,
                                                      ⌜NearLogic.StorageReadPost h1
                                                            (WNear.accountsPrefix ++
                                                              (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++
                                                                (↑a).toUTF8.toList))
                                                            0 st1 h2⌝ ∗
                                                        NearLogic.mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
                                Φ.normal []
                                  (WNear.Binary.BalanceOf297AbsentCall.frame 0 WNear.Binary.wInst 1048416
                                    (UInt32.ofNat (↑a).utf8ByteSize) (WNear.Binary.VecFromElem.pair64 p c)
                                    (1048416 + 40))) ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
        mi := WNear.Binary.wInst }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_store` (hash `0000000028d8ec0c`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_store {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (runtime : Wasm.Near.RuntimeConfig) (cfg : Wasm.Near.WasmConfig)
  (lim : Wasm.ExecLimits) (d : ℕ) (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (a : WNear.AccountId)
  (bs jsonRest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs)) (h0 h : Wasm.NearState)
  (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true)
  (hgas :
    h0.gas.used +
        (475 * cfg.regularOpCost +
          (3 * cfg.regularOpCost +
            (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
              (100 * cfg.regularOpCost +
                (100 * cfg.regularOpCost +
                  (1000 * cfg.regularOpCost +
                      (45 * cfg.regularOpCost +
                        ((700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
                          WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0 bs (↑a).toUTF8.toList jsonRest j)) +
                    WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg
                      (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) h S a R)))))) ≤
      Cg)
  (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WasmLogic.ownCells (NearLogic.mheapOf { store := WNear.Binary.wStore runtime h0 }) ∗
      ▷
        ∀ p c,
          (NearLogic.credits Cg R ∗
              (∃ ip, 0 ↦[wms][ (1048416 + 24).toNat ] WasmLogic.bytes32 ip) ∗
                0 ↦[wms][ (1048416 + 24).toNat + 4 ] WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                  0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                    0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                      0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                        0 ↦[wg] WNear.Binary.InitialState.g0 ∗
                          (∃ hl,
                              WNear.Binary.AllocInv.heapInv 0 2048 hl []
                                (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1 + 1 + 1 + 3 + 1 + 1 +
                                  1)) ∗
                            ∃ h1,
                              ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
                                ∃ st1 h2,
                                  ⌜NearLogic.StorageReadPost h1
                                        (WNear.accountsPrefix ++
                                          (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))
                                        0 st1 h2⌝ ∗
                                    NearLogic.mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
            Φ.normal []
              (WNear.Binary.BalanceOf297AbsentCall.frame 0 WNear.Binary.wInst 1048416 (UInt32.ofNat (↑a).utf8ByteSize)
                (WNear.Binary.VecFromElem.pair64 p c) (1048416 + 40))) ⊢
    |==>
      NearLogic.mwpi cfg lim d
        { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
          mi := WNear.Binary.wInst }
        [] WNear.Binary.f297.body Φ
```

## Bridge.Methods.FtBalanceOfInputBound

`WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_gas_bound` (hash `00000000e4bff134`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_gas_bound {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (cfg : Wasm.Near.WasmConfig) (lim : Wasm.ExecLimits) (d inst e : ℕ)
  (mi : Wasm.ModuleInst) (A : ℕ → ℕ) (n g ta : ℕ) (mx : Option ℕ) (hm : WNear.Binary.Interface.IfaceMod mi A n g ta)
  (hd : d + 39 < lim.maxCallDepth) (Cg R : ℕ) (gt : Wasm.GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 idx : UInt32)
  (len : ℕ) (a : WNear.AccountId) (live : List (ℕ × ℕ)) (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8)
  (j k : ℕ) (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32)
  (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 < 2 ^ 32) (hopt : oldOpt.length = 12)
  (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
  (modelCfg : WNear.Config) (modelCtx : NearInterface.Context) (modelSt : Option WNear.State)
  (hargs : modelCtx.args = bs)
  (hgas : (WNear.wnear modelCfg).gas modelCtx modelSt (WNear.Call.ftBalanceOf a) ≤ modelCtx.gasLimit)
  (hmax : WNear.Binary.FtBalanceOfMethod.BurnLimitV86 modelCtx.protocol)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 91)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (he :
    bs[bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs)]? =
      some 93)
  (hk : k = bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, jsonRest))
  (hcopied : ¬WNear.Binary.ParseStr.borrowed (List.drop (j + 1) bs))
  (hparserRoom :
    ∀ (len' : ℕ),
      len' = len ∨ len' = WNear.Binary.VecFromElem.grownLen len (UInt32.ofNat bs.length) →
        WNear.Binary.ParseStr.roomRun 2048 len' 0 [] (List.drop (j + 1) bs))
  (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
  (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12)
  (hhead : head.length = 8) (h0 h : Wasm.NearState) (hinput : h0.context.input = bs)
  (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hroom :
    WNear.Binary.LookupMapOps.HeapRoomK
      ((WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
          WNear.Binary.BalanceOf297AbsentCall.copiedParserPages bs (j + 1) a +
        6)
      len 2048)
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true) (ptr0 : UInt32)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  WNear.Binary.FtTotalSupply.codeA inst mi A ∗
      WNear.Binary.EnvInput.inCode e inst mi A n 2048 mx ∗
        A 527 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f527 ∗
          WNear.Binary.SerdeFromTrait.code66 n 2048 inst mi A ∗
            WNear.Binary.SerdeAccountId.code169 n 2048 inst mi A ∗
              WNear.Binary.ParseStr.code646 n 2048 inst mi A ∗
                A 644 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f644 ∗
                  A 66 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f66 ∗
                    A 65 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f65 ∗
                      A 157 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f157 ∗
                        WNear.Binary.StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
                          A 219 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f219 ∗
                            A 155 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f155 ∗
                              A 951 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[15]! inst WNear.Binary.f951 ∗
                                WNear.Binary.BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗
                                  A 293 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f293 ∗
                                    WNear.Binary.ToVec.tvCode n 2048 inst mi A ∗
                                      A 96 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f96 ∗
                                        A 158 ↪[wf] Wasm.FuncInst.wasm WNear.Binary.types[31]! inst WNear.Binary.f158 ∗
                                          A 779 ↪[wf]
                                              Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f779 ∗
                                            A 545 ↪[wf]
                                                Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f545 ∗
                                              A 456 ↪[wf]
                                                  Wasm.FuncInst.wasm WNear.Binary.types[14]! inst WNear.Binary.f456 ∗
                                                WNear.Binary.DropVec.dropCode inst mi A ∗
                                                  A 68 ↪[wf]
                                                      Wasm.FuncInst.wasm WNear.Binary.types[0]! inst WNear.Binary.f68 ∗
                                                    WNear.Binary.Interface.ifaceCode e inst mi A n mx ∗
                                                      inst ↪[inst] mi ∗
                                                        NearLogic.credits Cg
                                                            (475 * cfg.regularOpCost +
                                                              (3 * cfg.regularOpCost +
                                                                (100 * cfg.regularOpCost +
                                                                    WNear.Binary.EnvInput.cost527 cfg h0 +
                                                                  (100 * cfg.regularOpCost +
                                                                    (100 * cfg.regularOpCost +
                                                                      (1000 * cfg.regularOpCost +
                                                                          (45 * cfg.regularOpCost +
                                                                            ((700 +
                                                                                  96 *
                                                                                    WNear.Binary.SerdeRead.wsLen
                                                                                      (List.drop k bs)) *
                                                                                cfg.regularOpCost +
                                                                              WNear.Binary.SerdeStruct78Esc.costArray
                                                                                cfg 1 0 bs (↑a).toUTF8.toList jsonRest
                                                                                j)) +
                                                                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost
                                                                          cfg
                                                                          (WNear.Binary.BalanceOf297AbsentCall.copiedParserFree
                                                                            bs (j + 1) 1)
                                                                          h S a R)))))) ∗
                                                          g ↦[wg] { type := gt, value := Wasm.Value.i32 (s + 160) } ∗
                                                            WNear.Binary.VecFromElem.stk n (s.toNat - 592) 592 ∗
                                                              WNear.Binary.SetupPanicHook.hookCells n 0 hookOld 0 ∗
                                                                n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                                                  ta ↦[wt][ 116 ] Wasm.Ref.func (A 565) ∗
                                                                    ta ↦[wt][ 106 ] Wasm.Ref.func (A 564) ∗
                                                                      WNear.Binary.SetBlockchainInterface.blockchainInterfaceCells
                                                                          n 0 0 0 k3 ∗
                                                                        WNear.Binary.FtTotalSupply.vtab n ta A ∗
                                                                          n ↦[wms][ 1050188 + 36 ]
                                                                              WNear.Binary.Interface.dataWord
                                                                                (1050188 + 36) ∗
                                                                            ta ↦[wt][ 44 ] Wasm.Ref.func (A 246) ∗
                                                                              WNear.Binary.AllocFirstFit.vt n 1057464
                                                                                  idx ta (A 578) ∗
                                                                                n ↦[wms][ 1049788 ]
                                                                                    WNear.Binary.StateRead.stateKey ∗
                                                                                  NearLogic.mhostPt h0 ∗
                                                                                    WNear.Binary.AllocInv.heapInv n 2048
                                                                                        len live 1 ∗
                                                                                      n ↦[wms][ (s + 88).toNat ]
                                                                                          oldOpt ∗
                                                                                        n ↦[wms][ (s + 100).toNat ]
                                                                                            optTail ∗
                                                                                          n ↦[wms][ 1062392 ]
                                                                                              WNear.Binary.ParseStr.escTable ∗
                                                                                            n ↦[wms][ 1071704 ]
                                                                                                WNear.Binary.FromUtf8Gen.utf8Width ∗
                                                                                              n ↦[wms][ 1062712 ]
                                                                                                  WNear.Binary.SerdeEsc.hexTable ∗
                                                                                                n ↦[wms][
                                                                                                    (s + 104).toNat ]
                                                                                                    stateTail ∗
                                                                                                  n ↦[wms][
                                                                                                      (s + 128).toNat ]
                                                                                                      oldA ∗
                                                                                                    n ↦[wms][
                                                                                                        (s +
                                                                                                              128).toNat +
                                                                                                          8 ]
                                                                                                        WasmLogic.bytes32
                                                                                                          oldC ∗
                                                                                                      n ↦[wms][
                                                                                                          (s +
                                                                                                              140).toNat ]
                                                                                                          destTail ∗
                                                                                                        ⋯ ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 x1, Wasm.Value.i64 x2, Wasm.Value.i32 x3], inst := inst, mi := mi }
      [] WNear.Binary.f297.body Φ
```

`WNear.Binary.FtBalanceOfMethod.BurnLimitV86` (hash `6bda1514ee21b6c9`)

```lean
def WNear.Binary.FtBalanceOfMethod.BurnLimitV86 (p : Wasm.Near.RuntimeConfig) : Prop :=
  p.wasm.limits.maxGasBurnt ≤ 10 ^ 15
```

`WNear.Binary.FtBalanceOfMethod.argument_charge_le_limit` (hash `000000007a53b068`)

```lean
theorem WNear.Binary.FtBalanceOfMethod.argument_charge_le_limit (cfg : WNear.Config) (ctx : NearInterface.Context)
  (st : Option WNear.State) (a : WNear.AccountId)
  (hgas : (WNear.wnear cfg).gas ctx st (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit) :
  WNear.argumentByteGas * List.length ctx.args ≤ ctx.gasLimit
```

`WNear.Binary.FtBalanceOfMethod.argument_length_lt_2_24` (hash `0000000024fdaef7`)

```lean
theorem WNear.Binary.FtBalanceOfMethod.argument_length_lt_2_24 (cfg : WNear.Config) (ctx : NearInterface.Context)
  (st : Option WNear.State) (a : WNear.AccountId)
  (hgas : (WNear.wnear cfg).gas ctx st (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit)
  (hmax : WNear.Binary.FtBalanceOfMethod.BurnLimitV86 ctx.protocol) : List.length ctx.args < 2 ^ 24
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

## Bridge.Methods.FtBalanceOfModelGas

`WNear.Binary.BalanceOf297AbsentCall.initial_total_cost_le_model` (hash `00000000292c8331`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.initial_total_cost_le_model (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : WNear.RawStorage) (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8)
  (j k size : ℕ) (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
  (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest))
  (hv : (NearLogic.erase (WNear.Binary.hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
  (hnone :
    (NearLogic.erase (WNear.Binary.hostOf ctx raw)).storage
        (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none) :
  NearLogic.chargesUse (WNear.Binary.hostOf ctx raw) (Wasm.Near.loadingCharges size) +
        11 * ctx.protocol.wasm.regularOpCost +
      WNear.Binary.BalanceOf297AbsentCall.initialBodyCost ctx.protocol.wasm
        (NearLogic.erase (WNear.Binary.hostOf ctx raw))
        (NearLogic.inputHost (NearLogic.erase (WNear.Binary.hostOf ctx raw)) 0) S a bs rest j k ≤
    (WNear.wnear cfg).gas ctx st (WNear.Call.ftBalanceOf a)
```

## Bridge.Methods.FtBalanceOfObjectAdequacy

`WNear.Binary.BalanceOf297AbsentCall.objectBodyCost` (hash `1105112e21cc376d`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.objectBodyCost (cfg : Wasm.Near.WasmConfig) (h0 h : Wasm.NearState)
  (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ) : ℕ :=
  475 * cfg.regularOpCost +
    (3 * cfg.regularOpCost +
      (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
        (100 * cfg.regularOpCost +
          (100 * cfg.regularOpCost +
            (1000 * cfg.regularOpCost + WNear.Binary.SerdeObjectNoEsc.parserCost cfg 1 bs rest N +
              WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg 2 h S a 0)))))
```

`WNear.Binary.BalanceOf297AbsentCall.object_absent_adequate` (hash `0000000074af4f32`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_adequate (runtime : Wasm.Near.RuntimeConfig) (Cg : ℕ)
  (a : WNear.AccountId) (bs jsonRest : List UInt8) (N : ℕ) (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (h0 h : Wasm.NearState) (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true)
  (hgas : h0.gas.used + WNear.Binary.BalanceOf297AbsentCall.objectBodyCost runtime.wasm h0 h S a bs jsonRest N ≤ Cg)
  (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid) :
  Iris.ProgramLogic.adequate Iris.Stuckness.MaybeStuck
    (NearLogic.MCode.running runtime.wasm Wasm.Near.execLimits
      (NearLogic.entryThread
        { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
          mi := WNear.Binary.wInst }
        0 WNear.Binary.f297.body))
    { store := WNear.Binary.wStore runtime h0 } fun v σ' =>
    v = NearLogic.Ending.values [] ∧
      ∃ cs, WNear.Binary.BalanceOf297AbsentCall.endCells297 Cg h a st cs ∧ ∀ p ∈ cs, NearLogic.mlookup σ' p.1 = some p.2
```

## Bridge.Methods.FtBalanceOfObjectCase

`WNear.Binary.BalanceOf297AbsentCall.ObjectAbsentCase` (hash `4324fccd5b0657a0`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.ObjectAbsentCase (st : Option WNear.State) (ctx : NearInterface.Context)
  (c : WNear.Call) : Prop :=
  ∃ S a bs rest N,
    st = some S ∧
      c = WNear.Call.ftBalanceOf a ∧
        a ∉ S.registered ∧
          ctx.args = bs ∧
            bs.length ≤ 4194304 ∧
              92 ∉ bs ∧
                bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123 ∧
                  WNear.SerdeStructModel.objLoop "account_id"
                        (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R N
                        none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
                      some (some a, rest) ∧
                    bs.length - rest.length +
                        WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) =
                      bs.length
```

`WNear.Binary.BalanceOf297AbsentCall.object_case_accepted` (hash `00000000a0b21b15`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_case_accepted (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (c : WNear.Call) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hcase : WNear.Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.object_case_no_issue` (hash `000000002b2cf579`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_case_no_issue (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (he : WNear.Binary.Exported.Environment protocol) (hsize : size ≤ 185625) (raw : WNear.RawStorage)
  (st : Option WNear.State) (ctx : NearInterface.Context) (c : WNear.Call) (hrep : (WNear.wnear cfg).Represents raw st)
  (hwf : ctx.WF raw) (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hcase : WNear.Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c) (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
```

## Bridge.Methods.FtBalanceOfObjectGas

`WNear.Binary.BalanceOf297AbsentCall.object_body_cost_le` (hash `00000000ce0df66f`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_body_cost_le (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (h0 h : Wasm.NearState) (S : WNear.State) (a : WNear.AccountId)
  (bs rest : List UInt8) (N : ℕ) (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest)) :
  WNear.Binary.BalanceOf297AbsentCall.objectBodyCost p.wasm h0 h S a bs rest N ≤
    100 * 10 ^ 9 + 397500000 * bs.length + WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse h0 h a bs
```

`WNear.Binary.BalanceOf297AbsentCall.object_host_cost_le` (hash `000000005e04bce6`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_host_cost_le (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (h : Wasm.NearState) (S : WNear.State) (a : WNear.AccountId)
  (bs : List UInt8) (hext : h.extCosts = p.wasm.extCosts) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none) :
  WNear.Binary.BalanceOf297AbsentCall.initialBodyHostUse h (NearLogic.inputHost h 0) a bs ≤
    200 * 10 ^ 9 + 3 * 10 ^ 6 * bs.length +
          NearLogic.readNodes h
              (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.Binary.StateRead.stateKey) *
            NearLogic.trieNodeMax h +
        NearLogic.readNodes h
            (Near.TrieOverlay.contractKey h.context.currentAccountId
              (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) *
          NearLogic.trieNodeMax h +
      NearLogic.valueReturnDataGas h 3
```

`WNear.Binary.BalanceOf297AbsentCall.object_total_cost_le_model` (hash `000000001ff26c53`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_total_cost_le_model (cfg : WNear.Config) (ctx : NearInterface.Context)
  (raw : WNear.RawStorage) (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8)
  (N size : ℕ) (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
  (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304) (hnb : 92 ∉ bs)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hv : (NearLogic.erase (WNear.Binary.hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
  (hnone :
    (NearLogic.erase (WNear.Binary.hostOf ctx raw)).storage
        (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none) :
  NearLogic.chargesUse (WNear.Binary.hostOf ctx raw) (Wasm.Near.loadingCharges size) +
        11 * ctx.protocol.wasm.regularOpCost +
      WNear.Binary.BalanceOf297AbsentCall.objectBodyCost ctx.protocol.wasm
        (NearLogic.erase (WNear.Binary.hostOf ctx raw))
        (NearLogic.inputHost (NearLogic.erase (WNear.Binary.hostOf ctx raw)) 0) S a bs rest N ≤
    (WNear.wnear cfg).gas ctx st (WNear.Call.ftBalanceOf a)
```

## Bridge.Methods.FtBalanceOfObjectInitial

`WNear.Binary.BalanceOf297AbsentCall.object_absent_body_initial_resources` (hash `0000000062941ace`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_body_initial_resources {GF : Iris.BundledGFunctors}
  [WasmLogic.WasmGS Wasm.NearState GF] (runtime : Wasm.Near.RuntimeConfig) (cfg : Wasm.Near.WasmConfig)
  (lim : Wasm.ExecLimits) (d : ℕ) (hd : d + 46 < lim.maxCallDepth) (Cg R : ℕ) (a : WNear.AccountId)
  (bs jsonRest : List UInt8) (N : ℕ) (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, jsonRest))
  (hend :
    bs.length - jsonRest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - jsonRest.length) bs) = bs.length)
  (h0 h : Wasm.NearState) (hinput : h0.context.input = bs) (hafter : NearLogic.inputHost h0 0 = h)
  (hinputLimit : Wasm.Near.withinLimit h0.config.maxRegisterLen bs.length = true) (S : WNear.State)
  (st : Near.TrieOverlay.State) (hv : h.storage WNear.stateKey = some (WNear.header S))
  (hacc : h.storageAccounting = some st) (hlim : Wasm.Near.withinLimit h.config.maxStorageKeyLen 5 = true)
  (hcanon : NearLogic.Canon st) (hlink : NearLogic.StorageLink h st) (bud : ℕ) (hproof : NearLogic.ProofBudget h st bud)
  (hbudget :
    NearLogic.readProofCost (Near.TrieOverlay.contractKey h.context.currentAccountId WNear.stateKey)
          (h.storage WNear.stateKey) +
        NearLogic.readProofCost
          (Near.TrieOverlay.contractKey h.context.currentAccountId
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)))
          (h.storage
            (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) ≤
      bud)
  (hlimAccount :
    Wasm.Near.withinLimit h.config.maxStorageKeyLen
        (List.length
          (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList))) =
      true)
  (hnone :
    h.storage (WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat (↑a).utf8ByteSize) ++ (↑a).toUTF8.toList)) =
      none)
  (hreg : Wasm.Near.withinLimit h.config.maxRegisterLen 29 = true)
  (hret : Wasm.Near.withinLimit h.config.maxReturnLen 3 = true) (Φ : WasmLogic.Post Wasm.NearState GF) :
  (WNear.Binary.BalanceOf297AbsentCall.code297 runtime.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
      WNear.Binary.SerdeIgnValue.code81 0 WNear.Binary.wInst id ∗
        NearLogic.credits Cg
            (475 * cfg.regularOpCost +
              (3 * cfg.regularOpCost +
                (100 * cfg.regularOpCost + WNear.Binary.EnvInput.cost527 cfg h0 +
                  (100 * cfg.regularOpCost +
                    (100 * cfg.regularOpCost +
                      (1000 * cfg.regularOpCost + WNear.Binary.SerdeObjectNoEsc.parserCost cfg 1 bs jsonRest N +
                        WNear.Binary.BalanceOf297AbsentCall.parserSuccessCost cfg 2 h S a R)))))) ∗
          0 ↦[wg] WNear.Binary.InitialState.g0 ∗
            WNear.Binary.InitialState.frame297 0 ∗
              WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
                0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                  0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                    0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                      0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                        0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                          WNear.Binary.SerdeObjectNoEsc.parserStatics 0 ∗
                            NearLogic.mhostPt h0 ∗
                              ▷
                                ∀ p c,
                                  (NearLogic.credits Cg R ∗
                                      (∃ ip, 0 ↦[wms][ (1048416 + 24).toNat ] WasmLogic.bytes32 ip) ∗
                                        0 ↦[wms][ (1048416 + 24).toNat + 4 ]
                                            WasmLogic.bytes32 (UInt32.ofNat bs.length) ∗
                                          0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                            0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                              0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                                WNear.Binary.SerdeObjectNoEsc.parserStatics 0 ∗
                                                  0 ↦[wg] WNear.Binary.InitialState.g0 ∗
                                                    (∃ hl,
                                                        WNear.Binary.AllocInv.heapInv 0 2048 hl []
                                                          (2 + 1 + 1 + 3 + 1 + 1 + 1)) ∗
                                                      ∃ h1,
                                                        ⌜NearLogic.StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
                                                          ∃ st1 h2,
                                                            ⌜NearLogic.StorageReadPost h1
                                                                  (WNear.accountsPrefix ++
                                                                    (WasmLogic.bytes32
                                                                        (UInt32.ofNat (↑a).utf8ByteSize) ++
                                                                      (↑a).toUTF8.toList))
                                                                  0 st1 h2⌝ ∗
                                                              NearLogic.mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
                                    Φ.normal []
                                      (WNear.Binary.BalanceOf297AbsentCall.frame 0 WNear.Binary.wInst 1048416
                                        (UInt32.ofNat (↑a).utf8ByteSize) (WNear.Binary.VecFromElem.pair64 p c)
                                        (1048416 + 40))) ⊢
    NearLogic.mwpi cfg lim d
      { locals := #[Wasm.Value.i32 0, Wasm.Value.i32 0, Wasm.Value.i64 0, Wasm.Value.i32 0], inst := 0,
        mi := WNear.Binary.wInst }
      [] WNear.Binary.f297.body Φ
```

## Bridge.Methods.FtBalanceOfObjectRefines

`WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_init` (hash `0000000059f7d7ad`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_init (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (ctx : NearInterface.Context) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hl : WNear.Binary.FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24)
  (hreceipt : bs.length ≤ 4194304) (hnb : 92 ∉ bs) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hend : bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) = bs.length)
  (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S)) (ha : a ∉ S.registered) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx (some S) (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_v86` (hash `00000000f7a32516`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_v86 (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (modelSt : Option WNear.State)
  (ctx : NearInterface.Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ)
  (tr : Near.TrieOverlay.State) (bud : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304) (hnb : 92 ∉ bs)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hend : bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) = bs.length)
  (hentry : WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
  (hrep : (WNear.wnear cfg).Represents raw modelSt) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_with_obligations` (hash `00000000d1534069`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_with_obligations (cfg : WNear.Config) (size : ℕ)
  (codeOf : List UInt8 → Near.ContractCode) (raw : WNear.RawStorage) (modelSt : Option WNear.State)
  (ctx : NearInterface.Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ)
  (tr : Near.TrieOverlay.State) (bud : ℕ) (hp : WNear.Binary.WProtocol ctx.protocol) (hwf : ctx.WF raw)
  (hm : ctx.method = "ft_balance_of") (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 ctx.protocol)
  (hsize : size ≤ 185625) (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304) (hnb : 92 ∉ bs)
  (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hend : bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) = bs.length)
  (hentry : WNear.Binary.BalanceOf297AbsentCall.CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
  (hag :
    WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement cfg ctx raw modelSt a tr
      (NearLogic.erase (WNear.Binary.hostOf ctx raw)))
  (hagP :
    WNear.Binary.BalanceOf297AbsentCall.CopiedAgreement cfg ctx raw modelSt a tr
      (NearLogic.eraseP (WNear.Binary.hostOf ctx raw))) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx modelSt (WNear.Call.ftBalanceOf a);
  (∀ (msg : String), r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a) ≤ ctx.gasLimit →
        ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (WNear.Call.ftBalanceOf a)) →
          NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧
            r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (WNear.Call.ftBalanceOf a)) ∧
      (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
        NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

## Bridge.Methods.FtBalanceOfObjectRun

`WNear.Binary.BalanceOf297AbsentCall.objectMethodCost` (hash `8dd75fc17c9add10`)

```lean
def WNear.Binary.BalanceOf297AbsentCall.objectMethodCost (cfg : Wasm.Near.RuntimeConfig) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ) (e : Wasm.NearState) : ℕ :=
  11 * cfg.wasm.regularOpCost +
    WNear.Binary.BalanceOf297AbsentCall.objectBodyCost cfg.wasm e (NearLogic.inputHost e 0) S a bs
      rest N
```

`WNear.Binary.BalanceOf297AbsentCall.object_absent_runs` (hash `0000000051ab84b5`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_absent_runs (cfg : Wasm.Near.RuntimeConfig) (S : WNear.State)
  (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ) (st : Near.TrieOverlay.State) (bud : ℕ)
  (hlen : bs.length < 2 ^ 24) (hnb : 92 ∉ bs) (ho : bs[WNear.Binary.SerdeRead.wsLen bs]? = some 123)
  (hloop :
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account) WNear.IgnoreShallow.ign1R
        N none (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) =
      some (some a, rest))
  (hend : bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) = bs.length) :
  WNear.Binary.MethodRunsR cfg 297 (WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentPre S a bs st bud)
    (WNear.Binary.BalanceOf297AbsentCall.objectMethodCost cfg S a bs rest N)
    (WNear.Binary.BalanceOf297AbsentCall.copiedMethodPost a st)
```

`WNear.Binary.BalanceOf297AbsentCall.object_body_cost_erase` (hash `00000000e25dc1fc`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.object_body_cost_erase (cfg : Wasm.Near.WasmConfig) (e : Wasm.NearState)
  (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : ℕ) :
  WNear.Binary.BalanceOf297AbsentCall.objectBodyCost cfg (NearLogic.erase e) (NearLogic.inputHost (NearLogic.erase e) 0)
      S a bs rest N =
    WNear.Binary.BalanceOf297AbsentCall.objectBodyCost cfg e (NearLogic.inputHost e 0) S a bs rest N
```

## Bridge.Methods.FtBalanceOfParserGas

`WNear.Binary.BalanceOf297AbsentCall.account_encoded_le769` (hash `0000000037450236`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.account_encoded_le769 (bs : List UInt8) (a : WNear.AccountId) (q : ℕ)
  (rest : List UInt8) (hmodel : NearInterface.Json.stringBody (List.drop q bs) [] = some (some ↑a, rest)) :
  (List.drop q bs).length - rest.length ≤ 769
```

`WNear.Binary.BalanceOf297AbsentCall.alloc32_cost_le` (hash `00000000df048b8d`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.alloc32_cost_le (cfg : Wasm.Near.WasmConfig) (F P : ℕ) (size : UInt32) (hF : F ≤ 32)
  (hp : (WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf size) 1).toNat ≤ P) :
  WNear.Binary.VecWithCap.costAllocF cfg F size ≤
    11210 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * P
```

`WNear.Binary.BalanceOf297AbsentCall.alloc_walk32_cost_le` (hash `0000000005cde85e`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.alloc_walk32_cost_le (cfg : Wasm.Near.WasmConfig) (F P : ℕ) (size : UInt32)
  (hF : F ≤ 32) (hp : (WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf size) 1).toNat ≤ P) :
  WNear.Binary.AllocWalk.cost310W cfg F size 1 ≤
    11210 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * P
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_linear_work` (hash `00000000f6d57736`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_linear_work (cfg : Wasm.Near.WasmConfig) (bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  1300 +
          96 *
            (WNear.Binary.SerdeRead.wsLen bs +
                WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) +
              WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)) +
        (910 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop j bs) +
          470 * ((List.drop (j + 1) bs).length - rest.length)) +
      (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) ≤
    2910 + 470 * bs.length
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_parser_cost_le` (hash `00000000ef4682fe`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_parser_cost_le (cfg : Wasm.Near.WasmConfig) (bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * cfg.regularOpCost +
      WNear.Binary.SerdeStruct78Esc.costArray cfg 1 0 bs (↑a).toUTF8.toList rest j ≤
    (300400 + WNear.Binary.AccountIdValid.cost554 (↑a).toUTF8.toList.length + 96 * bs.length) * cfg.regularOpCost +
        WNear.Binary.ParseStrSuccess.growthBudget cfg 1
          (WNear.Binary.ScratchGrow.growthCount 0 0
            (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []))
          (↑a).toUTF8.toList.length +
      WNear.Binary.SerdeString.cost618 cfg
        (WNear.Binary.ScratchGrow.endFreeBound 1 0 0
          (WNear.Binary.ParseStrSuccess.appendChunks (List.drop (j + 1) bs) []))
        (UInt32.ofNat (↑a).toUTF8.toList.length)
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_parser_cost_le300b` (hash `0000000005e6e972`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_parser_cost_le300b (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (bs : List UInt8) (a : WNear.AccountId) (rest : List UInt8)
  (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) * p.wasm.regularOpCost +
      WNear.Binary.SerdeStruct78Esc.costArray p.wasm 1 0 bs (↑a).toUTF8.toList rest j ≤
    300 * 10 ^ 9 + 80 * 10 ^ 6 * bs.length
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_partition` (hash `00000000227106a4`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_partition (cfg : Wasm.Near.WasmConfig) (bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  WNear.Binary.SerdeRead.wsLen bs + WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) +
            WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) +
          WNear.Binary.SerdeRead.wsLen (List.drop k bs) +
        ((List.drop (j + 1) bs).length - rest.length) +
      3 =
    bs.length
```

`WNear.Binary.BalanceOf297AbsentCall.copied_array_short_work` (hash `000000000127168b`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_array_short_work (cfg : Wasm.Near.WasmConfig) (bs : List UInt8)
  (a : WNear.AccountId) (rest : List UInt8) (j k : ℕ) (hlen : bs.length < 2 ^ 24)
  (hj :
    j =
      WNear.Binary.SerdeRead.wsLen bs + 1 +
        WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs))
  (hq : bs[j]? = some 34)
  (hk : k = bs.length - rest.length + WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs) + 1)
  (hend : k + WNear.Binary.SerdeRead.wsLen (List.drop k bs) = bs.length)
  (hmodel : NearInterface.Json.stringBody (List.drop (j + 1) bs) [] = some (some ↑a, rest)) :
  1300 +
          96 *
            (WNear.Binary.SerdeRead.wsLen bs +
                WNear.Binary.SerdeRead.wsLen (List.drop (WNear.Binary.SerdeRead.wsLen bs + 1) bs) +
              WNear.Binary.SerdeRead.wsLen (List.drop (bs.length - rest.length) bs)) +
        (910 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop j bs) +
          470 * ((List.drop (j + 1) bs).length - rest.length)) +
      (700 + 96 * WNear.Binary.SerdeRead.wsLen (List.drop k bs)) ≤
    300000 + 96 * bs.length
```

`WNear.Binary.BalanceOf297AbsentCall.copied_growth_count_le5` (hash `00000000ff2144dc`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_growth_count_le5 (bs : List UInt8) (a : WNear.AccountId) (q : ℕ)
  (rest : List UInt8) (hmodel : NearInterface.Json.stringBody (List.drop q bs) [] = some (some ↑a, rest))
  (hlen : bs.length < 2 ^ 24) :
  WNear.Binary.ScratchGrow.growthCount 0 0 (WNear.Binary.ParseStrSuccess.appendChunks (List.drop q bs) []) ≤ 5
```

`WNear.Binary.BalanceOf297AbsentCall.copied_parser_free_le12` (hash `00000000464e3804`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.copied_parser_free_le12 (bs : List UInt8) (a : WNear.AccountId) (q : ℕ)
  (rest : List UInt8) (hmodel : NearInterface.Json.stringBody (List.drop q bs) [] = some (some ↑a, rest))
  (hlen : bs.length < 2 ^ 24) : WNear.Binary.BalanceOf297AbsentCall.copiedParserFree bs q 1 ≤ 12
```

`WNear.Binary.BalanceOf297AbsentCall.escape_consumed_le12` (hash `000000009f532e16`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.escape_consumed_le12 (l out : List UInt8) (m : ℕ)
  (he : WNear.Binary.ParseEscape.escDecode l = some (out, m)) : m + 1 ≤ 12 * out.length
```

`WNear.Binary.BalanceOf297AbsentCall.owned_short_cost_le11b` (hash `0000000054f10a59`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.owned_short_cost_le11b (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (F : ℕ) (size : UInt32) (hF : F ≤ 32) (hs : size.toNat ≤ 64) :
  WNear.Binary.SerdeString.cost618 p.wasm F size ≤ 11 * 10 ^ 9
```

`WNear.Binary.BalanceOf297AbsentCall.short_growth_budget_le17b` (hash `0000000043d76957`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.short_growth_budget_le17b (p : Wasm.Near.RuntimeConfig)
  (hc : WNear.Binary.FtTotalSupplyMethod.CostsV86 p) (G N : ℕ) (hg : G ≤ 5) (hn : N ≤ 64) :
  WNear.Binary.ParseStrSuccess.growthBudget p.wasm 1 G N ≤ 17 * 10 ^ 9
```

`WNear.Binary.BalanceOf297AbsentCall.strRun_encoded_le12` (hash `0000000048fe7e43`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.strRun_encoded_le12 (l acc bytes rest : List UInt8)
  (h : WNear.Binary.ParseStr.strRun l acc = WNear.Binary.ParseStr.StrOut.ok bytes rest) :
  l.length - rest.length ≤ 12 * (bytes.length - acc.length) + 1
```

`WNear.Binary.BalanceOf297AbsentCall.unicode_consumed_le10` (hash `000000000ba4f1ca`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.unicode_consumed_le10 (l r : List UInt8) (c : Char)
  (h : NearInterface.Json.unicodeEscape l = some (c, r)) : l.length - r.length ≤ 10
```

`WNear.Binary.BalanceOf297AbsentCall.wsLen_quote` (hash `00000000b0a51967`)

```lean
theorem WNear.Binary.BalanceOf297AbsentCall.wsLen_quote (bs : List UInt8) (j : ℕ) (hq : bs[j]? = some 34) :
  WNear.Binary.SerdeRead.wsLen (List.drop j bs) = 0
```

## Bridge.Methods.Statics297

`WNear.Binary.InitialState.frame297` (hash `637e958867d03070`)

```lean
def WNear.Binary.InitialState.frame297 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] (n : ℕ) :
  Iris.IProp GF :=
  fun n =>
    iprop(WNear.Binary.VecFromElem.stk n 1047824 592 ∗
        n ↦[wms][ 1048416 ] List.replicate 8 0 ∗
          n ↦[wms][ 1048424 ] List.replicate 16 0 ∗
            n ↦[wms][ 1048440 ] List.replicate 8 0 ∗
              n ↦[wms][ 1048448 ] List.replicate 8 0 ∗
                n ↦[wms][ 1048456 ] WasmLogic.bytes32 0 ∗
                  n ↦[wms][ 1048464 ] List.replicate 12 0 ∗
                    n ↦[wms][ 1048476 ] List.replicate 28 0 ∗
                      n ↦[wms][ 1048504 ] List.replicate 12 0 ∗
                        n ↦[wms][ 1048516 ] List.replicate 4 0 ∗
                          n ↦[wms][ 1048520 ] List.replicate 24 0 ∗
                            n ↦[wms][ 1048544 ] List.replicate 8 0 ∗
                              n ↦[wms][ 1048552 ] WasmLogic.bytes32 0 ∗
                                n ↦[wms][ 1048556 ] List.replicate 4 0 ∗
                                  n ↦[wms][ 1048560 ] List.replicate 12 0 ∗ True)
```

`WNear.Binary.InitialState.frame297_of` (hash `00000000184dc454`)

```lean
theorem WNear.Binary.InitialState.frame297_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  {m : Wasm.Memory} {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (n : ℕ) :
  WNear.Binary.InitialState.memR m n 1047824 752 ⊢ WNear.Binary.InitialState.frame297 n
```

`WNear.Binary.InitialState.memRes297` (hash `00000000a177d87e`)

```lean
theorem WNear.Binary.InitialState.memRes297 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] {m : Wasm.Memory}
  {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (n : ℕ) :
  WNear.Binary.InitialState.memR m n 0 L ⊢
    WNear.Binary.InitialState.frame297 n ∗
      n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
        n ↦[wms][ 1050188 + 12 ] WNear.Binary.Interface.dataWord (1050188 + 12) ∗
          n ↦[wms][ 1050188 + 16 ] WNear.Binary.Interface.dataWord (1050188 + 16) ∗
            n ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
              n ↦[wms][ 1050188 + 92 ] WNear.Binary.Interface.dataWord (1050188 + 92) ∗
                n ↦[wms][ 1050188 + 100 ] WNear.Binary.Interface.dataWord (1050188 + 100) ∗
                  n ↦[wms][ 1050188 + 188 ] WNear.Binary.Interface.dataWord (1050188 + 188) ∗
                    n ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit ∗
                      n ↦[wms][ 1051817 ] [34] ∗
                        (n ↦[wms][ 1051836 ] WasmLogic.bytes32 1051836 ∗ n ↦[wms][ 1051836 + 4 ] WasmLogic.bytes32 0) ∗
                          n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                            n ↦[wms][ 1057480 ] WasmLogic.bytes32 123 ∗
                              n ↦[wms][ 1061856 ] WNear.Binary.SerializeStr.esc ∗
                                n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                  n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                    n ↦[wms][ 1065416 ] WasmLogic.bytes32 157 ∗
                                      n ↦[wms][ 1070974 ] WNear.Binary.FmtDigits.lut ∗
                                        n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                          n ↦[wms][ 1074896 ] WasmLogic.bytes32 0 ∗
                                            (n ↦[wms][ 1074900 ] WasmLogic.bytes32 0 ∗
                                                n ↦[wms][ 1074900 + 4 ] WasmLogic.bytes32 0 ∗
                                                  n ↦[wms][ 1074900 + 8 ] WasmLogic.bytes32 0 ∗
                                                    n ↦[wms][ 1074900 + 12 ] WasmLogic.bytes32 0) ∗
                                              (n ↦[wms][ 1074920 ] WasmLogic.bytes32 0 ∗
                                                  n ↦[wms][ 1074920 + 4 ] WasmLogic.bytes32 0 ∗
                                                    n ↦[wms][ 1074920 + 8 ] WasmLogic.bytes32 0 ∗
                                                      n ↦[wms][ 1074920 + 12 ] WasmLogic.bytes32 0) ∗
                                                True
```

`WNear.Binary.InitialState.seg_v36` (hash `0000000006270f35`)

```lean
theorem WNear.Binary.InitialState.seg_v36 :
  WNear.Binary.InitialState.seg 1050224 4 = WNear.Binary.Interface.dataWord (1050188 + 36)
```

`WNear.Binary.InitialState.startRes297` (hash `00000000c66b6d1a`)

```lean
theorem WNear.Binary.InitialState.startRes297 {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  WasmLogic.ownCells (NearLogic.mheapOf { store := WNear.Binary.wStore cfg h }) ⊢
    |==>
      (WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
        0 ↪[inst] WNear.Binary.wInst ∗
          0 ↦[wg] WNear.Binary.InitialState.g0 ∗
            NearLogic.mhostPt h ∗
              NearLogic.gasPt h.gas h.gasProfile h.actionProfile ∗
                WNear.Binary.InitialState.frame297 0 ∗
                  WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
                    (WNear.Binary.PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit) ∗
                      0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                        0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                          0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                            0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                              0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable)
```

`WNear.Binary.InitialState.startRes297_gen` (hash `0000000068ef457d`)

```lean
theorem WNear.Binary.InitialState.startRes297_gen {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  {m : Wasm.Memory} {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (cfg : Wasm.Near.RuntimeConfig)
  (h : Wasm.NearState) :
  (WasmLogic.Loc.inst 0 ↦ₛ{Iris.DFrac.own 1} WasmLogic.Cell.inst WNear.Binary.wInst ∗
        WasmLogic.Loc.memLimit 0 ↦ₛ{Iris.DFrac.own 1} WasmLogic.Cell.memLimit (some 2048) ∗
          0 ↦[wmlength] WNear.Binary.InitialState.memLen ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗ NearLogic.gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ WNear.Binary.InitialState.tabCells, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
        ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
          WNear.Binary.InitialState.memR m 0 0 L ⊢
    |==>
      (WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
        0 ↪[inst] WNear.Binary.wInst ∗
          0 ↦[wg] WNear.Binary.InitialState.g0 ∗
            NearLogic.mhostPt h ∗
              NearLogic.gasPt h.gas h.gasProfile h.actionProfile ∗
                WNear.Binary.InitialState.frame297 0 ∗
                  WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
                    (WNear.Binary.PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit) ∗
                      0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                        0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                          0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                            0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                              0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable)
```

`WNear.Binary.InitialState.statics297P` (hash `0000000052d5ac99`)

```lean
theorem WNear.Binary.InitialState.statics297P {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  {m : Wasm.Memory} {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (n ta len : ℕ) (hl1 : len % 65536 = 0)
  (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
  WNear.Binary.InitialState.memR m n 0 L ∗
      n ↦[wmlength] len ∗
        n ↪[wmlimit] some 2048 ∗ WNear.Binary.InitialState.tableRes ta ∗ ta ↦[wt][ 44 ] Wasm.Ref.func 246 ⊢
    WNear.Binary.InitialState.frame297 n ∗
      WNear.Binary.FtTotalSupply.statics n ta id 0 0 123 1051836 2048 len ∗
        (WNear.Binary.PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit) ∗
          n ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
            ta ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
              n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                  n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable
```

`WNear.Binary.InitialState.table297Of` (hash `000000005ac28f60`)

```lean
theorem WNear.Binary.InitialState.table297Of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF] :
  ([∗list] p ∈ WNear.Binary.InitialState.tabCells, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ⊢
    WNear.Binary.InitialState.tableRes 0 ∗ 0 ↦[wt][ 44 ] Wasm.Ref.func 246
```

## Bridge.Methods.Statics297Object

`WNear.Binary.InitialState.ignored_code_of` (hash `00000000bb2f2019`)

```lean
theorem WNear.Binary.InitialState.ignored_code_of {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.discard} p.2) ∗
      0 ↪[inst] WNear.Binary.wInst ⊢
    WNear.Binary.SerdeIgnValue.code81 0 WNear.Binary.wInst id
```

`WNear.Binary.InitialState.memRes297Obj` (hash `0000000093cdf94b`)

```lean
theorem WNear.Binary.InitialState.memRes297Obj {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  {m : Wasm.Memory} {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (n : ℕ) :
  WNear.Binary.InitialState.memR m n 0 L ⊢
    WNear.Binary.InitialState.frame297 n ∗
      n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes ∗
        n ↦[wms][ 1049788 ] WNear.Binary.StateRead.stateKey ∗
          n ↦[wms][ 1050188 + 12 ] WNear.Binary.Interface.dataWord (1050188 + 12) ∗
            n ↦[wms][ 1050188 + 16 ] WNear.Binary.Interface.dataWord (1050188 + 16) ∗
              n ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                n ↦[wms][ 1050188 + 92 ] WNear.Binary.Interface.dataWord (1050188 + 92) ∗
                  n ↦[wms][ 1050188 + 100 ] WNear.Binary.Interface.dataWord (1050188 + 100) ∗
                    n ↦[wms][ 1050188 + 188 ] WNear.Binary.Interface.dataWord (1050188 + 188) ∗
                      n ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit ∗
                        n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                          n ↦[wms][ 1051817 ] [34] ∗
                            (n ↦[wms][ 1051836 ] WasmLogic.bytes32 1051836 ∗
                                n ↦[wms][ 1051836 + 4 ] WasmLogic.bytes32 0) ∗
                              n ↦[wms][ 1055020 ] WasmLogic.bytes32 116 ∗
                                n ↦[wms][ 1057480 ] WasmLogic.bytes32 123 ∗
                                  n ↦[wms][ 1061856 ] WNear.Binary.SerializeStr.esc ∗
                                    n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                                      n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                        n ↦[wms][ 1065416 ] WasmLogic.bytes32 157 ∗
                                          n ↦[wms][ 1070974 ] WNear.Binary.FmtDigits.lut ∗
                                            n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                              n ↦[wms][ 1074896 ] WasmLogic.bytes32 0 ∗
                                                (n ↦[wms][ 1074900 ] WasmLogic.bytes32 0 ∗
                                                    n ↦[wms][ 1074900 + 4 ] WasmLogic.bytes32 0 ∗
                                                      n ↦[wms][ 1074900 + 8 ] WasmLogic.bytes32 0 ∗
                                                        n ↦[wms][ 1074900 + 12 ] WasmLogic.bytes32 0) ∗
                                                  (n ↦[wms][ 1074920 ] WasmLogic.bytes32 0 ∗
                                                      n ↦[wms][ 1074920 + 4 ] WasmLogic.bytes32 0 ∗
                                                        n ↦[wms][ 1074920 + 8 ] WasmLogic.bytes32 0 ∗
                                                          n ↦[wms][ 1074920 + 12 ] WasmLogic.bytes32 0) ∗
                                                    True
```

`WNear.Binary.InitialState.seg_ident` (hash `000000005e950939`)

```lean
theorem WNear.Binary.InitialState.seg_ident : WNear.Binary.InitialState.seg 1048576 10 = WNear.Binary.SerdeIdent.identBytes
```

`WNear.Binary.InitialState.startRes297Obj` (hash `00000000fa579627`)

```lean
theorem WNear.Binary.InitialState.startRes297Obj {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  (cfg : Wasm.Near.RuntimeConfig) (h : Wasm.NearState) :
  WasmLogic.ownCells (NearLogic.mheapOf { store := WNear.Binary.wStore cfg h }) ⊢
    |==>
      (WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
        WNear.Binary.SerdeIgnValue.code81 0 WNear.Binary.wInst id ∗
          0 ↪[inst] WNear.Binary.wInst ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗
                NearLogic.gasPt h.gas h.gasProfile h.actionProfile ∗
                  WNear.Binary.InitialState.frame297 0 ∗
                    WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
                      (WNear.Binary.PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit) ∗
                        0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                          0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                            0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                              0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                  0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                                    0 ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes)
```

`WNear.Binary.InitialState.startRes297Obj_gen` (hash `000000005dbd8c88`)

```lean
theorem WNear.Binary.InitialState.startRes297Obj_gen {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  {m : Wasm.Memory} {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (cfg : Wasm.Near.RuntimeConfig)
  (h : Wasm.NearState) :
  (WasmLogic.Loc.inst 0 ↦ₛ{Iris.DFrac.own 1} WasmLogic.Cell.inst WNear.Binary.wInst ∗
        WasmLogic.Loc.memLimit 0 ↦ₛ{Iris.DFrac.own 1} WasmLogic.Cell.memLimit (some 2048) ∗
          0 ↦[wmlength] WNear.Binary.InitialState.memLen ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗ NearLogic.gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ WNear.Binary.InitialState.tabCells, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
        ([∗list] p ∈ WNear.Binary.InitialState.funcCells cfg h, p.1 ↦ₛ{Iris.DFrac.own 1} p.2) ∗
          WNear.Binary.InitialState.memR m 0 0 L ⊢
    |==>
      (WNear.Binary.BalanceOf297AbsentCall.code297 cfg.fees.numExtraBytesRecord 0 WNear.Binary.wInst id 0 (some 2048) ∗
        WNear.Binary.SerdeIgnValue.code81 0 WNear.Binary.wInst id ∗
          0 ↪[inst] WNear.Binary.wInst ∗
            0 ↦[wg] WNear.Binary.InitialState.g0 ∗
              NearLogic.mhostPt h ∗
                NearLogic.gasPt h.gas h.gasProfile h.actionProfile ∗
                  WNear.Binary.InitialState.frame297 0 ∗
                    WNear.Binary.FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 WNear.Binary.InitialState.memLen ∗
                      (WNear.Binary.PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit) ∗
                        0 ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
                          0 ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
                            0 ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                              0 ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                                0 ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                                  0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                                    0 ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes)
```

`WNear.Binary.InitialState.statics297PObj` (hash `0000000074f1595b`)

```lean
theorem WNear.Binary.InitialState.statics297PObj {GF : Iris.BundledGFunctors} [WasmLogic.WasmGS Wasm.NearState GF]
  {m : Wasm.Memory} {L : ℕ} (hm : WNear.Binary.InitialState.MemImage m L) (n ta len : ℕ) (hl1 : len % 65536 = 0)
  (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
  WNear.Binary.InitialState.memR m n 0 L ∗
      n ↦[wmlength] len ∗
        n ↪[wmlimit] some 2048 ∗ WNear.Binary.InitialState.tableRes ta ∗ ta ↦[wt][ 44 ] Wasm.Ref.func 246 ⊢
    WNear.Binary.InitialState.frame297 n ∗
      WNear.Binary.FtTotalSupply.statics n ta id 0 0 123 1051836 2048 len ∗
        (WNear.Binary.PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] WNear.Binary.PanicStr.notInit) ∗
          n ↦[wms][ 1050188 + 36 ] WNear.Binary.Interface.dataWord (1050188 + 36) ∗
            ta ↦[wt][ 44 ] Wasm.Ref.func 246 ∗
              n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗
                n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
                  n ↦[wms][ 1062712 ] WNear.Binary.SerdeEsc.hexTable ∗
                    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
                      n ↦[wms][ 1048576 ] WNear.Binary.SerdeIdent.identBytes
```

## NearInterface.Boundary

`NearInterface.Context.WF` (hash `3c54348dc29aaf11`)

```lean
inductive NearInterface.Context.WF (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) : Prop
| NearInterface.Context.WF.mk {ctx : NearInterface.Context} {raw : NearInterface.RawStorage}
  (balance_lt : ctx.balance + ctx.attached < 2 ^ 128) (locked_lt : ctx.locked < 2 ^ 128)
  (arguments_length : List.length ctx.args ≤ ctx.protocol.wasm.limits.maxArgumentsLength)
  (prepaidGas_lt : ctx.prepaidGas < 2 ^ 64) (blockHeight_lt : ctx.blockHeight < 2 ^ 64)
  (timestamp_lt : ctx.timestamp < 2 ^ 64) (epochHeight_lt : ctx.epochHeight < 2 ^ 64)
  (usage_ge : NearInterface.storageUsageOf ctx.protocol raw ≤ ctx.storageUsage)
  (usage_room : ctx.storageUsage + ctx.protocol.wasm.limits.maxGasBurnt < 2 ^ 64)
  (opCost_pos : 0 < ctx.protocol.wasm.regularOpCost ∧ 0 < ctx.protocol.wasm.linearOpBaseCost)
  (trie_canonical : Near.TrieConstruction.build ctx.trie.entries = Except.ok ctx.trie.base)
  (trie_storage : NearInterface.contractData ctx.trie ctx.current.bytes = raw)
  (trie_no_zero_hash : List.replicate 32 0 ∉ List.map Prod.fst ctx.trie.base.witness)
  (prospective_unique : (List.map Prod.fst ctx.trie.prospective).Nodup)
  (committed_unique : (List.map Prod.fst ctx.trie.committed).Nodup)
  (raw_keys_unique : ∀ (k v v' : Wasm.Near.Bytes), (k, v) ∈ raw → (k, v') ∈ raw → v = v')
  (proof_growth :
    ∀ (size : Near.TrieOverlay.State → ℕ),
      ctx.storageProofSize = some size →
        ∀ (t : Near.TrieOverlay.State) (c : ℕ), Near.TrieOverlay.ProofReach ctx.trie t c → size t ≤ size ctx.trie + c) :
  ctx.WF raw
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

## NearRuntime.ActionValidation

`Near.validateActionOrder_member` (hash `0000000061746082`)

```lean
theorem Near.validateActionOrder_member (limits : Wasm.Near.LimitConfig) (actions : List Near.Action) (found : Bool)
  (h : Near.validateActionOrder limits found actions = Except.ok ()) (action : Near.Action) (hmem : action ∈ actions) :
  Near.validateAction limits action = Except.ok ()
```

`Near.validateAction_functionCall_arguments` (hash `000000005b2a33be`)

```lean
theorem Near.validateAction_functionCall_arguments (limits : Wasm.Near.LimitConfig) (method : String) (args : List UInt8)
  (gas deposit : ℕ) (h : Near.validateAction limits (Near.Action.functionCall method args gas deposit) = Except.ok ()) :
  args.length ≤ limits.maxArgumentsLength
```

`Near.validateAction_functionCall_ok_iff` (hash `000000002c8f68f7`)

```lean
theorem Near.validateAction_functionCall_ok_iff (limits : Wasm.Near.LimitConfig) (method : String) (args : List UInt8)
  (gas deposit : ℕ) :
  Near.validateAction limits (Near.Action.functionCall method args gas deposit) = Except.ok () ↔
    gas ≠ 0 ∧ method.utf8ByteSize ≤ limits.maxLengthMethodName ∧ args.length ≤ limits.maxArgumentsLength
```

`Near.validateActions_functionCall_arguments` (hash `0000000065ac4ce6`)

```lean
theorem Near.validateActions_functionCall_arguments (limits : Wasm.Near.LimitConfig) (actions : List Near.Action)
  (method : String) (args : List UInt8) (gas deposit : ℕ) (h : Near.validateActions limits actions = Except.ok ())
  (hmem : Near.Action.functionCall method args gas deposit ∈ actions) : args.length ≤ limits.maxArgumentsLength
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

`WNear.ftBalanceOf_other_accepted_obligation` (hash `000000005366c771`)

```lean
theorem WNear.ftBalanceOf_other_accepted_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of") (c : WNear.Call)
  (hparse : (WNear.wnear cfg).Parses ctx.method ctx.args c)
  (hother : ¬WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.ftBalanceOf_other_no_issue_obligation` (hash `00000000a2782db8`)

```lean
theorem WNear.ftBalanceOf_other_no_issue_obligation (cfg : WNear.Config) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hother : ¬∃ c, WNear.Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
```

`WNear.ftBalanceOf_outside_array_absent_accepted_obligation` (hash `0000000099132b93`)

```lean
theorem WNear.ftBalanceOf_outside_array_absent_accepted_obligation (cfg : WNear.Config)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of") (c : WNear.Call)
  (hparse : (WNear.wnear cfg).Parses ctx.method ctx.args c)
  (hother : ¬WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.ftBalanceOf_outside_array_absent_no_issue_obligation` (hash `00000000663ea2d0`)

```lean
theorem WNear.ftBalanceOf_outside_array_absent_no_issue_obligation (cfg : WNear.Config)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hother : ¬∃ c, WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c) (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
```

`WNear.ftBalanceOf_outside_array_object_absent_accepted_obligation` (hash `00000000bdfc9a1e`)

```lean
theorem WNear.ftBalanceOf_outside_array_object_absent_accepted_obligation (cfg : WNear.Config)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of") (c : WNear.Call)
  (hparse : (WNear.wnear cfg).Parses ctx.method ctx.args c)
  (hother : ¬WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c)
  (hobject : ¬WNear.Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c) :
  have r := Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx;
  have res := (WNear.wnear cfg).step ctx st c;
  ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
        NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (NearInterface.Matches (WNear.wnear cfg) ctx raw r res ∨
      NearInterface.ResourceFailure r ∧ NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)
```

`WNear.ftBalanceOf_outside_array_object_absent_no_issue_obligation` (hash `0000000029270d65`)

```lean
theorem WNear.ftBalanceOf_outside_array_object_absent_no_issue_obligation (cfg : WNear.Config)
  (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol)
  (he : WNear.Binary.Exported.Environment protocol) (hcfg : cfg.WF) (raw : WNear.RawStorage) (st : Option WNear.State)
  (ctx : NearInterface.Context) (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
  (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
  (hother : ¬∃ c, WNear.Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c)
  (hobject : ¬∃ c, WNear.Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c) (msg : String) :
  (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode WNear.Binary.wNearBytes.size codeOf) raw ctx).outcome ≠
    Except.error (NearInterface.Failure.executionIssue msg)
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

`WNear.refines_wnear_of_clauses` (hash `00000000059f2cae`)

```lean
theorem WNear.refines_wnear_of_clauses (cfg : WNear.Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hcfg : cfg.WF)
  (hcode : Wasm.Binary.decode WNear.Binary.wNearBytes = Except.ok code)
  (hc : WNear.Binary.Exported.Clauses cfg WNear.Binary.wNearBytes.size codeOf protocol) :
  NearInterface.Refines Near.Boundary.nearRuntime protocol
    { code := { module := code, size := WNear.Binary.wNearBytes.size, hash := "" }, codeOf := codeOf } (WNear.wnear cfg)
```

`WNear.refines_wnear_with_obligations` (hash `00000000678046d0`)

```lean
theorem WNear.refines_wnear_with_obligations (cfg : WNear.Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hcfg : cfg.WF)
  (hcode : Wasm.Binary.decode WNear.Binary.wNearBytes = Except.ok code)
  (he : WNear.Binary.Exported.Environment protocol)
  (hr : WNear.Binary.Exported.Remaining cfg WNear.Binary.wNearBytes.size codeOf protocol) :
  NearInterface.Refines Near.Boundary.nearRuntime protocol
    { code := { module := code, size := WNear.Binary.wNearBytes.size, hash := "" }, codeOf := codeOf } (WNear.wnear cfg)
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
