# Factory proof index — raw-trie method model

| Statement | Evidence | Status |
|---|---|---|
| Fixed header/code key disjointness | `fixedKeysDisjoint`, `Proofs/Namespaces.lean` | proved |
| Code and DAO membership keys always disjoint | `namespaces_not_disjoint` | false; kernel-checked witness |
| Default setter storage check accepts a DAO index | `dao_index_accepted_as_default` | proved for internal post-authorization operation |
| Code getter can return DAO index bytes | `get_code_can_return_dao_index` | proved for raw getter |
| Raw code deletion can erase DAO membership | `code_deletion_erases_membership_only` | proved for internal deletion |
| Missing membership can cause a duplicate DAO vector entry | `deleted_membership_allows_duplicate_vector_entry` | proved for collection insertion after internal deletion |
| DAO list getter returns physical vector order, including duplicate entries after alias/reinsertion | `Proofs/DaoProjection.lean`, `duplicate_dao_getter` | proved under vector-only layout and explicit account decoding bounds; witness is source-model storage, not a full exported transaction trace |
| Successful callback appends an absent DAO or leaves an existing one unchanged | `Proofs/DaoInsert.lean` | both exported branches proved; absent branch preserves canonical DAO layout and list readback under u64 room, owner-independent private-call context and account decode bounds |
| Code/DAO key alias can make a successful callback return true without registration | `alias_only_callback_true_without_registration` | proved for a constructed source-model raw state; chain reachability not established |
| DAO pagination slices vector records; overflowing u64 addition aborts | `dao_page_matches_layout`, `dao_page_overflow` | proved through exported methods under vector-only layout and decode bounds |
| Code keys disjoint from canonical vector and metadata keys; DAO index overlap requires 26 account bytes | `Proofs/Namespaces.lean` | proved |
| Raw read/write/remove laws and key uniqueness | `Proofs/Trie.lean` | proved |
| All 18 exported methods represented in one shared raw-trie model | `Model/Methods.lean` | modeled; source refinement open |
| Key uniqueness for every successful model method | `step_preserves_wf` | proved |
| Single-use initialization and callback/deposit wrapper guards | `Proofs/Transactions.lean` | proved at model level |
| Failed callback refund and success/abort branch selection | `Proofs/Callbacks.lean` | proved through exported wrapper, conditional on decodable header and set insertion |
| Set/map Borsh header encode/decode round trip | `Proofs/Borsh.lean` | proved under serialized length bounds |
| Metadata Borsh value round trip, including UTF-8 strings and optional changelog | `exact_metadata_encode_bounded` | proved under u32 string lengths |
| Create action order, 40/10 TGas and base receipt return | `create_entry_returns_base_receipt` | proved for qualifying model state and inputs |
| Canonical DAO layout established by new; count reads vector length | `Proofs/Storage.lean` | proved conditionally at model level |
| Ordered metadata layout; missing versus empty header behavior | `Spec/Storage.lean`, `Proofs/Storage.lean` | layout stated, empty case and getter behavior proved |
| Coherent metadata map projects to exported getter's exact vector order | `metadata_getter_matches_layout` | proved under header/string bounds |
| First metadata insertion establishes layout and reads back, with either default flag | `Proofs/MetadataInsert.lean` | proved for empty metadata index namespace and qualifying owner/code state |
| Valid singleton metadata replacement preserves layout and reads back | `store_metadata_replacement_then_get` | proved through exported method for false default flag and bounded values |
| Replacing a malformed old metadata value aborts after a provisional write | `Proofs/MetadataMalformed.lean` | proved through exported method for either default flag; runtime rollback open |
| Second distinct metadata insertion preserves ordered map layout and reads back | `Proofs/MetadataSecondInsert.lean` | proved from canonical singleton layout and absent second index |
| Absent-hash insertion appends at arbitrary bounded map length and reads back | `Proofs/MetadataGeneralInsert.lean` | proved through exported method under u64 room and bounded metadata values |
| Singleton metadata deletion restores empty layout and reads back | `Proofs/MetadataRemove.lean` | proved through exported method with bounded old value |
| Deleting the first entry of a two-entry map swaps the last entry into slot zero | `Proofs/MetadataSwapRemove.lean` | proved through exported method, layout preservation and getter readback |
| Deleting the last entry of a two-entry map leaves slot zero intact | `Proofs/MetadataTailRemove.lean` | proved through exported method, layout preservation and getter readback |
| General vector pop and both swap-removal branches; exported metadata deletion at arbitrary size | `Proofs/MetadataGeneralRemove.lean` | final and nonfinal exported storage effects, canonical layout preservation, and getter readback proved under explicit bounded, coherent-map hypotheses |
| Deleting an absent metadata hash preserves any coherent bounded map | `Proofs/MetadataAbsentDelete.lean` | proved through exported method, layout and getter |
| Replacing an existing value at arbitrary valid index preserves layout and reads back | `Proofs/MetadataGeneralLayout.lean` | proved through exported method for bounded coherent maps |
| Owner-only exported methods reject a different caller before their bodies | `owner_only_rejects_other` | proved under decodable STATE and OWNER |
| Owner update changes getter and revokes the prior predecessor | `Proofs/Admin.lean` | proved through exported methods for a valid replacement AccountId and decodable STATE/OWNER |
| Default setter accepts any present raw hash key and rejects an absent key | `set_default_entry`, `set_default_missing_raw_key`, `set_default_then_getter` | proved through exported method and getter; no Wasm or metadata validation |
| DAO membership index accepted by exported default setter | `exported_default_accepts_dao_index` | proved for constructed STATE and DAO-index storage with owner defaulting to current; chain reachability open |
| Update authority, raw membership/code guards, and weighted receiver receipt | `Proofs/Update.lean` | exported success and three failure branches proved; effective owner decode remains required for DAO-self calls |
| Key alias can pass update checks with an empty DAO vector | `update_alias_without_registered_dao` | constructed source-model raw witness; no reachable-chain or receiver-success claim |
| Store cost saturation and success/underfunded branches | `Proofs/Store.lean` | proved at model level; runtime rollback and global publication open |
| Delete failure after provisional code erase when METADATA is absent | `delete_entry_missing_metadata` | proved at model level; runtime rollback open |
| Complete method invariants and resource bounds | `Model/Methods.lean` | open |
| Storage projection and actual SDK write equivalence | `Model/Borsh.lean`, `Model/Collections.lean` | open |
| Deployed runtime refinement / chain guarantees | concrete adapter not yet present | open |

All proved statements are kernel checked and included in the strict transitive
axiom audit. Passing this package does not mean the factory is verified.
