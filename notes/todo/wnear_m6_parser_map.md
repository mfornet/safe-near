# M6: serde_json's argument parser in `contract.wasm`, mapped

The call graph below `from_trait` (66), the parser of `ft_balance_of`'s arguments
`{ account_id: ValidAccountId }`, read from `contracts/w-near/contract.wasm`
(`wasm-tools print`) and the names in `Binary/functions.tsv`. Sizes are instruction
counts (`block`/`loop`/`end` included). Proof status refers to
`contracts/w-near/verification/Bridge/Functions/`.

**Totals.** 202 functions and 13 922 instructions are reachable from 66 (including the panic
machinery and the allocator). About 45 of them run on the accepting path of the canonical
input `{"account_id":"<a>"}`; most of the rest build or drop `serde_json::Error`.

Across the nine argument parsers (the `from_trait`s 50, 52, 54, 56, 58, 60, 62, 64, 66) and
`ft_resolve_transfer`'s promise-result parser (318), 137 functions (9 550 instructions) are
shared by all of them, and the union is 271 functions (25 926 instructions). Only 69
functions (12 004 instructions) lie outside 66's graph, and most of those are the
per-struct copies of the same generic code: one `deserialize_struct`, one `next_key_seed`
and one field visitor for each struct.

`storage_balance_of`'s parser (52, then 222 and 191) is 66's code instruction for
instruction. It differs only in the callee indices (191 for 193, 192 for 194) and in one
data pointer, the struct's field list used in error messages (1050060 for 1050156). The
proof of 66 transfers to it.

## The input model

Every function below takes the `Deserializer` at `de`, as built by 634
(`ArgsLeaves.deserializer`). Its fields:

* `+0` is the `SliceRead` `(ptr, len, index)`.
* `+12` is the scratch `Vec<u8>` `(ptr, cap, len)`.
* `+24` is `remaining_depth`, a byte that starts at 128.

The reader's state is `SerdeRead.rd n de ptr bs i`: the triple over the input `bs` at
`ptr`, at the position `i ≤ bs.length`. A position-indexed spec says how far `i` moves and
what the function returns, in terms of `bs.drop i`. `NearInterface.Json` reads the same
suffix (`skipWhitespace`, `stringBody`, `value`), so each spec can be matched to one
grammar function.

`Result<Option<u8>>` and `Result<u8>` come back packed in an `i64`:

* bit 0 is the `Err` tag;
* bit 8 is `Some`;
* the byte is at bits 16..23 (`SerdeRead.optByte`), or at bits 8..15 for `peek_or_null`
  (`byteOrNull`).

## Layers

### Entry and exit

| fn | size | role | status |
|---|---|---|---|
| 65 | 13 | `from_slice`: `SliceRead::new` (644), then 66 | proved from any spec of 66 (`ArgsLeaves.f65_of_66`) |
| 66 | 114 | `from_trait`: 634, `deserialize_struct` (78 → 228), `end` (320), drop the scratch (68) | stated (`FromSliceSpec.FromTraitContract`) |
| 634 | 23 | `Deserializer::new` | proved (`f634_spec`) |
| 78 | 7 | `Input::deserialize`, which calls 228 | |
| 320 | 41 | `end`: `parse_whitespace`, then `Some(_)` gives `TrailingCharacters` (322) | |
| 68 | 4 | drop the scratch `Vec<u8>` (747/777/311) | proved (`DropVec`) |

### Reader primitives (`SliceRead`)

| fn | size | role | status |
|---|---|---|---|
| 332 | 26 | `peek` | proved (`SerdeRead.f332_spec`, 24) |
| 333 | 19 | `eat_char` (overflow-checked `index + 1`) | proved (`f333_spec`, 12) |
| 324 | 33 | `next_char` | proved (`f324_spec`, 31) |
| 637 | 33 | `SliceRead::next`, the same body as 324 | proved (`f637_spec`) |
| 329 | 37 | `peek_or_null` | proved (`f329_spec`, 65) |
| 339 | 61 | `parse_whitespace`, a loop over `" \t\n\r"` (mask `0x800013`) | proved (`f339_spec`, `100 + 96·w`) |
| 88 | 37 | `next_char_or_null` (324) | |
| 323 | 92 | `parse_ident`: the rest of `null`, `true` or `false` | |
| 655 | 86 | `next_or_eof` (637, else an `EofWhileParsingString` error) | |

### The struct visitor (`ft_balance_of`)

| fn | size | role |
|---|---|---|
| 228 | 528 | `deserialize_struct`. Steps: `parse_whitespace`; on `{`, decrement the depth (`RecursionLimitExceeded` at 0), then the inlined derived `visit_map` loop; on `[`, the same with `visit_seq`; on anything else, `peek_invalid_type` (340). After the visitor comes `end_map` (90) or `end_seq` (91), then `fix_position` (326) on errors. |
| 193 | 265 | `MapAccess::next_key_seed`: whitespace, then `}` (end), `,` (only after the first key), or `"`. A key is `parse_str` (646) into the scratch, after `Vec::clear` (82), and goes to the field visitor 194. |
| 194 | 8 | `__FieldVisitor::visit_str`: the key equals `account_id` (10 bytes at 1051092, compared by 754 → 755 → `bcmp` 953) to give field 0; otherwise `__ignore`. 953, 755, 754 and 194 are proved (`SerdeKey`). |
| 205 | 19 | `next_value_seed` of the known field: `parse_object_colon` (89), then `ValidAccountId::deserialize` (169) |
| 201 | 12 | `next_value_seed` of an unknown field: 89, then `ignore_value` (81) |
| 214 | 225 | `SeqAccess::next_element_seed` (the array form `["<a>"]`): 169 |
| 89 | 61 | `parse_object_colon` |
| 90 | 75 | `end_map`: `}`, else `TrailingComma`, `TrailingCharacters` or EOF |
| 91 | 132 | `end_seq`: the same for `]` |
| 177 | 11 | a missing `account_id`: `missing_field` (101) |
| 166 | 47 | `duplicate_field` (a second `account_id`) |
| 165 | 66 | `invalid_length` (`[]`) |
| 77 | 8 | drop `Option<ValidAccountId>` (the value read before a later error) |

### Strings

| fn | size | role | status |
|---|---|---|---|
| 646 | 317 | `SliceRead::parse_str`. It scans while `ESCAPE[b] = 0` (the table at 1062392: nonzero exactly for `0x00..0x1F`, `"` and `\`). On `"` with an empty scratch, the result is the borrowed slice (583); with a non-empty scratch, the rest is appended (613). On `\`, the slice so far is appended, then `parse_escape` (649). On a control byte, `ControlCharacterWhileParsingString`. On EOF, `EofWhileParsingString` (647). The result goes through `as_str` (648). | plain case proved (`ParseStr.f646_spec_plain`, ASCII; `ParseStrUtf8.f646_spec_utf8`, any UTF-8 body; no escape, scratch empty; `plain_model`, `utf8_model`) |
| 648 | 39 | `as_str`: `from_utf8` (927), else `InvalidUnicodeCodePoint` (657) | proved on every input: `ParseStrUtf8.f648_spec_valid` (`utf8Ok`), `SerdeErrBox.f648_spec_bad` (not UTF-8: 657) |
| 927 | 443 | `core::str::from_utf8`, with its word-at-a-time ASCII fast path | proved on any input (`FromUtf8Gen.f927_spec`: `Ok` exactly when `Utf8.utf8Ok`, `100 + 100·len`; the width table at 1071704 owned) |
| 649 | 401 | `parse_escape`: the simple escapes are pushed (614); `\u` goes through `decode_hex_escape` (653, 162) and the surrogate pair logic, then `encode_utf8` (605, 109) and an append (613) |
| 650 | 106 | `ignore_str` (ignored values): the same scan, without UTF-8 validation |
| 652 | 267 | `ignore_escape`: validates the escape without decoding it |
| 82, 343 | 3 | `Vec::clear` of the scratch (674 `truncate`) |
| 583 | 33 | `<Range as SliceIndex>::index` (panics 855/864 never reached) | proved (`ParseStr.f583_spec`, 20) |

### The value: `ValidAccountId`

| fn | size | role |
|---|---|---|
| 169 | 106 | `ValidAccountId::deserialize`: `String::deserialize` (379 → 380), then `try_into` (501 → 502). An `Err` is formatted: `to_string` (130), then `Error::custom` (387), then the box is dropped (151). |
| 380 | 177 | `deserialize_str`. Steps: whitespace; on `"`, eat it, clear the scratch (343) and `parse_str` (646), then `StringVisitor::visit_str` (633); on anything else, `peek_invalid_type` (340). |
| 633 | 28 | `visit_str`, then `to_owned` (618): `RawVec::allocate_in` (626, through 624/625/310 to the allocator), then `memcpy` (951) |
| 502 | 72 | `TryFrom<String>`: `is_valid_account_id` (554); on false, a `Box<dyn Error>` from `&str` (693 → 811) and the `String` dropped (479) |
| 554 | 102 | `is_valid_account_id`: the length in 2..=64, `[a-z0-9]` runs separated by single `-`, `_` or `.`, and no separator at either end. Proved, with 673 (`AccountIdValid.f554_spec`). |

### Ignored values

| fn | size | role |
|---|---|---|
| 81 | 498 | `ignore_value`. It is iterative: the open `[` and `{` frames are pushed onto the scratch `Vec` (84 `spec_extend`, which grows through 698/712–716) and popped (85), so the depth is unbounded. It handles the literals (323), numbers (83/86/87), strings (650) and keys (650 + 89). |
| 83 | 168 | `ignore_integer`: one leading `0`, or `[1-9][0-9]*`, then `.` or `e`/`E` |
| 86 | 97 | `ignore_decimal` (at least one digit) |
| 87 | 115 | `ignore_exponent` (an optional sign, at least one digit) |

### Errors

Errors happen only on input the model rejects. `Refines` needs only that they return `Err`
without effects other than heap allocation. Their code is still large, and it has to be
covered for the gas bound and for termination.

| fn | size | role |
|---|---|---|
| 322 / 325 | 42 | `peek_error` / `error`: the position (640 / 638, then `position_of_index` 645, which scans the input from the start to count lines, so it is linear), then `Error::syntax` (639) and a `Box` (590) |
| 340 | 322 | `peek_invalid_type`: describes the unexpected value for the message. For numbers it parses them fully: `parse_integer` (336), 328 `parse_number`, 330 `parse_decimal`, 331 `parse_exponent`, 334/337/338 overflow, 335 `f64_from_parts`, then 635/636 `invalid_type` |
| 642 | 52 | `Error::custom`: `format!` (598 → `core::fmt::write` 872, through indirect calls), then `make_error` (643) |
| 643 | 644 | `make_error`: searches the message for `" at line N column M"` (929 `StrSearcher::new` 718, 606 `next_back` 283, 934 `u32::from_str` 111, 584–587, 857) |
| 327 / 326 | 39 | `Error::fix_position` |
| 92, 341, 342, 143, 356, 151, 348 | | drops of `Error`, `io::Error` and `Box<dyn Error>`, some through indirect calls |
| 101, 166, 165 | | `missing_field`, `duplicate_field`, `invalid_length` (each a `format!` with `ArgumentV1` 597/700/701) |

Proved, with a loose cost as the reject paths need:

* 647/657, `Deserializer::error` (`SerdeErrBox.f647_spec`, `f657_eq`): `Err(box)`, at most
  `costErr cfg F i`;
* 645, 638, 609, the position (`SerdePosition`);
* 639, `Error::syntax`, the 20-byte box (`SerdeErrBox`).

Not proved yet: 322/325 (`peek_error` / `error`, which reach 639 through 640), 340, 642/643 and the
drops.

### Shared infrastructure

Already proved:

* the allocator: wee_alloc 568–582 and 236–239, 310–314 (`AllocWalkHeap.f310_spec_walk`,
  `AllocDealloc`);
* `memcpy` 951 and `memset` 952;
* the `Vec<u8>` drops 68/747/777.

Not yet proved:

* the `RawVec`/`Vec` growth used by the scratch: 588, 589, 613, 614, 620–632, 698, 712–716
  (`VecWithCap` covers 623/630/631 on the serializer side);
* `Layout` 607/608;
* `exchange_malloc` 590 and 624/625 are proved at alignment 4 for the error box
  (`SerdeErrBox.f590_spec`, through `AllocWalk.f310_spec_walk`), but not for the scratch `Vec`.

The panic paths are never reached on any input: 852, 853, 855, 857, 859, 864, 881, the
panic machinery 816–832, and the out-of-memory handling 842–844/821. They appear only behind
arithmetic and bounds checks.

## Which pieces serve the other methods' arguments

| piece | used by |
|---|---|
| reader primitives, `parse_str`/`as_str`/`from_utf8`, escapes, `ignore_value` and its number/string skippers, `parse_object_colon`, `end_map`/`end_seq`/`end`, the error constructors | every argument parser, and `ft_resolve_transfer`'s promise-result parser (318) for the reader, `parse_str` and the errors |
| `deserialize_str` (380) + `visit_str` (633) | every `String`-carrying field: `ValidAccountId`, `U128`, and `memo`/`msg` (`Option<String>` / `String`) |
| `ValidAccountId` (169/177/501/502/554) | `ft_balance_of`, `storage_balance_of` (`account_id`), `ft_transfer`/`ft_transfer_call` (`receiver_id`), `ft_resolve_transfer` (`sender_id`, `receiver_id`), `storage_deposit` (`Option<ValidAccountId>`, through the `Option` impls 168–172) |
| `U128` (178, the string, then `u128::from_str_radix` 871/933 with `__multi3` 954; 319 for the promise result) | `near_withdraw`, `ft_transfer(_call)`, `ft_resolve_transfer`, `storage_withdraw` (`Option`) |
| `bool` (167 `deserialize_bool`, then `parse_ident` 323) | `storage_deposit` (`registration_only`), `storage_unregister` (`force`), both `Option<bool>` |
| `Option<T>` (168/170/171/172: `null` through `parse_ident`, otherwise `T`) | `storage_deposit`, `storage_withdraw`, `storage_unregister`, `ft_transfer(_call)` (`memo`) |
| `deserialize_struct` / `next_key_seed` / the field visitor / `next_element_seed` | one copy per struct (221–229, 183–199, 209–215). Each is the same generic code instantiated with the struct's field names, and 222/191 equal 228/193. |

## Model against serde_json 1.0.60: checked, no disagreement found

We read the binary's control flow, checked it against serde_json 1.0.60's source, and
compared both with `NearInterface.Json.parse` and `structFields` / `required account`. The
two accept the same inputs:

* **Whitespace.** Only `' ' '\t' '\n' '\r'` (339's mask `0x800013` over `b - 9`); a BOM is
  rejected in both.
* **Top level.** Only `{` or `[` (228; anything else is `invalid_type`). After the value,
  only whitespace (`end`, 320). The model reads any value, then `structFields` rejects
  anything that is not an object or an array.
* **Object form.** Behaviour on each kind of key:
  * Keys must be strings (`KeyMustBeAString`).
  * Keys are decoded with escapes and validated as UTF-8 (`parse_str` → `as_str`); the
    model requires `ms.all (·.1.isSome)`.
  * A second `account_id` is `duplicate_field`, and the model counts `≤ 1`.
  * Unknown keys go to `ignore_value`, and the model ignores them.
  * A missing `account_id` is `missing_field`, and the model's `required` is `none`.
  * A trailing comma is an error in `next_key_seed`, `end_map` and `ignore_value`; the
    model's `members` needs a `"` after a `,`.
* **Array form.** Exactly one element, through `next_element_seed`, then `end_seq` (an
  extra element is an error); the model needs `vs.length == names.length`.
* **Strings.** Control bytes `< 0x20` are rejected (the `ESCAPE` table, dumped from the data
  segment, is nonzero exactly at `0x00–0x1F`, `"` and `\`). The escapes are
  `\" \\ \/ \b \f \n \r \t \uXXXX`. A lone or reversed surrogate is rejected, in both
  `parse_escape` and `ignore_escape` (serde_json 1.0.60 predates the lenient handling of
  lone surrogates). The UTF-8 check covers the whole decoded string, in typed fields and
  keys only. Ignored strings are only scanned, as the model's `invalidStr` and `none` keys
  allow.
* **Numbers in ignored values.** The syntax is the same (one leading zero; `.` and `e`
  need at least one digit). Where serde fails early (`01`), the model fails one step
  later, when the container sees the next byte. The outcome is the same.
* **Depth.** The model has no limit. In the binary, the struct itself takes one level
  (128 → 127), its field values are strings, and `ignore_value` is iterative with its
  frames on the heap, so no input reaches `RecursionLimitExceeded`. The heap the frame
  stack needs is one byte per open bracket, which the parser's heap-room premise must
  cover.
* **`ValidAccountId`.** The `String` comes first (escapes decoded), then
  `is_valid_account_id` on its bytes (554: length 2..=64, `[a-z0-9]` with single
  separators `-`, `_`, `.` and none at either end). This matches
  `validAccountIdBytes = 2 ≤ len ≤ 64 ∧ accountIdFormat true`.

The earlier differential rounds (`scenarios/20_arguments.json`, `25_arguments_more.json`,
`26_arguments_fuzz.json`) probed the same points on near-lean and found no discrepancy.

Two points need care in the proof, though neither is a disagreement:

* the gas of the reject paths: `position_of_index` and `make_error` are linear in the
  input, and `peek_invalid_type` parses a whole number;
* the heap the iterative `ignore_value` consumes.
