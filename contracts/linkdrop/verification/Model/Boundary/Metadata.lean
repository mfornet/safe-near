import Model.Boundary.Encoding

/-!
# Metadata exports

`cargo near` adds two methods to the binary: `contract_source_metadata`
(NEP-330) and `__contract_abi`. Both ignore their input, the deposit and the
state, and return a constant: the NEP-330 JSON, and the zstd-compressed ABI
near-sdk embeds, stored verbatim in `contract.wasm` (at byte offset 96462).
-/

namespace Linkdrop.Boundary

/-- The NEP-330 metadata `contract_source_metadata` returns. -/
def sourceMetadata : String :=
  "{\"version\":\"0.1.1\",\"link\":\"https://github.com/near/near-linkdrop/tree/9a6bb316f6" ++
  "b7c83b504ce9c94a80c37178097655\",\"standards\":[{\"standard\":\"nep330\",\"version\":\"1.3" ++
  ".0\"}],\"build_info\":{\"build_environment\":\"sourcescan/cargo-near:0.16.0-rust-1.86." ++
  "0@sha256:3220302ebb7036c1942e772810f21edd9381edf9a339983da43487c77fbad488\",\"buil" ++
  "d_command\":[\"cargo\",\"near\",\"build\",\"non-reproducible-wasm\",\"--locked\"],\"contract" ++
  "_path\":\"\",\"source_code_snapshot\":\"git+https://github.com/near/near-linkdrop?rev=" ++
  "9a6bb316f6b7c83b504ce9c94a80c37178097655\",\"output_wasm_path\":\"/home/near/code/ta" ++
  "rget/near/linkdrop.wasm\"}}"

/-- The compressed ABI `__contract_abi` returns, as lowercase hex. -/
def abiHex : String :=
  "28b52ffd0088753800da4a380d34406d9b03c3300cc3c03a86f5c3840dc9941c24250971526b49e4" ++
  "26f23628c1b3bcfa851f1a9243c4af38d048af73fdbe310c7326c200bd00cd001554bf800f8a7e6a" ++
  "6c531308075a9afaefafec77bc1cbbebc5ad3f64da5ad51ca346e872e157a0c370188ef48b41a6ee" ++
  "b28e1b8fbe9566b4e851a8fcc8545af99fa89df8293dbe7bbc56e25acb2ea51c9b2de84e33f8d101" ++
  "2e66d3665b8ef7977b968a712673c089c0888bf0a57319907004e07a7fddda96626d5fd44028cd82" ++
  "8997d378f173539dea18706b2a25c0e52ab0532d9ac9d378b3f42f053802286e96e1b6e994aee9f0" ++
  "34f9c9f2756a204d8453c089689ec6f17aab0694934acb9b0e016dc2a93b76a98d399ab259993655" ++
  "a96033562a6fe98662eb5b123356468ed2503961f5d4a4e85c2b2a2a8d4081c2c2c2f89d14726ab6" ++
  "b8759c6aec053f77b17ba2bb7eaf155a46d0ebe517f917c4dc048a992e971a2ca17e8720508bb2ca" ++
  "47d57e692f438f9e63f373a033a6ee49e1af33a50c994bc47f8c5187907e6a37185d0d48573f7608" ++
  "9251df899bc2b7e7da1456312159b7166512088b7600882d7469c7ae81aa1e4a0edb725bdda7eca4" ++
  "94716bcc6d86d3fabe176dac30a71ea8de4a358520716129860206d4b3013e2cf8ec3c7c70a04482" ++
  "081e0f47b742be0b123c4fae7af8d06038007c3f1c5436c63de7e150efa49c06c369305001e2a36b" ++
  "5be26b43f03ca90ed51f562a156aca0d0a84807844220ae1a0e872ca74695388cddd14135475646f" ++
  "130fd7f63ac23602d1a6979c0d656e1d14e71f478b1936d5d016d1cf56bd986434635e1d4bed88cb" ++
  "e9490861db5203abfd95ef2a4788be0deb1ea68577ca2a102b4c50583cb5bd5c19e4a2fd42480e44" ++
  "44de92cd2497662722913cd4bfd43c733f3a865b994c26a3afff4169ad942142cf07e89472952cb0" ++
  "855a35d6a1a4d093318d10b1720eab9ea3af5309838fe65e75b07a6b8b991203f02fae284c7bdf06" ++
  "6d87b1f43a21562acdda63e9029dacc84c1e9101041c88ca78499ed22f32adb851ca96d356ac22df" ++
  "0da865c4ed02a9bf09094c7fa76d106481642c132a9710a569edb9897e15e97e2bc5fd4b35446cc1" ++
  "0827e269a637ad5b89d77ad177eb93fe667766f0614dd7821d2e306a81bf1ee5419928f0764c1064" ++
  "20cfe3aea1c3f364307f7f8d516581c44b50098198a891a95288664692a420a5e13108c250989518" ++
  "9e0722a940c94130869022841865249089241a092410099324693afc1ae380055e9152bffb5906d0" ++
  "4e5fc924839c168d9de8f8af144f6ae33eb7e6429b4c9f90afda773d3991217bb1c75135bb7caac6" ++
  "9a71dfe080afb88304e3d190cdcb6eabdce9f4596741b6a2e8fee14885868a4c028d4370389aa731" ++
  "a14fecb0778d6d6cd888554cddd4bd4d786e0a5ba139a4bac981e13c53e145a5e3c2e9c422f4d450" ++
  "c4fa00f4a5d8984b28fb6efd752c24711cbda8be1af68d0d6aebc8c2211d96abf1de9d9738e8e680" ++
  "64cf5e9f7c311cd37033b9dc4885c4fd495a0afccc139832b2eafae298dd2c9df6518451978f2787" ++
  "ae080804141c129cf5d2051de825cd10fc0bae9d87038fec890a07e485fe9643e4fceb7131530134" ++
  "98ee4e3832bb3f03c45bb94da0214f2508281c099a6655b1fa0a81432fe39e537f954fa854c506bd" ++
  "8b48e0be8620cce8883ecf19fa6651358ba64ad2543d0b2dc04a048a0f4e0d5bb9f478ed4824f049" ++
  "ed7a49d942d85d07c39a63b40dc6e4f7ff5fe015a479d0a1d397dd066bdb37127ee151ef9840c97c" ++
  "63fa806066f0a8889338c9fde4d4381420ee2fd51af9a769645915bda29cf0c78df00f4a863533ad" ++
  "9ffff90a44e43f8cc9699c0a7a620049ec201955450782c86647a2cec9ca98d208183012d792514d" ++
  "beb0141c4836486a1d0db4a87880e389de2bc291acaf973531411c95c8e41028a4a29956dbce1849" ++
  "a55d57193f6ff794b04d1672560ca41ccd8739ce0438e8f130f0ba8ce8e44cc2675e250e0640c02a" ++
  "6aba250c1d19f35280bb1d5994c0260854481eff1d8ee9782ad896675ea8246bc6ab045cc3e2176a" ++
  "31c46c0b8c764b12c8c682439fafae58889b98538be8a4ea31385157aef57d650e66316e6bc038c3" ++
  "600c7e23e139fa64f399b351694a8d888106ea1f8450d0ac508704f2a05a64ec20580a8cc08f437a" ++
  "8fbc145c194932439a7d3bf4170a0a8953d22e60c082dce836627e330f6cfeeb576d25559346fa78" ++
  "383759e15de038503bbb7bf80b0d50c80ec7fe03ff100379ed5ffe1f7f9a9c2683368b5e9fb82a87" ++
  "54e976235430053b7d5676338705808905fb474ecd8c404ef4073bf5bdea724058ae6ba8588db9f1" ++
  "26792bb6232c6c7feb20187d05ef4b5deba5ead25c14dc96b25900395ac0b96c9abd8cddef0f9613" ++
  "f639dac3447e6acb9af9960b6e2d933dbd2caff68c56e0c7fb495bdd06fd05a8811ad582d96be414" ++
  "08e933ffb0a8e6bb0865a05422e7708db500be0039a33264da8130f0d0844fbd1565b9712dc32ccf" ++
  "5a1aa3c0de02e97480904473f9a006"

def bytesOfHex (s : String) : Bytes :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → Bytes
    | a :: b :: rest => UInt8.ofNat (digit a * 16 + digit b) :: go rest
    | _ => []
  go s.toList

def abiBytes : Bytes := bytesOfHex abiHex

end Linkdrop.Boundary
