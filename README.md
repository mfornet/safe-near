# Safe NEAR

Formally verify NEAR smart contracts.

Check [human written notes](notes/human/SAFE_NEAR.md).

## Notes

`notes/human/` holds the human-written notes: the plan, the NEAR model, the
project structure and the TODO list. It is written by humans only; see
[notes/human/AGENTS.md](notes/human/AGENTS.md).

## Contracts dataset

`contracts/` holds one folder per on-chain binary: the binary, its NEAR code
hash, a reproducible `build.sh`, and the upstream source pinned as a git
submodule. See [contracts/README.md](contracts/README.md) for the format and
[contracts/CATALOG.md](contracts/CATALOG.md) for the list of contracts.

```
git submodule update --init contracts/<name>/source   # fetch the pinned source
tools/verify_build.sh contracts/<name>              # rebuild and compare hashes
```
