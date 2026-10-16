# Safe NEAR

Formally verify NEAR smart contracts.

Check the [human written notes](notes/README.md).

## Notes

`notes/` holds the human-written notes: the design of each component, the
plan for what is being worked on, and the TODO list. Start at
[notes/README.md](notes/README.md). The folder is written by humans only; see
[notes/AGENTS.md](notes/AGENTS.md).

## Contracts dataset

`contracts/` holds one folder per on-chain binary: the binary, its NEAR code
hash, a reproducible `build.sh`, and the upstream source pinned as a git
submodule. See [contracts/README.md](contracts/README.md) for the format and
[contracts/CATALOG.md](contracts/CATALOG.md) for the list of contracts.

```
git submodule update --init contracts/<name>/source   # fetch the pinned source
tools/verify_build.sh contracts/<name>              # rebuild and compare hashes
```
