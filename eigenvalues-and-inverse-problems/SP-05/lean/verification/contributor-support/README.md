# Local contributor proof-support evidence

This archive records the successful local build of `NLA.SP05.Cone` and its
contributor-owned dependencies `Complexification`, `Sylvester`, and `Modulus`.
`build.json` records exact source hashes, root-owned dependency hashes, the
unchanged ten pre-proof inputs, build exit code 0, and permitted axioms.
`build.log` contains exact compiler messages extracted from the retained
Lake `.trace` files under `lake-traces/`, retained byte-for-byte with `.trace.json`
filenames so Git includes these evidence records despite the build-cache ignore rule.
These raw logs contain temporary
local checkout paths; they are provenance records, not portable commands.

Reproduce from this Lean project with:

```bash
lake build NLA.SP05.Cone
```

The proof contributor is an implementation author, not an independent
referee. This evidence does not claim a final source review, actual Linux
Comparator execution, or canonical status promotion. The later complete
Solution build is recorded separately in `../local-solution-build.log`.
