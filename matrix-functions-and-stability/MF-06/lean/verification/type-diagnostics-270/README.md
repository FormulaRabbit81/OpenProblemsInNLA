# Actual local diagnostic evidence

The two 24.7 MB expression dumps are preserved as lossless `.json.gz` files.
`LOSSLESS-COMPRESSION.json` records both raw and compressed hashes and sizes.
Decompress with `gzip -dc challenge-types.json.gz` (likewise for solution).
The original `COMPARISON.json` remains unchanged and binds the raw JSON bytes.
This was a local Lean type/body diagnostic, not Linux Comparator execution.
