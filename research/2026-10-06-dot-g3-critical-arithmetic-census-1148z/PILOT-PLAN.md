# Bounded universal-constant check

New check, 6 October 2026. This does not rerun historical cofactor/resultant evidence.

Input: the accepted reduced-B integer coefficient JSON, SHA256 cc57db65563ac4a7e2f5bf9581b8b75803f2052a49d19442f5e756a0f82996e3. Verify the hash before reading its coefficient arrays.

Operations: standard-library integer sums and powers only. Compute the safe L, c and ell of WORKING-PROOF.md; check the homogeneous identity P6=(A+2B)(A^3+3AB^2-2B^3)+9B^4 by integer coefficient convolution; check 44*24745+42*441=1107302. Preserve a JSON output with input hash and new-run timing.

Caps: 5 CPU seconds, 10 wall seconds, 128MiB address space. Stop on any assertion/error/timeout and preserve it as failure or unknown. No input-dependent endpoint QE, critical census, denominator bound or recognition run is part of this pilot.
