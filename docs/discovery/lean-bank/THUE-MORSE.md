# Thue–Morse: two Lean-checked ways to reuse the actual sources

The first extension imports the exact [binary digit-parity provider](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/ThueMorseBits.lean), also present with the same blob in the full-height dependency lock. For any starting phase, finite observation length and requested gap, it constructs a later phase with the same finite prefix. The two tails nevertheless agree and disagree arbitrarily far out. The specific shift \(3\cdot2^m\) from phase zero first disagrees at index \(2\cdot2^m\), using zero-based indexing. This is a finite-word observation result, not a statement that finite observations fix actual graph heights.

The second extension imports the actual [FullHeight](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/lean/SamuelAlexanderResearch/FullHeight.lean) development, instead of coding a lookalike. Let \(Z(N)\) count starting vertices \(v<N\) of matching height zero in that graph, \(t\) be Thue–Morse, and \(B\) the alternating sum of binary digits starting with plus at the least significant. Lean checks
\[
6 Z(N)=2(N+1)+B(N+1)-3t(N+1).
\]
So these starts have density one third. The formula gives logarithmic worst-case fluctuation (hand consequence: choose binary numbers with ones only at alternating positions). The included exact finite control checks 512 graph heights and 65,537 prefixes but does not replace the proof.

[Dependency order and exact Git/SHA pins](thue/PROVIDER-MANIFEST.tsv). Each path is rooted at the public repository's `lean/`. Stage those exact files (no Lake package download), then run `bash thue/replay-all.sh /absolute/path/to/pinned/lean /path/to/staged/provider`. [Lean log](thue/COMBINED-REPLAY.log). Novelties are not asserted: substitution, aperiodicity and recurrence are classical; the bounded ambiguity and frequency results here are identified by their exact checked statements and source dependencies.
