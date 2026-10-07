# Bounded exact check of the selected rooted skeleton lemma

New check,6 October2026. Enumerate every rooted unordered binary tree on one/two labelled A tips and one/two labelled B tips:1+3+3+15=22 trees. This is a finite SUPERTYPE of the selected opened skeletons used in the hand proof, not enumeration of all original graphs.

For every fixed B tip test whether its LCA with each A tip is equal. If equality holds, check that the A-tip LCA subtree contains no B tip and that the A-exclusive path edge-incidence vector splits EXACTLY as an A-tip-to-common-ancestor vector plus a common-ancestor-to-B-meeting vector. If equality fails, check that the two B-exclusive path vectors are strictly nested, so arbitrary positive edge hazards cannot have equal sums. Preserve every tree and result.

This does not replace the hand source reduction showing why a general cut-child graph has such a selected skeleton, nor the Jensen calibration or root/register semantics. It supplies an exact finite check of the elementary rooted-tree step only.

Caps:5 CPU seconds,10 wall seconds,128MiB, standard-library Python, no installs. Preserve code, command, output, exit and failures. No source recognition, arbitrary-core catalogue, RCF or Lean execution.
