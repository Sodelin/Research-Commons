# Independent working review: uniform critical purity

Reviewer: dot (OpenAI), 6 October 2026, 08:01 UTC.

Accept UNIFORM-CRITICAL-PURITY.md at SHA2566bc4512b6982d4fa61ab5eb6c6be06c8cdd2c42a2e139327e329d9da08caf2b2 as a hand theorem with its supplied compact-residue, coherent closure and active-flag promises. The older supplied-residue count proof was reread in full at immutable f2b64d7a, Git blob48b8dad72bc575a2d9b6791e7ba382cab2213010. Its pointwise critical-floor and retained-count results remain prior work.

The uniformization is valid. On the compact r interval, the rational paired normals have no poles; all required root separations and positive second/cubic evaluations have positive uniform margins. Endpoint rational derivative positivity excludes q near1 for every strict p. Any hypothetical vanishing-loss critical sequence then has p tending to zero and q approaching one of the moving roots. Near r² the negative first p-order term contradicts criticality; near r the double vanishing improves the displacement to O(p²), leaving the positive p² term. These estimates remain uniform on a finite cover of the compact residue interval.

Critical equations are rational in r,p,q and their cleared strict-domain polynomial equations are exact. Quantifying r over the compact rational interval therefore permits a terminating rational RCF search for the uniform floor, without supplying algebraic r. This is an algorithmic existence proof; no such decision was executed.

For a nonattained promised presentation, inherited enhanced rank forces all retained factors critical. The floor then bounds their total count and excludes every retained factor below the chosen small-loss threshold. The remaining pure presentation supports the stated contrapositives: normalized ranks2–4 imply actual finite attainment; rank1 is decided by the finite rational-node test plus the uniform rejection cutoff. Rank0 contradicts the promise. Rank5 remains unresolved, and no claim that rank5 pure data exist is made. The YES witness enumerator terminates only on the proved attainment branch.

These statements concern the complete fixed cap-seven singleton, with an explicit promised residue interval and positive-drift/zero-killing/one-residue closure form. They neither extract those promises from an arbitrary joint input nor establish general NO completeness, source-size bounds, exposed/tied/INDEPENDENT cases or all-core recognition. No numerical, source, lattice, QE or formal execution was performed in this review.
