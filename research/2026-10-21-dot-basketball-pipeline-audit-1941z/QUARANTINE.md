# Source-label failure: withdraw real-game validation interpretation

2026-10-21. The initial real-data fit is **quarantined**. Independent external score checks found:

- 2015-10-27 Atlanta–Detroit: source home-segment labels sum −10; actual score 94–106 gives −12.
- 2015-10-27 Chicago–Cleveland: source labels sum +4; actual score 97–95 gives +2.

Accordingly the reported 175.8189 versus 147.3536 held-out MSE, paired resampling interval and fitted player coefficients are calculations on flawed/unverified source labels. They are NOT actual game-margin predictive validation, proof of model improvement, usable NBA player ratings, or evidence for the proposed all-in-one statistic. The earlier interpretation was incorrect and is withdrawn.

Original run bytes and code are preserved in `quarantined-flawed-label-run/`. Current root-level outputs carry quarantine status. Do not promote those original files without this warning. No score residuals have been allocated to intervals and no periods relabelled.

The author-source review identifies plausible mechanisms: initialization from a quarter's first post-event differential can omit initial scoring; an inner merge restricted to quarters with substitutions can omit no-substitution overtime periods. The derived table lacks the missing event increments and complete omitted-period lineups, so these corrections cannot be uniquely recovered from its fields. This explains why internal home/away conservation and duration checks were insufficient. Two games with discontinuous overtime labels were already rejected, but that does not cure the other scoring defects.

The real-data CLI now requires documented independent source-label validation before fitting. This is an explicit provenance gate, not a guarantee that a declaration is true. Reconciliation must establish correct interval labels, not merely final complementary totals. Parent/independent source review retains primary external-score citations. Source processing code: https://github.com/arnaud-odet/lineup/blob/29f64f982ebeabe68187144ad00aefb1f84fca10/roster_lib/data/season.py .

Next legitimate route is a source with correct reconstructible intervals and permitted data access, or an explicitly authorized source-side correction. The existing comparator remains a separate licensed publisher output, not a substitute for ground-truth outcomes. Implementation tests remain valid software checks; the real-data empirical gate is again open and unresolved.
