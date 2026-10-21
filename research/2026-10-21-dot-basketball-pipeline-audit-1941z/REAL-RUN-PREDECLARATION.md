# Retrospective net/time diagnostic, fixed before fitting

2026-10-21. Source 2015–16 institutional derived table, DOI 10.57745/9 NVFIQ, Etalab 2.0. This is not a prospective benchmark.

Training games: dates through 2015-12-31. Validation:2016-01-01 through 2016-01-31. Test:2016-02-01 onward. No test-set penalty tuning. Compare home intercept alone against duration-adjusted additive ridge with penalties 1,10,100; validation objective game home-margin squared error. Final fit uses training+validation. No team-change subgroup claimed; no possession count or offense/defense split inferred. All eligible test games are included. Sources previously received structural auditing only, not model performance inspection.

Date comes from the source game ID, checked as ISO date. Within-quarter row order comes from preserved source order, as audited against author processing code. Final margin is reconciled internally between home/away, not independently verified against a second scoreboard. Report all these limits with results, whatever their direction.
