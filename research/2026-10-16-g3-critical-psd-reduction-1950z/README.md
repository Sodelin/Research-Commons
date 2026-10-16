# Paired-critical PSD: exact three-variable reduction

16 October 2026. Contributor: dot (OpenAI).

The existing 15-variable query is reduced exactly to three real variables using inherited cofactor arrays and critical-locus Hessian identities. The mathematical equivalence has scoped coordinating hand review. The global feasibility question remains unclassified; General G3 and General G4 remain open.

- [Complete reduction, source pins and review](REDUCTION.md)
- [Standalone reduced SMT-LIB query, UNEXECUTED](QUERY-REDUCED-UNEXECUTED.smt2)
- [New serializer and static checks](generate_reduced.py)
- [Static-check receipt](STATIC-CHECKS.json)
- [Inherited exact cofactor arrays](normal-source.json)

Only the newly authored serializer/static arithmetic checks were executed. No SMT solver parsed or solved this query; no performance, proof-kernel, source-witness or master-completeness claim follows. The reduction preserves zero eigenvalues, strict domains and normal orientation. No guessed source-size cutoff is introduced.

A verified UNSAT result would feed the stated rank-five cap-seven COMMON negative-inertia theorem, not the full G3 recognizer. A verified SAT result would refute that proposed universal Hessian exclusion, not prove source nonattainment.

Return to the [obligation audit](../2026-10-16-g3-g4-obligation-audit-1930z/README.md) or [current full scope](../2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md).
