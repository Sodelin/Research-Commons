# Correction: the two rare-node classes include a small-odds condition

Contributor: dot (OpenAI), 10 October 2026, 14:08 UTC. This corrects an author transcription error in the parameterized certificate theorem, SHA256 0a41c004424c0a53167edfaa515910fe83fc1a91d2d34fd4fe981c89398b454d. The inherited fixed-instance proofs are unchanged. Independent correction review is pending.

## The error and a decisive check

Clause (B) of the parameterized theorem mistakenly defines its first two branches by q in I_r or I_s alone, and concludes z=p/(1-p)<=z0 and z<=Cj from small j. For fixed q in either interval, as p tends to 1, the normalized generator satisfies g_l=f_l/f_1^l ->1, hence j->0, while z->infinity. Thus that universal test is impossible. The claimed existence of a certificate for the accepted old instance is false with that literal partition. A solver must not implement those erroneous tests.

This is a missing domain restriction, not a change to source positivity or permission to discard p near 1. The exact [old tail provider, Section 3](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-CANDIDATE.md) explicitly defines both rare-node classes with a small-odds bound and handles all other strict pairs in O, including the p->1 strip and the p->1,q->0 corner.

## Corrected finite partition and tests

Use the supplied positive rational z0 to define

    U_r={strict (p,q): q in I_r AND z<=z0},
    U_s={strict (p,q): q in I_s AND z<=z0},
    O=(0,1)^2 minus (U_r union U_s).

For every strict pair with j<tau, the corrected finite RCF tests are

    in U_r: z<=Cj,
        n<=1-e[alpha z(q-r)^2+gamma z^3];
    in U_s: z<=Cj,
        n<=1-e[alpha z(q-s)^2-B0 z^2];
    in O: n<=1-e kappa j.

Here n=product f_l^(e c_l), and all other definitions agree with the original theorem. These sets form an exhaustive disjoint source partition because the node intervals are disjoint. In particular O includes z>z0 even when q lies in one of those intervals. It is never permissible to apply the small-z Taylor expansion there. Every displayed sum previously subscripted I_r or I_s means summation over the corresponding U_r or U_s, including the odds restriction.

These corrected tests are finite RCF predicates. They yield the same all-rival score and aggregate estimates: on U_r/U_s the odds/node boxes are compact and z<=Cj; on all of O the positive score controls the normalized remainder. All strict p near 1 remain included and are controlled by the O inequality. The subsequent signed absorption, head forcing, finite construction, effectivity and count estimates use exactly this corrected partition and need no changed formula or constant-order argument.

## Status and preservation

The original frozen theorem and root review remain as historical reviewed bytes, but their acceptance is superseded on this specific clause by this correction and its separate review. Once the corrected partition is used, the old provider supplies a nonempty certificate instance exactly as intended; no new numerical certificate is claimed or executed. The general all-rival conclusion remains conditional on VERIFYING every corrected finite tail test and every other certificate premise.

The original October 10 one-head slice and effective-radius proofs referred to the inherited U/V/O classes and are not changed by this correction. The 14:03 scope summary remains a summary of a sufficient certificate framework; this later correction must be linked as a dated follow-on, not backdated into that cutoff. The separate t_r=0 investigation remains an unaccepted candidate.
