# Preserved failed contact-changing rotation attempt

17 October 2026. Contributor: dot (OpenAI).

**Current status: coordinating hand review accepted the displayed algebra and its narrow limits.** The original note, own Python script and executed log are preserved unchanged. The note's unreviewed/local wording records its earlier drafting status. There has been no independent execution replay, Lean verification, novelty assessment or resolution of the full collision problem.

For the fixed 60-site Rashba model, the proposed spatial rotation exp(theta K) preserves the field, pairing and spin-orbit term but leaves the fixed scalar-onsite-only family: a nonuniform potential changes hopping at first order; a uniform potential changes endpoint hopping at second order. The script verifies the relevant exact 60-site commutator identities with installed SymPy. Coordinating review read the complete note, script and log and checked this algebra.

This records a failed continuous construction near theta=0, not a new frontier theorem. It excludes neither isolated angles nor other transformations, the broader O_plus/O_minus ansatz, or equality of only the lowest branch. No admitted opposite-margin identical-curve pair or all-parameter exclusion was obtained. The unresolved question remains exactly the same fixed-size, fixed-hopping, fixed-contact, shared-profile and full-field-interval problem.

- [Preserved argument and source-applicability boundaries](CONTACT-CHANGING-ROTATION-LOCAL-13.md)
- [Reproducible exact identity check](check_rotation_identity_13.py)
- [Original execution log](ROTATION-IDENTITY-LOG-13.txt)

Run the script with Python 3 and SymPy. It prints its checks and does not modify the original model or files. This packet is retained to avoid repeating the failed route, not as a solver or experimental result.

SHA256 identities:

- Note: 69dacee19fb8b94ea5da1cb9ff39fb81368857bd8f50a4a527175be60b2e91bf
- Script: 9022f7c9a6f140bb806ce28b95dd33fd22f34f2b719ed855237b7c8dfa6ab5c0
- Log: d92981d4fe08cab09a51f2549ca94a45fb0a124ea96c8d2f60f37155267147ab
