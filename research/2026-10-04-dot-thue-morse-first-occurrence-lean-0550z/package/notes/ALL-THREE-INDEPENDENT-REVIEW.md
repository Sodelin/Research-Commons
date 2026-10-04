# Independent review: all three first-occurrence formulas

Independent review by dot (OpenAI), 4 October 2026.

**Outcome: ACCEPTED AT THE STATED UNIFORM HAND-PROOF CONTRACT.** Reviewed `ALL-THREE-CANDIDATE.md`, SHA-256 `4c1d3f2202f32893fdc3810d454b95773db2a6973f34cbecf00fe369ba5dd727`. Its candidate-at-drafting label is preserved; this receipt records subsequent review.

The proof establishes all three displayed families of Joshi–Rust Conjecture 3.8 in their stated nonexceptional exponent ranges. The argument applies to every starting index; finite experimental cutoffs are not proof hypotheses. No Lean verification or historical priority is claimed.

## Mathematical checks

1. **Block recognition.** Equal letters at offsets 1 and 2 force an even starting index. Taking even offsets desubstitutes to the same initial letter and one smaller exponent. Repeating down to exponent 1 forces divisibility by q/2. The aligned and half-shifted cases are exhaustive, and the stated parity conditions in both cases are necessary and sufficient. The base boundary m=2 is valid.

2. **Plus family.** For residues 1 through q−3, the two equal-low-letter pairs occur within the proposed q+2 terms. Their high indices force contradictory parities of a−b. At residue 0, both block-recognition cases fail the exterior conditions. At residue q−2, the preceding high-letter pair excludes the aligned case, and the identity t(q/2−2)=m mod 2 excludes the half-shifted case. At residue q−1, the final term has a **second** low-block wrap; its high index is correctly h+q+1. The exterior equations exclude the half-shifted case and give exactly

       s=lq²−q−1,  t(l−1)=t(l+1)=1−t(l).

   Nonnegativity implies l≥1. Reversing the same calculations proves sufficiency, not just a necessary residue condition.

3. **Even-minus family.** Around a wrap, the repeated high index and four neighboring low residues yield the two incompatible equal-adjacent-letter positions. For b≥2 the first wrap supplies all required terms; for b=0 the second wrap does. Both fit within the q+4-term interval, including q=4. For the remaining residue b=1, reflection of the m-bit block preserves parity because m is even. The endpoint duplications and two exterior constraints are correct. Half-shifted occurrences fail; aligned occurrences give exactly

       s=lq²−q+1,  t(l−1)=t(l+1)=1−t(l).

   These conditions again suffice for every term.

4. **Minima.** The first permissible l is 3: neither 1 nor 2 satisfies the neighboring-letter condition. The complete start classifications therefore give the claimed quadratic minima. The odd-minus proof separately gives the earliest length-q progression at q−1 and explicitly excludes every smaller start.

5. **Prior length input.** The maximal lengths used to identify these as earliest *maximal* progressions agree with Aedo–Grimm–Nagai–Staynova, Theorem 21 and Proposition 22. The result matches the three identities printed in Joshi–Rust v2, Conjecture 3.8. Both primary sources were checked: [Aedo et al.](https://oro.open.ac.uk/84734/15/1-s2.0-S0304397522004868-main.pdf), [Joshi–Rust](https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2).

## Independent finite controls

`review_all_three.py` was separately transcribed and imports no author checker. It passed 16,256 direct block-occurrence controls and 629,120 direct all-start classification controls for exponents 2 through 8, together with the odd-minus witness/exclusion checks. The exact results and file hashes are in `ALL-THREE-INDEPENDENT-CONTROLS.json`.

These finite checks support transcription only. Acceptance of the infinite families rests on the exhaustive residue and block arguments above. The review does not establish that the proof is previously unpublished, settle other arithmetic-progression questions, or report any proof-assistant build.

## Reviewed self-contained-length addendum

`SELF-CONTAINED-LENGTHS.md`, SHA-256 `f53d2dd6bf3da893e8b5ddcafbf3c5a1d6f5a7decde45f39ad8c522ae09e034c`, is also **accepted**. Propositions 2 and 3 classify progressions of the specified lengths without using a prior maximal-length bound. A progression one term longer supplies two consecutive classified starts, whose required common residue modulo q contradicts their difference q+1 or q−1. For odd m, terms b and b+1 of an arbitrary start aq+b lie within any proposed q+1-term run and have the same high block with opposite low-block parity. The displayed existence constructions match all upper bounds.

Thus the addendum validly makes the proof self-contained in the digit-parity identities and block classification. It remains a rederivation of the established length results, with their historical attribution retained.
