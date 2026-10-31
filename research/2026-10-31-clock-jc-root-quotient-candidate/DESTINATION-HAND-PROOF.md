# Exact corresponding-destination quotient: hand proof

31 October 2026. AI-assisted derivation by dot (OpenAI), NOT kernel verification. This note does not select or certify the separate unreviewed merge-join Lean scratch. The selected independent source adapter remains SHA256 5495fb22a26eebc6e48e50d48241fa319a13c22d875468798c915e8a4ac4bf28.

Fix one original graph, one original labelled copy type/sample assignment, and positive original rates. Let s,t be original admitted source codes. Assume their actual complete descendant-block sets agree, and copyLocation(state s,x)=copyLocation(state t,x) for every ORIGINAL copy x. Neither register equality nor full source-state equality is assumed.

For an actual choice p=(i,(a,b)) in s, the source catalogue makes a,b distinct live roots in originalPlace(N,i). Their descendant sets A,B are nonempty and disjoint by source validity. Equality of the complete current-block sets supplies actual live roots a',b' in t with EXACT same labelled sets A,B. Source-valid leaf fibers make these roots unique. Since A and B are distinct, a' and b' are distinct. For any x∈A, the original leaf-fiber equations give ancestor_s(x)=a and ancestor_t(x)=a'. Thus equality of original-copy locations gives location_s(a)=location_t(a'). The same holds for b,b'. Therefore p'=(i,(a',b')) is an actual legal choice in t at the SAME original population index i, and has the SAME pairRate(i)/2. Matching back by the same blocks proves bijectivity; no quotient generator or transition law has been assumed.

Now apply the accepted actual_merge_blocks theorem to each original raw merge:

    blocks(merge(s,a,b)) = insert(A∪B, erase B (erase A blocks(s))),
    blocks(merge(t,a',b')) = insert(A∪B, erase B (erase A blocks(t))).

The two right sides are literally equal by the initial block equality. Apply the existing merge_population_preserved theorem separately to each legal merge: every original copy keeps its population within this epoch. Therefore the two raw destination observations agree, not just the pair's own location.

The ACTUAL stepDestination is admittedCode of this raw legal merge, not the raw State itself. FiniteSourceSnapshot.decode_encode_live_genealogy preserves every live genealogy and the live set is definitionally unchanged; hence its descendant-block image is unchanged. decode_encode_copyLocation preserves every original copy's population. Composing these two already-proved encoding facts with the raw merge identities proves observation equality for the actual CODED destinations. No equality of ordered tree shape, history, survivor IDs or registers is required or concluded.

## Edge cases and limits checked

* Empty live/Choice carriers give an empty bijection and zero totalRate; no division by totalRate is used here.
* Every block keeps all original labelled copies. This is not a selected/pruned-panel argument; a pruned empty block would invalidate the witness step.
* Both pair orientations remain distinct choices. Destination observation agreement plus this deterministic construction is still not equality of future weighted continuation; that requires the fuel induction against accepted original weighted renewal.
* The bijection preserves the original Option E index; it does not silently identify distinct graph locations or provide a P-sized epoch code.
* Different retained registers can affect a later routing boundary. No whole-calendar factorization follows from this epoch-only deterministic result.

This establishes the intended source correspondence at hand-proof level. Compiler acceptance and independent review of the selected adapter remain separate gates. The full original finite-window theorem remains HOLD_FULL_LEAN_PROOF_PENDING.
