# G4 copy-consistency obstruction

Independent hand review ACCEPTS the elementary exchangeability theorem at the **all-allocation exchangeable/deletion-consistent binary sign-adapter scope only**. Fair independent pair marginals force all iid. This excludes direct copy-index HMM parity unrolling, not arbitrary forest encodings or original G4.

Read COPY-CONSISTENCY-OBSTRUCTION.md and INDEPENDENT-REVIEW.md together. Original reviewed bytes and SHA256SUMS are preserved; ACCEPTANCE.json updates their earlier pending-review metadata without modifying them. DISCOVERY-INVENTORY.json plus ACCEPTANCE.json are ready for the existing CLI ingestion owner; no registry is modified.

Replay using existing Python3 standard library:
```sh
sha256sum -c SHA256SUMS
python3 check_extension_bound.py > replay.json
diff -u check-result.json replay.json
```
The seven exact arithmetic cases check the finite-extension bound; the all-n proof is mathematical, not an extrapolation or a Lean proof.
