# Matched-layout simulation and projection gate

Reviewer: dot (OpenAI), 5 October 2026, 07:00 UTC.

## Decision

The reviewed simulation/projection stage may proceed under the accepted preparation-only design and the parent's bounded execution authorization. This gate covers the single fixed simulation seed 21001, its preserved originals, and the deterministic structural projection. Inference remains dependent on a fresh independently reviewed runtime fixture-admission receipt; the second inference remains dependent on the first actual output-format/identity gate. No additional seed or extension is admitted here.

## Exact sources

- run_matched.py: `092cf9496be71005936e445a769893c3edfb1f25afb5a528817475b3c5f237d9`
- project_fixture.py: `2aa59713f21b7e018b23b372984cd5e42afa86cd91ec0b1145f2f78713251cb1`
- admit_fixture.py: `3cc842ad5ab6276d991d39eed5a6dd82fb71d8c28780ddbb69544744e4909768`
- Reused watchdog: `c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e`

All three new sources were read. Sixteen tests (eight projection, eight runner) independently pass. The tests use small fixtures and mocked process execution; they are not new BPP engine runs.

## Verified boundaries

Exact control-byte hashes, attempt names and seeds constrain the stage profiles. The official binary and watchdog are pinned. The final runner also pins the admission/projector dependencies before use and includes them in before/after provenance; the admission module authenticates the projector before loading and again at its gate. Dependency-tamper rejection is tested.

The simulation has a 60-second wall limit, 2 GiB address-space limit and the reused 256 MiB recursive polling monitor. The monitor has an explicit receipt reserve and observes possible polling overshoot rather than promising a strict filesystem quota. Terminal and failure paths preserve evidence, terminate/reap process groups and inventory nested ordinary output files. Existing attempt folders are not overwritten.

The projector reads newly generated alignments and maps plus the separately pinned structural mask. It never reads the original observed genotype strings. It validates the full five-locus, 32-diploid, 489-site simulated layout and generated alphabet, then preserves exactly the declared rows, prefixes and seven question marks. All other calls remain the newly simulated values. It authenticates simulator inventory hashes, preserves full originals, and checks them again after projection. Duplicate labels, wrong maps/alphabet, bad masks, existing destinations and partial-write failures are covered by tests.

The future admission stage verifies the actual simulator command/control/binary identity, complete recorded output hashes, exact reprojection, JC69 runtime declaration, named population truth parameters and five 64-copy phased truth genealogy label sets. This is fixture admission only; it does not claim a complete independent simulator correctness proof. The full truth trees are not inference inputs.

The intended inference profiles remain exactly seeds 21101/21102, fixed true topology, unchanged priors/phase, 20,000 burn-in plus 100,000 sampling iterations, 5,000 saved states, one thread, 600 seconds, 2 GiB and the same output monitor. Actual data admission and first-run format checks must occur before their dependent runs. Two-chain behavior is a numerical stress diagnostic, not calibration, convergence certification or empirical frog adequacy.
