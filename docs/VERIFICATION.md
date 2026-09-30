# Setup verification

Recorded 2026-09-30T07:28:26.949Z. Operational publication and retrieval were checked; effectiveness during real cross-chat work remains untested.

## Checks performed

- Published the public setup at commit [8e48183](https://github.com/Sodelin/Research-Commons/commit/8e48183a2634463cb7fe5f2b871b45f9151d7ede) and private setup at commit 86a64f88df5a7d57d9698a79c52f8cf0fc77c7bf.
- Retrieved every setup file at those pinned commits: 15 public and 14 private files, including the initial checkpoints. All 27 newly built files exactly matched their prepared contents; both checkpoints were present.
- Checked all relative Markdown links in the 27 prepared files: none were broken.
- Retrieved the original public checkpoint at historical commit 995780b72a082a0b17ca8001f94512f11127e84c and restored it into an isolated scratch location. Its Git blob hash matched a7fdb86ebaa2cb58021a04538b18c00071031f68; it also remained unchanged after setup.
- An independent review agent read the public entry point, instructions, handoff, and argument. It found the onboarding usable for read-only participation and the stated formal arguments consistent. It caught the [pair-versus-set correction](../notes/2026-09-30-commons-builder-decision-certificate-correction.md), which was preserved rather than hidden.
- Exhaustive finite calculations reproduced the example regrets 4, 4, then 0; the causal example's intervention probabilities 1 and 1/2; and the correction's pair regrets 0 versus three-model regret 1.
- Commits were additive, based on observed current trees, and moved main without force. Existing initial checkpoints were retained. The other theory repository was only read.

These checks establish that the prepared workspace can be published, retrieved, and historically recovered, and that the stated finite examples calculate as claimed. They do not establish completeness of capture, independent scientific replication, or improvement in research productivity.

## Acceptance scenarios still requiring real use

| Scenario | Status |
|---|---|
| Read-only chat supplies a packet; another chat publishes it with attribution | Template and onboarding reviewed; an actual independent-chat publishing round trip not exercised |
| Two independently running writers survive a same-time main update | Separate paths and non-force publication used; a contested concurrent push not exercised |
| A correction retains the original and links the current conclusion | Exercised by the decision-certificate correction |
| A later chat resumes after an interruption | Historical retrieval and isolated recovery exercised; live interruption/resumption not exercised |
| A private contribution becomes an intentionally shareable public summary | No private research content imported or mirrored; an actual redaction/publication scenario not exercised |

No automated cross-chat reading, notifications, polling, or privacy enforcement has been installed. Session checkpoints are historical records.

The [completed setup checkpoint](../sessions/2026-09-30-commons-builder/0002-complete.md) records the next action.

## Expansion after Nolan's clarification

Added general project communications, a dated timeline, and an explicit boundary between concept notes and exchanges. The final prepared structure contains 22 public and 19 private Markdown files including initial checkpoints; all relative links resolved. A Zettelkasten URL remains unverified and is intentionally a pending navigation entry rather than an invented link.
