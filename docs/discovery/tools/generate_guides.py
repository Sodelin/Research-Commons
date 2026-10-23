#!/usr/bin/env python3
"""Generate human/agent entry routes from the existing source, not a new registry."""
import json,pathlib,collections
ROOT=pathlib.Path(__file__).resolve().parents[1]
source=json.loads((ROOT/'dist/claims.json').read_text());meta=json.loads((ROOT/'dist/source.json').read_text())
OUT=ROOT/'github';OUT.mkdir(exist_ok=True)
claims=source['claims'];byid={c['id']:c for c in claims}
def card(c):return f"[**{c['id']}**](CLAIM-BOARD.md#{c['id'].lower()})"
def clean(s):return s.replace('|','/').replace('\n',' ')
intro=f"Generated from the existing canonical claim register at `{meta['commit']}` ({source['board_version']}). Attribution and scientific statuses remain with its authors. This is a discovery view, not a new proof audit. The register contains {len(claims)} selected cards and is not exhaustive.\n"
lines=['# Find an answer in Research Commons','',intro,
'Begin with the question you need answered. Each link opens the exact claim, assumptions, proof/review sources and remaining obligation. You do not need to reconstruct commit history.','',
'- **Which existing published questions have we addressed?** Start with the source-attributed table below. Addressing a branch is not necessarily solving the entire published conjecture.',
'- **What is established or refuted?** Follow the scoped result cards; completed hand mathematics does not become open because Lean is unfinished.',
'- **How do the results connect?** Read [typed relationships](RESEARCH-CONNECTIONS.md). An idea in common is different from a proved adapter.',
'- **What should an agent work on next?** Use [the reuse-before-work procedure](REUSE-BEFORE-WORK.md), including the exact unsupplied implication and completed suppliers.',
'- **Need full context?** [Canonical claim board](CLAIM-BOARD.md), [status corrections](STATUS-LABEL-AUDIT.md), [accepted work](ACCEPTED-RESULTS-AND-REMAINING-WORK.md), [October source map](OCTOBER-2026-RESEARCH-MAP.md).','',
'## Published questions and credited classical suppliers','',
'Origin is taken from the canonical card. This table does not assert a new historical-priority review.','',
'| Entry / exact provenance | What this contribution establishes | Boundary |','|---|---|---|']
for c in claims:
 if c['origin']['category'] not in ['published_open_problem','classical_prior']:continue
 origin=c['origin'];url=origin.get('source_url');ref=f"[Original source]({url})" if url else ('Classical prior' if origin['category']=='classical_prior' else 'Direct original-paper link not indexed')
 lines.append(f"| {card(c)} · {ref}. {clean(origin['detail'])} | {clean(c['plain_language']['what_we_learned'])} | {clean(c['plain_language']['what_cannot_conclude'])} |")
lines+=['','## Browse by the question','']
groups=collections.defaultdict(list)
for c in claims:groups[c['programme'].split(' · ')[0]].append(c)
for group,items in groups.items():
 lines+=['### '+group,'','| Question | Result / use | Disposition |','|---|---|---|']
 for c in items:
  p=c['plain_language'];lines.append(f"| {card(c)} · {clean(p['question'])} | {clean(p['what_we_learned'])} {clean(p['what_it_lets_someone_do'])} | {clean(c.get('completion',{}).get('display',c['mathematical_status'].replace('_',' ')))} |")
 lines+=['']
lines+=['## Missing from this map','',*['- '+s for s in source['coverage']['gaps']], '',
'A failed lookup is **status unverified / not indexed**, not evidence that a result is absent or mathematically open. Search the archive and ask its current owner before allocating another derivation.']
(OUT/'FIND-AN-ANSWER.md').write_text('\n'.join(lines)+'\n')
lines=['# Research connections: what depends on what','',intro,
'Directions below follow the canonical register: the source card names a supplier/connection. The relationship type is part of the result. Do not promote a candidate or common idea into a proved implication.','']
for relation,definition in source['relation_types'].items():
 lines+=['## '+relation.replace('_',' '),'',definition,'','| Source card | Named connection | Exact scope/detail |','|---|---|---|']
 found=False
 for c in claims:
  for r in c['dependencies']:
   if r['relation_type']==relation:lines.append(f"| {card(c)} | {card(byid[r['claim_id']])} | {clean(r['detail'])} |");found=True
 if not found:lines.append('| No edge indexed at this snapshot | | |')
 lines+=['']
lines+=['## Reading scientific completion beside implementation','',
'The [existing Lean gateway](https://github.com/Sodelin/Research-Commons/blob/3a309156d573b1b61f1c32c83e881ad61e538cf7/research/2026-10-21-lean-online-builder/RESEARCH-DISCOVERY-GATEWAY.md) joins G6/G7 hand results to current implementation evidence, G3/G4 open endpoints to already-completed suppliers, and P5 completion to its complete proof/verdict/correction. This is an evidence-navigation relation, not an added theorem premise.','',
'Cards without a typed edge are not asserted unrelated; their connection simply has not been indexed. Broader coverage remains ongoing.']
(OUT/'RESEARCH-CONNECTIONS.md').write_text('\n'.join(lines)+'\n')
(OUT/'REUSE-BEFORE-WORK.md').write_text('''# Before starting work: recover the result and name the new gap

Use the existing canonical register and current owners. This procedure prevents accidental re-derivation without suppressing useful independent checks or improvements.

1. Search [questions and answers](FIND-AN-ANSWER.md), the [claim board](CLAIM-BOARD.md), [accepted results](ACCEPTED-RESULTS-AND-REMAINING-WORK.md) and [status corrections](STATUS-LABEL-AUDIT.md). Search by the scientific question, its aliases and exact assumptions, not only a task title or recent commit.
2. Read the actual accepted sources/reviews and later corrections. Record the stable claim ID and immutable source. A historical pending header does not override a later matching acceptance. A failed lookup means status unverified, not mathematically open.
3. Match the proposed statement, quantifiers, source/observation model, output and cost to those sources. Reuse completed suppliers. A formal/native gap does not reopen completed hand mathematics; a broader question does not demote a narrower theorem.
4. Name the exact remaining implication and its existing owner. Classify the proposed action: new result, independent proof/check, sharper scope/bound, new application/adapter, useful failed-route exclusion, source recovery/integration, or no added result. A return to the same starting point needs this explanation before another job.
5. Publish the actual difference with source/evidence, supersedes links where needed, and one next bounded action. Preserve owners, holds and uncertain/consumed operations. Discovery grants no execution authority.

## Agent lookup using the same reader engine

From this repository, after Node is available:

```sh
node docs/discovery/tools/query.mjs --query 'independent routing' --refresh
node docs/discovery/tools/query.mjs --query 'CB-G6-001'
node docs/discovery/tools/query.mjs --origin published_open_problem
```

The interface returns the exact claim scope, separate evidence axes, accepted source links, typed dependencies, owner-supplied implementation/proof joins and genuine remaining obligation. `--refresh` retrieves the current canonical PUBLIC register in memory. Without it, the source-pinned snapshot is explicitly identified. Browser and CLI share one ranking/facet module; no model call or local background service is required.

## Record before a new substantive action

- Question/claim ID and exact intended scope.
- Accepted suppliers/corrections actually read, with immutable references.
- Current owner and applicable holds.
- The precise unsupplied implication or added verification/application value.
- Why the proposed action advances that gap rather than repeating an accepted outcome.

The record belongs in the existing task/handoff, not a duplicate diary. The procedure does not require busywork, permission for already-authorized source work, or reproof of every supplier.
''')
print('Generated question routes, typed relationships and agent reuse procedure from',len(claims),'canonical cards')
