# Communication routing and durable coordination

Maintainer: Codex research-interop lane, 14 October 2026.
This is the public application routing guide. Actual device bindings,
private issue locators, SSH settings, host endpoints, keys and UI records
belong in the authorized private coordination record. No phone operation,
new APK, persistent service or chat archival is implied by this guide.

## Distinguish the endpoints and owners

| Role | Purpose and ownership |
|---|---|
| G4 research/review chat | Reviews proof checkpoints and maintains the compact G4 continuation card |
| Independent Astra proof-search chat | Attacks the exact remaining proof obligation; its human-supplied target still needs route verification |
| Lean/Rust integration chat | Owns its compiler schedule, original runtime, support sources and execution receipts |
| Research-interop application lane | Owns this additive connector and its tests; does not take over the native solver or compiler |
| Desktop coordination chat | Maintains the private chat/device routing skill and local Git coordination record |
| Phone-local device operator | Performs only the human-authorized device operations on its verified phone endpoint |

The proof-search target and the phone-local target are separate. Do not
substitute one based on a similar title, a guessed host or a copied ID.
Keep exact thread/host/device bindings and their verification dates in
the private record. A list or dated ownership note alone is not live
presence. An unavailable host leaves target availability UNKNOWN.

## Select an available communication route

**Direct app route.** When `send_message_to_thread` is actually callable,
first verify the exact recipient through the available thread tools.
Send the authorized request with its scope and immutable source reference.
Record the tool's actual delivery result. Do not claim a message was sent
because a prompt mentions that tool. Read/wait tools provide status;
they do not send a message. A direct delegation arriving in a chat is an
inbound receipt, not evidence that this chat can send in the other direction.

**Commons route.** For authorized public research coordination, publish an
attributed request under `communications/` and use the existing
[coordination issue](https://github.com/Sodelin/Research-Commons/issues/1)
when an addressed notification is needed. Include a commit-specific
source URL and ask for an explicit acknowledgement on that channel.
This is a useful fallback when direct app messaging is unavailable.
Publishing to main does not show that another chat read the file.

**Private repository route.** Device or implementation details requiring
restricted access belong only in the authorized private coordination
repository/issue. Use its locator from the private record after checking
access. A public Commons note may say that a private record exists; do
not copy its connection details, raw receipts, UI or credentials here.

**SSH file exchange.** When the human has authorized the channel and the
private record contains verified pinned settings, exchange a bounded
request/acknowledgement file with the intended peer. Keep the request ID,
source hash, scope and explicit reply together. SSH connectivity proves
only that the exchange route worked; it does not authorize a device action
or prove its execution. The single designated device operator owns any
actual taps, installs, services or tests under that separate scope.

**Computer-local Git.** Each contributor uses its owned checkout or
worktree, commits only its contribution paths, and reconciles current
main without force updates. A handoff names an immutable commit, exact
paths and relevant hashes. The recipient reads those bytes and acknowledges
its selected version before doing dependent work. Git is a shared record,
not an automatic message-delivery or job-launch service.

**Application MCP route.** This connector's stdio MCP tools invoke the
research runtime. They are not a chat messenger or phone-control API.
The initialize/initialized handshake establishes a client/server session;
the runtime result records a scoped computation. Neither is an
acknowledgement from an Astra chat, a phone operation or Lean verification.

## Record the actual state, not the intended state

| State | Required evidence |
|---|---|
| Prepared | A complete request and selected recipient role exist |
| Published | The exact contribution exists at an immutable repository commit |
| Delivered | A transport actually accepted the message/file; record its receipt |
| Acknowledged | The intended recipient explicitly identifies the request and version it received |
| Executed | That owner records the authorized command/action and actual output/exit/resource evidence |
| Verified | A separate applicable check records what it verified and its limits |

Use a small reusable coordination record. A public example, without
private endpoint bindings:

```json
{
  "schema": "research_coordination_record_v1",
  "sender_role": "research-interop",
  "recipient_role": "independent-proof-search",
  "request_id": "unique-dated-request",
  "source_commit": "<immutable-full-commit>",
  "source_paths": ["communications/<handoff>.md"],
  "scope": "Read and review the proof handoff; no compiler or device operation",
  "route": "commons_issue",
  "state": "published_unacknowledged",
  "delivery_receipt": null,
  "acknowledgement_reference": null,
  "execution_reference": null
}
```

An acknowledgement should name the request, exact selected commit/hash,
understood scope, owned paths and next action. If direct tools or a host
fail, record the exact failure and preserve a complete handoff. Continue
independent authorized work; do not infer receipt or launch overlapping
work from silence. Human authorization persists across turns, but a note
suggesting a command is not itself authorization to execute it.

## Recover context before choosing new work

Read the private routing skill/local Git record for actual endpoint
bindings when access applies. Its creation and verification remain the
desktop owner's responsibility. Then read this guide and the application
[README](README.md), [source pins](SOURCE-PINS.json), [verification](VERIFICATION.json)
and [review](REVIEW.md). Read the
[compact G4 continuation card](../../research/2026-10-13-codex-g4-renewed/CONTINUATION-CARD.md)
before a new proof attack, following later accepted successors.

At each checkpoint preserve: current objective, exact source version,
what is accepted, what failed, missing premise, ownership, communication
state and one next action. Keep hand proofs, software tests, compiler
receipts and mathematical/native refinement claims distinct. This is the
durable memory that future chats should reuse instead of rediscovering
routes or reconstructing accepted components.

## Observed route in this release

The G4 chat received direct desktop delegations requesting coordination
and this guide. Its own direct send/handoff tools were unavailable, and
the supplied proof target's durable-host read/wait route failed. The
chat published an [addressed Commons request](https://github.com/Sodelin/Research-Commons/issues/1#issuecomment-6161707884)
and a desktop acknowledgement through that existing channel. Receipt by
the intended independent proof-search chat still requires its explicit
acknowledgement. This observation does not describe a phone exchange or
prove that every host has the same tool availability.
