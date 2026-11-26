# Exact bounded graph observations, version 1

Inputs are two UTF-8 JSON objects. Unknown fields, duplicate keys, noninteger
numeric values, and malformed vertices/masks are rejected.

- Request: `{schema, domain, observations, query}`. Schema is
  `proofbridge.simple-graph-observation.v1`. Domain is
  `{kind:"all_labeled_simple_undirected", n}` for integer `0 ≤ n ≤ 6`.
  Vertex IDs are `0..n-1`; edges are unordered pairs written with increasing
  endpoints. Observations (at most 64) are `{feature, eq}`, with the natural
  equality value in the range of each feature (`edge`: 0–1,
  `degree`: 0–n-1, `edge_count`: 0–n(n−1)/2). Feature object fields:
  `{kind:"edge",uv:[u,v]}`, `{kind:"degree",v}`, or `{kind:"edge_count"}`.
  Query is `{kind:"feasible"}` or `{kind:"identify",target:feature}`.
- Certificate: `{request_sha256,kind,...}`. SHA-256 is over the request
  serialized with recursively sorted keys, no structural whitespace, ASCII
  escapes and an unadorned UTF-8 byte string (no BOM or newline). JSON mask
  bits are in the edge order `(0,1),(0,2),...,(n-2,n-1)`, least
  significant bit first.

| Certificate kind | Additional fields | Verification | Result |
|---|---|---|---|
| feasible_witness | witness mask | Check each observation on witness | feasible |
| empty_replay | none | Check every mask and find no observing model | empty |
| identified_replay | witness mask | Check observing witness and exclude every alternative target value over all masks | identified and value |
| ambiguity_pair | left and right masks | Check observations on both graphs and unequal exact target values | ambiguous and values |
| unknown | none | No mathematical assertion | unknown |

Witness and ambiguity do not depend on search completeness. Empty and
identified are valid only in the declared finite universe. In particular,
`ambiguous` is a counterexample to identification, not evidence of
infeasibility; `empty` is not a successful identification (nonvacuity
policy). An SMT result, incomplete enumeration, or externally reported
counterexample is only a candidate until checked. Rejection is not a
mathematical result. Exact Python replay is not Lean kernel acceptance.

For later scale-up keep this semantic boundary and replace complete replay
with a checked coverage artifact rather than a boolean completeness flag:
for example, a split tree explicitly covering both branches at every free
edge, with each prune justified by a checked contradiction to an exact
observation or to the requested alternative target. Prove the exhaustive
split theorem in Lean before admitting those receipts as Lean verified.
Separate adapters may handle graph reindexing or isomorphism; v1 treats
the labels as part of the request and does not quotient by isomorphism.

Run `python graph_certificate.py REQUEST CERTIFICATE` for the CLI;
`python -m unittest -v` validates the prototype.
