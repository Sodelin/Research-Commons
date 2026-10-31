# Append-only historical correction: parallel cap repair

The accepted literal cap variant remains9517bd6aa577d8d832562c3cca6de5ecd9ed1c4284ddb809ea8db18d645350d1, public acceptance f5ccf9cefee1f5e42320513df84227d3259160c1. Its successful source and two direct named checks are unaffected.

A later sole-compiler checkpoint, relayed by the parent, reveals the separately published owner repair0d98205c9954c6686a081dec0f121422e0b90c30f63bed8c9805e11e53b3cbd0 was checked ONCE before the cancellation/skip instruction reached the compiler. It failed at125:6 with a type mismatch, exit1; no object, named or owned acceptance. No retry occurred after cancellation. Compiler holds CANCELLED-NO-RETRY.json; that receipt has not been independently materialized in this packet.

Thus historical “uncompiled/never compiled” wording for0d982 in the f5cc acceptance packet is superseded by **failed once, cancelled, superseded, not accepted**. Do not attribute the9517 passing receipt to0d982 and do not retry0d982. Original source bytes and historical packets remain unchanged.
