# Exact interrupted-log repair before fresh3036 retry

Batch065 did not launch Lean. The pinned helper printed its resource policy,
then refused to open `3036.stdout` exclusively because the previous interrupted
invocation's empty file still occupied that path. The actual guard records
exit1/no resource stop after7.507seconds. Its exact traceback, zero-event capture
and detached finish remain preserved; there is no new module receipt or object.

The prior064 source and both empty logs had already been copied into the public
checkpoint. The repair now moves only those two exact empty owned files into
`/workspace/scratch/astra-support-external-0840/preserved-interrupted-3036-before-066`.
It preserves additional public copies and exact move/hash records in
`support0830/evidence/interrupted-3036-exclusive-log-repair/REPAIR.json`
(SHA25663cff91c6e0e59ac5cf39e533113236cdfeee03a1fd0282b827ad3e3e47fe78d).
No source, compiler, object, unrelated file or resource limit changed.

After this closed checkpoint, batch066 can run exactly one fresh unchanged3036
module under the same6GiB virtual/4GiB physical900wall/600CPU guard. Neither the
original064 wall-limit failure nor the065 prelaunch refusal is promoted to a
successful compilation. The original042/057/059 outer outcomes remain UNKNOWN.
