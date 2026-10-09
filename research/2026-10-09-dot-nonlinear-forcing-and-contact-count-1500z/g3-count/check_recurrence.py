"""Check integer arithmetic only. This is not a source or root solver."""
from functools import lru_cache
from pathlib import Path
import json

@lru_cache(None)
def bound(n, degree):
    return degree if n == 1 else 2 * degree + 1 + bound(n - 1, 2 * degree + 20)

rows = []
for n in range(1, 21):
    closed = 60 * (2 ** (n - 1) - 1) - 39 * (n - 1)
    assert bound(n, 0) == closed
    rows.append({"terms": n, "bound": closed})

result = {
    "claim": "Integer recurrence arithmetic only; no root or source computation",
    "checked_n": list(range(1, 21)),
    "rows": rows,
}
Path(__file__).with_name("RECURRENCE-CHECK.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
print("PASS: recurrence/closed form for n=1..20; integer arithmetic only")
