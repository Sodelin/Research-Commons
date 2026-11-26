"""Compare exact-contract Lean addon compilation from the same built checkpoint."""
import json, os, statistics, subprocess, sys, tempfile, time
from pathlib import Path

lean, baseline = map(lambda p: str(Path(p).resolve()), sys.argv[1:])
src = Path(baseline)
routes = {
    "direct": ["EfficiencyBranchWidth", "EfficiencyGridMinorEnd"],
    "reuse": ["GridMinorCross", "CommonConnectedCut", "GridMinorAssembly",
              "SeparateCrossCoordinates", "GridMinorObstruction"],
}
result = {route: [] for route in routes}
with tempfile.TemporaryDirectory() as work:
    for round_number in range(5):
        order = list(routes)
        if round_number % 2:
            order.reverse()
        for route in order:
            target = Path(work) / f"{round_number}-{route}"
            target.mkdir()
            env = dict(os.environ, LEAN_PATH=f"{target}:{src}")
            start = time.monotonic()
            for module in routes[route]:
                subprocess.run([lean, "-o", str(target / f"{module}.olean"),
                                f"{module}.lean"], cwd=src, env=env, check=True,
                               stdout=subprocess.DEVNULL)
            result[route].append(round(time.monotonic() - start, 3))
print(json.dumps({"schema": "commons.proofbridge.addon-replay-comparison.v1",
                  "measures": "new Lean module compilation from warm shared base; not authoring",
                  "shared_module": "CappedMinorBranchCross",
                  "route_modules": routes,
                  "seconds": result, "median_seconds": {
                      r: statistics.median(times) for r, times in result.items()
                  }}, indent=2))
