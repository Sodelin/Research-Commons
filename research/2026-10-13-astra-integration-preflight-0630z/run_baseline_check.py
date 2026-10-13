"""Run only the inherited public-packet verifier, serially and with limits.

This authenticates stored evidence. It does not run Lean, Lake or Rust.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import resource
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PACKET = ROOT / "research/2026-10-12-dot-accepted-connected-union1613-1737z"
OUT = HERE / "evidence"
OUT.mkdir(exist_ok=True)
GIB = 1024**3
LIMITS = dict(address_space_bytes=2 * GIB, cpu_seconds=90, wall_seconds=120,
              output_file_bytes=16 * 1024**2, free_disk_floor_bytes=8 * GIB,
              available_ram_floor_bytes=GIB, cgroup_usage_stop_bytes=4 * GIB,
              sample_interval_seconds=0.5)


def observation():
    mem = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    return dict(free_disk_bytes=shutil.disk_usage(HERE).free,
                available_ram_bytes=int(mem["MemAvailable"].split()[0]) * 1024,
                cgroup_memory_bytes=int(Path("/sys/fs/cgroup/memory.current").read_text()))


def pressure(obs):
    if obs["free_disk_bytes"] < LIMITS["free_disk_floor_bytes"]:
        return "disk_floor"
    if obs["available_ram_bytes"] < LIMITS["available_ram_floor_bytes"]:
        return "ram_floor"
    if obs["cgroup_memory_bytes"] >= LIMITS["cgroup_usage_stop_bytes"]:
        return "cgroup_usage_stop"
    return None


def child_limits():
    resource.setrlimit(resource.RLIMIT_AS, (2 * GIB, 2 * GIB))
    resource.setrlimit(resource.RLIMIT_CPU, (90, 90))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024**2, 16 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    cmd = [sys.executable, "-I", "-B", str(PACKET / "verify_public_packet.py")]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    samples = [dict(elapsed_seconds=0, **observation())]
    stop = pressure(samples[0])
    child = None
    elapsed = time.monotonic()
    try:
        with (OUT / "baseline.stdout").open("wb") as stdout, (OUT / "baseline.stderr").open("wb") as stderr:
            if stop is None:
                child = subprocess.Popen(cmd, cwd=PACKET, stdout=stdout, stderr=stderr,
                                         start_new_session=True, preexec_fn=child_limits)
                while child.poll() is None:
                    obs = observation()
                    samples.append(dict(elapsed_seconds=time.monotonic() - elapsed, **obs))
                    stop = pressure(obs)
                    if time.monotonic() - elapsed > LIMITS["wall_seconds"]:
                        stop = "wall_limit"
                    if stop:
                        os.killpg(child.pid, signal.SIGTERM)
                        try:
                            child.wait(timeout=2)
                        except subprocess.TimeoutExpired:
                            os.killpg(child.pid, signal.SIGKILL)
                            child.wait()
                        break
                    time.sleep(LIMITS["sample_interval_seconds"])
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
        receipt = dict(schema="astra_bounded_public_evidence_check_v1", started_utc=started,
                       command=cmd, cwd=str(PACKET), limits=LIMITS, samples=samples,
                       elapsed_seconds=time.monotonic() - elapsed, guard_stop=stop,
                       exit_code=None if child is None else child.returncode,
                       child_peak_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024,
                       compiler_execution=False, native_execution=False,
                       verifier_sha256=hashlib.sha256((PACKET / "verify_public_packet.py").read_bytes()).hexdigest(),
                       runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       stdout_sha256=hashlib.sha256((OUT / "baseline.stdout").read_bytes()).hexdigest(),
                       stderr_sha256=hashlib.sha256((OUT / "baseline.stderr").read_bytes()).hexdigest())
        (OUT / "BASELINE-CHECK.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "samples"}, indent=2))
    return 0 if child is not None and child.returncode == 0 and stop is None else 1


if __name__ == "__main__":
    sys.exit(main())
