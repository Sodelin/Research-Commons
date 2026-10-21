#!/usr/bin/env python3
"""New ONLINE Rust-job adapter for the unchanged inherited guard.

The process supervisor, limits, floors, polling/cleanup and receipts are reused
from captured hash-checked source. Only counter acquisition gains a cgroup-v1
root-memory alternative. Missing/invalid counters refuse before child launch.
"""
import hashlib
from pathlib import Path
import types

HERE = Path(__file__).resolve().parent
ORIGINAL = HERE.parent / "2026-10-13-astra-unified-solver-0645z/guard.py"
ORIGINAL_SHA256 = "f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3"
V2 = Path("/sys/fs/cgroup/memory.current")
V1 = Path("/sys/fs/cgroup/memory/memory.usage_in_bytes")


def main():
    own_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    original = ORIGINAL.read_bytes()
    if hashlib.sha256(original).hexdigest() != ORIGINAL_SHA256:
        raise ValueError("original guard source identity changed")
    module = types.ModuleType("inherited_guard")
    module.__file__ = str(ORIGINAL)
    exec(compile(original, str(ORIGINAL), "exec"), module.__dict__)
    old_state = module.state

    def state(path):
        if V2.is_file():
            result = old_state(path)
            result.update(cgroup_counter_kind="v2_root_memory_current",
                          cgroup_counter_path=str(V2), adapter_sha256=own_hash)
            return result
        # Fixed known root controller, with actual /proc membership evidence.
        # Do not fabricate a counter, silently omit it, or reclassify refusal.
        memberships = Path("/proc/self/cgroup").read_text().splitlines()
        admitted = any(len(parts := line.split(":", 2)) == 3 and
                       "memory" in parts[1].split(",") for line in memberships)
        mounts = Path("/proc/self/mountinfo").read_text().splitlines()
        mounted = False
        for line in mounts:
            left, separator, right = line.partition(" - ")
            fields = left.split()
            tail = right.split()
            if (separator and len(fields) >= 5 and fields[4] == "/sys/fs/cgroup/memory"
                    and len(tail) >= 3 and tail[0] == "cgroup"
                    and "memory" in tail[2].split(",")):
                mounted = True
        if not admitted or not mounted or not V1.is_file():
            raise RuntimeError("required cgroup memory counter unavailable")
        raw = V1.read_text().strip()
        if not raw or not raw.isascii() or not raw.isdigit():
            raise RuntimeError("invalid cgroup-v1 memory counter")
        mem = dict(row.split(":", 1) for row in Path("/proc/meminfo").read_text().splitlines())
        return dict(disk_free=module.shutil.disk_usage(path).free,
                    ram_available=int(mem["MemAvailable"].split()[0])*1024,
                    cgroup_memory=int(raw), cgroup_counter_kind="v1_root_memory_usage",
                    cgroup_counter_path=str(V1), adapter_sha256=own_hash)

    module.state = state
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
