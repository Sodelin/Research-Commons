#!/usr/bin/env python3
"""New ONLINE Rust-job counter adapter for the unchanged inherited guard.

Reuse its captured hash-checked supervisor/limits/floors/cleanup. Resolve
actual current cgroup membership against actual mount information. No
controller setting/migration, invented counter or unbounded fallback.
"""
import hashlib
from pathlib import Path, PurePosixPath
import re
import sys
import types

HERE = Path(__file__).resolve().parent
ORIGINAL = HERE.parent / "2026-10-13-astra-unified-solver-0645z/guard.py"
ORIGINAL_SHA256 = "f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3"
BASE = PurePosixPath("/sys/fs/cgroup")


def absolute(value):
    value = re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), value)
    path = PurePosixPath(value)
    if (not path.is_absolute() or ".." in path.parts or "\\" in value
            or "\n" in value or value.endswith(" (deleted)")):
        raise ValueError("unsupported cgroup path")
    return path


def candidates(memberships, mounts):
    groups = []
    for line in memberships.splitlines():
        fields = line.split(":", 2)
        if len(fields) != 3:
            continue
        identity, controllers, group = fields
        if identity == "0" and controllers == "":
            groups.append(("v2", absolute(group)))
        elif "memory" in controllers.split(","):
            groups.append(("v1", absolute(group)))
    found = []
    for line in mounts.splitlines():
        left, separator, right = line.partition(" - ")
        fields, tail = left.split(), right.split()
        if not separator or len(fields) < 5 or len(tail) < 3:
            continue
        if tail[0] == "cgroup2":
            kind, filename = "v2", "memory.current"
        elif tail[0] == "cgroup" and "memory" in tail[2].split(","):
            kind, filename = "v1", "memory.usage_in_bytes"
        else:
            continue
        root, point = absolute(fields[3]), absolute(fields[4])
        if point != BASE and BASE not in point.parents:
            raise ValueError("cgroup mount outside supported root")
        for group_kind, group in groups:
            if group_kind != kind:
                continue
            try:
                relative = group.relative_to(root)
            except ValueError:
                continue
            entry = (kind+"_current_group", str(point/relative/filename))
            if entry not in found:
                found.append(entry)
    return found


def self_test():
    mount2 = "10 9 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw"
    assert candidates("0::/system.slice/runner.service", mount2) == [
        ("v2_current_group", "/sys/fs/cgroup/system.slice/runner.service/memory.current")]
    assert candidates("0::/", mount2) == [("v2_current_group", "/sys/fs/cgroup/memory.current")]
    bind = "10 9 0:1 /pool/job /sys/fs/cgroup rw - cgroup2 cgroup rw"
    assert candidates("0::/pool/job/sub", bind) == [("v2_current_group", "/sys/fs/cgroup/sub/memory.current")]
    assert candidates("0::/other", bind) == []
    mount1 = "10 9 0:1 / /sys/fs/cgroup/memory rw - cgroup cgroup rw,memory"
    assert candidates("4:memory:/job", mount1) == [
        ("v1_current_group", "/sys/fs/cgroup/memory/job/memory.usage_in_bytes")]
    assert candidates("4:cpu:/job", mount1) == []
    assert candidates("4:memory:/job", mount2) == []
    assert candidates("broken", mount2) == []
    assert candidates("0::/job", mount2+"\n"+mount2) == [
        ("v2_current_group", "/sys/fs/cgroup/job/memory.current")]
    for group, mount in [
        ("0::/../escape", mount2),
        ("0::/job (deleted)", mount2),
        ("0::/job", mount2.replace("/sys/fs/cgroup", "/tmp/cgroup")),
        ("0::/job", mount2.replace(" / /sys", " /../x /sys"))]:
        try:
            candidates(group, mount)
        except ValueError:
            pass
        else:
            raise AssertionError("unsupported path admitted")
    print('{"cgroup_parser_source_controls":13,"all_passed":true,"live_counter_verified":false}')


def main():
    if sys.argv[1:] == ["--self-test"]:
        self_test()
        return 0
    own_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    original = ORIGINAL.read_bytes()
    if hashlib.sha256(original).hexdigest() != ORIGINAL_SHA256:
        raise ValueError("original guard source identity changed")
    module = types.ModuleType("inherited_guard")
    module.__file__ = str(ORIGINAL)
    exec(compile(original, str(ORIGINAL), "exec"), module.__dict__)

    def state(path):
        locations = candidates(Path("/proc/self/cgroup").read_text(),
                               Path("/proc/self/mountinfo").read_text())
        selected = [(kind, Path(name)) for kind, name in locations if Path(name).is_file()]
        if not selected:
            raise RuntimeError("required actual-membership cgroup memory counter unavailable")
        kind, counter = selected[0]
        raw = counter.read_text().strip()
        if not raw or not raw.isascii() or not raw.isdigit():
            raise RuntimeError("invalid actual cgroup memory counter")
        mem = dict(row.split(":", 1) for row in Path("/proc/meminfo").read_text().splitlines())
        return dict(disk_free=module.shutil.disk_usage(path).free,
                    ram_available=int(mem["MemAvailable"].split()[0])*1024,
                    cgroup_memory=int(raw), cgroup_counter_kind=kind,
                    cgroup_counter_path=str(counter), adapter_sha256=own_hash)

    module.state = state
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
