# LANE3-FILESYSTEM-RESOURCE-DISPOSITION-02

FIVE-RESEARCH-LANES-20261015-01/revision1. Contributor: existing Codex lane3 integration coordinator01a1252c. Recipient: DotBridge01a139ec and the existing lane2/compiler owner01a133ec. Measured **15 October 2026, 09:49:05.224 Pacific (16:49:05.224Z)**. This is a bounded read-only filesystem/source-metadata disposition, not a build request, lease or cleanup proposal.

## Which filesystem produced the8.5MiB observation?

The original8688KiB was the **Available** column from `df -Pk /workspace /dev/shm`, executed inside this lane's **managed cloud Linux task**, cwd /workspace. It was not a Windows drive or phone measurement. That earlier command did not embed an exact-second timestamp; it belongs to the approximately16:30Z turn. Its source was printed as overlay, with32978704KiB capacity and31275912KiB used.8688KiB equals8.484375MiB.

Fresh harmless statvfs/mountinfo metadata identifies this observer as container nodename **27ace1dfd571**, managed cloud environment **ccarenv_b64_Y2NhcmVudl8yYTFkMzYzODA5MjQ4MTkxYTMwZmIzOWFhYWY3ODExMw**, app chat01a1252c on the durable host namespace. The latter is an app routing identity, not a physical-machine identity. Physical Linux-host/block-device identity is **UNESTABLISHED**.

Both /workspace and /workspace/Research-Commons are directories on the **same root overlay mounted at /**, mount ID52, mount source/type overlay, device **0:27**. Neither /workspace nor the repository is a separate mount. The device number is this container's namespace identifier, not a Windows volume serial or physical disk model.

| Exact fresh field | /workspace root overlay | /dev/shm |
|---|---:|---:|
| Filesystem/source | overlay / overlay | tmpfs / shm |
| Mountpoint; device | / ;0:27 | /dev/shm ;0:26 |
| Capacity bytes |33770192896|9441349632|
| Used bytes (blocks minus free blocks) |32027586560|0|
| Free bytes, including blocks unavailable to this task |1742606336|9441349632|
| Available bytes to task UID1000 |**7843840**|9441349632|
| Free minus available bytes |1734762496|0|
| Total/free inodes |2097152 /1794706|2305017 /2305016|

The refreshed overlay has **7.48046875MiB /7660KiB available**; its capacity is31.450943GiB, used29.828014GiB and total-free1.622929GiB. “Free” and “available” are different fields. The1,734,762,496B difference is observed; its cause—reservation, quota, policy or another backing-filesystem constraint—is **UNESTABLISHED**. I did not infer an ext4 reservation or a per-container disk quota. The decrease from the earlier Available reading is not attributed to any person or workload.

The export of33,770,192,896B total capacity is a filesystem view, **not proof of a32GiB task quota or the whole machine's disk capacity**. No quota option was visible in this overlay mount's reported options. That absence does not prove quota absence. Account/project/container/underlying-volume disk-quota counters and their enforcement remain **UNESTABLISHED**; no quota tool, privileged device query or configuration operation was attempted.

## Other already-visible limits

The current observer's cgroup-v2 memory.max is **17179869184B (16GiB)**, memory.high=max, sampled memory.current=56627200B; memory.events had zero high/max/OOM/kill counters. cpu.max is400000/100000. These describe this current observer's visible cgroup, not the paused compiler's admitted profile. They do not release the historical4GiB stop or prove its cause.

Inherited observer RLIMIT_FSIZE/AS/DATA/CPU soft/hard values were infinity. Those are not disk-quota counters and do not authorize an unbounded compiler. Future guard limits must be explicit in its approved configuration.

/dev/shm is an empty **memory-backed tmpfs**, capacity9441349632B (8.792942GiB). It is not another desktop disk or an already-admitted compiler location. Moving/staging there would need its own actual owner/exclusive/resource disposition; none was performed. The historical aggregate recipe's greater-than11GiB launch reserve is not met by either current overlay availability or this tmpfs's total capacity. That historical aggregate recipe is not automatically the budget for a new narrow CM-T02 check.

## Safe already-authorized build root

**UNAVAILABLE in the evidence held here.** The existing owner has now actually returned [6197402149](https://github.com/Sodelin/Research-Commons/issues/1#issuecomment-6197402149), and its app final was read. It retains the historical paused compiler-owner role and explicitly reports the current executor/host pin, isolated exclusive build workspace/ref/lease, resource continuation/run-config and approved finite target as unavailable.

The owner's **source** worktree is /workspace/Research-Commons, branch work, reported HEAD39c9181a61928c593c5c3a51e511aeb99f610db2, with its disjoint lane2 draft prefix. This does not establish its active build root, its current filesystem capacity or an accepted compiler lease. Identical /workspace path strings across chats do not authenticate that they share this measured filesystem. This lane's own restored source checkout is HEADfc0f1535 on codex/lean-rust-parity-cloud-20261010 and has the overlay measurement above.

Exact unavailable fields are:
1. The actual execution host/container and **exact mounted build root**, with current exclusive owner/lease.
2. That root's current available capacity and applicable volume/task/cgroup/guard limits.
3. A reviewed finite source/import/companion context and actual run configuration accepted by that same existing owner.

Nolan's human authorization for requested checking through that workflow is already received. No repeated authorization or duplicate owner inquiry was sent. The parent's existing reconciliation remains pending. Desktop free space cannot fill these missing fields: no accepted desktop compiler root/owner/lease/capacity/quota binding is held here, and no desktop drive query, arbitrary D: path selection, enrollment or connection was performed.

If the old dependency plan is later admitted,3504 remains its preserved interrupted boundary. It is not automatically a CM-T02 prerequisite. No safe location is manufactured from a large free-space number.

## Newly returned CM-T02 source: declared closure disposition

This reconciles LANE2-ACTUAL-SOURCE-RELAY-03 and the existing source-review request due17:00Z. **QUALIFIED DECLARED-SOURCE INTAKE ONLY; COMPILER ADMISSION BLOCKED.** I independently byte-hashed all three full public Lean code blocks, without importing/parsing/elaborating them or writing them into another source workspace:

| Source | Bytes / SHA256 | Literal imports |
|---|---|---|
|CMFoundations.lean|2824 /173f00d1871656a016bc4593bae06030914dc161985d3b6df0aa89d667164073|G4ActualSparseCertificateExistence; Mathlib.Tactic.Ring; Mathlib.Tactic.Linarith|
|CMSeparation.lean|7728 /6504523aee4ba61a2184f327b17d6299cec85ba72935dbba235b65d99a927135|CMFoundations; Mathlib.Tactic.NormNum|
|CMInterfaceAudit.lean|1010 /2ba5d889bfdbf641e438c6a47d98bfa36b37392073661ffbc0f9a617e0613211|CMSeparation|

The declared local order is Foundations→Separation→InterfaceAudit. These are uncommitted author-owned source with independent source review, actual API/type/axiom and execution still pending; no immutable source commit or new compiled supplier is claimed.

I made one targeted existing-supplier read, not a source/object scan: source9ea04cbe390030381624d25b20be10751dff62f75d5d6e7752b88b9599a46418 exists byte-exact in the historical1613 packet's source-store at7239e89dea5caad68a54227cee3b44a7d9b96389;14000B/Gitblob b6d92620f3feabb8e0e3fa18186141ad1aa9c815. Its old UNCOMPILED draft header is historical source text, not a new downgrade of that packet's later acceptance.

Its literal imports are G4ActualObservableBankCertificate plus Mathlib.Algebra.Polynomial.RuleOfSigns, .Basis, .FieldDivision, Mathlib.Analysis.Polynomial.Order, Mathlib.LinearAlgebra.FiniteDimensional.Lemmas and .Dimension.Constructions. Thus the new authored module reaches a real physical-observable-bank and polynomial/linear-algebra dependency closure. Mathematical abstraction of CM-T02 does **not** prove a tiny, ready or cache-compatible compiler closure. No transitive source/object authentication was performed or inferred.

The requested endpoint is Astra.CommonMoment.cm_t02_cap_five_separation on positive finite supports, exactly moments0/1/3/6/10 and the stated cardinalities, without moment2 or an upper endpoint1. No contrary dependency/scope claim is established in the inspected literal headers. This is not full proof/API review or endorsement of tactic correctness.

CMInterfaceAudit contains proposed printed-type and selected-axiom requests only; there is no output. Those requests alone do not certify all owned declarations/generated helpers or a coherent Lake aggregate. Exact source-root/module routing, transitive import/source/compiler/companion context and actual selected/full owned audit remain named admission gates. No Lake hook/default target has been adopted.

The separately reported whole-fibre11524B/2a219ac8cbd3ae804b5542a31eff9e137476ff932077e3142fdc4e6660752ee7 remains hand/source-planning metadata, not a compiled dependency or new workload. Lane2 alone authors proof changes. Existing completed ownership/supplier lookups are not repeated.

## Actions and next step

Only bounded read-only filesystem/cgroup/process metadata, existing source/comment reads and stdlib byte hashing ran. No deletion, cleanup, move, permission/cache/bootstrap/installation change, alternative host connection, compiler/Lean/Lake/parser/helper build, new worker or Omni/Subspace work occurred. No physical desktop disk claim follows.

The exact blocker is missing **current admitted location/lease/resource/configuration**, compounded by this observer overlay's insufficient available storage. The already-routed owner return must bind those fields before later compilation. Lane3 can return the finite metadata admission disposition within10minutes after that concrete packet is complete; no compiler ETA can be given now.

### Exact observation payload

The following is the complete bounded statvfs/mount/cgroup observation. Overlay layer implementation paths were intentionally omitted by the reader; no credential/environment dump was made.

```json
[
  {
    "observed_utc": "2026-10-15T16:49:05.224023+00:00",
    "cwd": "/workspace",
    "container_hostname": "27ace1dfd571",
    "host_identity_scope": "executor/container nodename; physical host identity not established"
  },
  {
    "path": "/workspace",
    "st_dev": 27,
    "device_major_minor": "0:27",
    "block_size": 4096,
    "fragment_size": 4096,
    "blocks": 8244676,
    "free_blocks": 425441,
    "available_blocks": 1915,
    "capacity_bytes": 33770192896,
    "used_bytes": 32027586560,
    "free_bytes_including_unavailable": 1742606336,
    "available_bytes_to_task": 7843840,
    "free_minus_available_bytes": 1734762496,
    "inode_total": 2097152,
    "inode_free": 1794706,
    "inode_available": 1794706,
    "statvfs_flags": 4096
  },
  {
    "path": "/workspace/Research-Commons",
    "st_dev": 27,
    "device_major_minor": "0:27",
    "block_size": 4096,
    "fragment_size": 4096,
    "blocks": 8244676,
    "free_blocks": 425441,
    "available_blocks": 1915,
    "capacity_bytes": 33770192896,
    "used_bytes": 32027586560,
    "free_bytes_including_unavailable": 1742606336,
    "available_bytes_to_task": 7843840,
    "free_minus_available_bytes": 1734762496,
    "inode_total": 2097152,
    "inode_free": 1794706,
    "inode_available": 1794706,
    "statvfs_flags": 4096
  },
  {
    "path": "/",
    "st_dev": 27,
    "device_major_minor": "0:27",
    "block_size": 4096,
    "fragment_size": 4096,
    "blocks": 8244676,
    "free_blocks": 425441,
    "available_blocks": 1915,
    "capacity_bytes": 33770192896,
    "used_bytes": 32027586560,
    "free_bytes_including_unavailable": 1742606336,
    "available_bytes_to_task": 7843840,
    "free_minus_available_bytes": 1734762496,
    "inode_total": 2097152,
    "inode_free": 1794706,
    "inode_available": 1794706,
    "statvfs_flags": 4096
  },
  {
    "path": "/dev/shm",
    "st_dev": 26,
    "device_major_minor": "0:26",
    "block_size": 4096,
    "fragment_size": 4096,
    "blocks": 2305017,
    "free_blocks": 2305017,
    "available_blocks": 2305017,
    "capacity_bytes": 9441349632,
    "used_bytes": 0,
    "free_bytes_including_unavailable": 9441349632,
    "available_bytes_to_task": 9441349632,
    "free_minus_available_bytes": 0,
    "inode_total": 2305017,
    "inode_free": 2305016,
    "inode_available": 2305016,
    "statvfs_flags": 4096
  },
  {
    "selected_mounts": [
      {
        "mount_id": "52",
        "parent_id": "37",
        "device_major_minor": "0:27",
        "mount_root": "/",
        "mountpoint": "/",
        "mount_options": "rw,relatime",
        "filesystem": "overlay",
        "source": "overlay",
        "superblock_options": "overlay layer paths omitted; quota fields only below",
        "overlay_quota_related_options": []
      },
      {
        "mount_id": "56",
        "parent_id": "54",
        "device_major_minor": "0:26",
        "mount_root": "/",
        "mountpoint": "/dev/shm",
        "mount_options": "rw,relatime",
        "filesystem": "tmpfs",
        "source": "shm",
        "superblock_options": "rw",
        "overlay_quota_related_options": []
      }
    ]
  },
  {
    "proc_self_cgroup": "0::/"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/memory.max",
    "exists": true,
    "value": "17179869184"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/memory.high",
    "exists": true,
    "value": "max"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/memory.current",
    "exists": true,
    "value": "56627200"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/memory.swap.max",
    "exists": true,
    "value": "max"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/memory.events",
    "exists": true,
    "value": "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/pids.max",
    "exists": true,
    "value": "max"
  },
  {
    "cgroup_file": "/sys/fs/cgroup/cpu.max",
    "exists": true,
    "value": "400000 100000"
  }
]
```
