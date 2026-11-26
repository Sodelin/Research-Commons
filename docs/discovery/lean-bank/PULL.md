# Pull and check just the chosen modules

The [source lock](source-pull.lock.json) lists **four** files. Each row carries repository, Git commit, path, exact Git blob and destination. The connector fetched those four exact Git sources into an empty directory; no Drive access and no large Lean library were required. Copy [CheckBank.lean](CheckBank.lean) into the same directory and run:

```
python check-source-pull.py /path/to/that/directory /absolute/path/to/pinned/lean
```

The runner checks the blob bytes and compiler commit, builds that subset in dependency order, and imports two exact named theorems in a separate Lean consumer. The receipt links the precise printed statements and their hashes. The runner has no network side effects; acquisition can use the GitHub connector or equivalent pinned copies, and compilation is a separately chosen step. The linked catalog lock locates artifacts; it is not a complete external package build graph. Approved public external sources can be inspected by path without executing or installing anything. Never execute a third-party package merely because it is indexed.
