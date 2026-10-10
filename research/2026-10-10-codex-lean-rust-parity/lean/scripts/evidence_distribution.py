"""Lossless, byte-authenticated distribution of large generated evidence."""
from __future__ import annotations
import gzip
import hashlib
from pathlib import Path
import shutil
from check_core import sha

LIMIT = 50_000_000


def verify_distribution(base: Path, row: dict) -> None:
    archive = base / row["path"]
    assert archive.is_file() and sha(archive) == row["sha256"]
    assert archive.stat().st_size == row["bytes"]
    digest = hashlib.sha256()
    count = 0
    with gzip.open(archive, "rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
            count += len(block)
    assert count == row["restored_bytes"]
    assert digest.hexdigest() == row["restored_sha256"]


def distribute_file(source: Path, base: Path, relative: Path, *, force_gzip: bool = False) -> dict:
    destination = base / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    original_hash = sha(source)
    original_bytes = source.stat().st_size
    if original_bytes <= LIMIT and not force_gzip:
        shutil.copyfile(source, destination)
        assert sha(destination) == original_hash
        return {"path": str(relative), "sha256": original_hash, "bytes": original_bytes}
    archive = Path(str(destination) + ".gz")
    if not archive.exists():
        temporary = Path(str(archive) + ".incomplete")
        with source.open("rb") as raw, temporary.open("xb") as target:
            with gzip.GzipFile(filename="", mode="wb", fileobj=target, mtime=0) as zipped:
                shutil.copyfileobj(raw, zipped, 1024 * 1024)
        temporary.replace(archive)
    row = {"path": str(archive.relative_to(base)), "sha256": sha(archive),
           "bytes": archive.stat().st_size, "encoding": "gzip",
           "restored_path": str(relative), "restored_sha256": original_hash,
           "restored_bytes": original_bytes}
    verify_distribution(base, row)
    assert sha(source) == original_hash and source.stat().st_size == original_bytes
    return row
