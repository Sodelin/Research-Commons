#!/usr/bin/env python3
"""One-shot transport to the existing native Z3 engine, without z3py."""

import ctypes
import hashlib
import json
from pathlib import Path
import resource
import sys


LIBRARY = Path("/usr/lib/aarch64-linux-gnu/libz3.so.4")


def main():
    # Android's Termux launcher cannot start under a 512 MiB virtual-address
    # cap. Apply the memory cap inside the existing glibc container before
    # loading the solver; the outer process still has CPU/file/wall caps.
    resource.setrlimit(resource.RLIMIT_CPU, (3, 3))
    resource.setrlimit(resource.RLIMIT_AS, (536870912, 536870912))
    resource.setrlimit(resource.RLIMIT_FSIZE, (65536, 65536))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    library = ctypes.CDLL(str(LIBRARY))
    library.Z3_get_full_version.argtypes = []
    library.Z3_get_full_version.restype = ctypes.c_char_p
    version = library.Z3_get_full_version().decode("utf-8")
    if len(sys.argv) == 2 and sys.argv[1] == "--probe":
        print(json.dumps({
            "engine": "Z3 native C API",
            "version": version,
            "library_path_in_container": str(LIBRARY),
            "library_sha256": hashlib.sha256(LIBRARY.read_bytes()).hexdigest(),
            "python": sys.version,
            "rlimit_cpu": resource.getrlimit(resource.RLIMIT_CPU),
            "rlimit_as": resource.getrlimit(resource.RLIMIT_AS),
            "rlimit_fsize": resource.getrlimit(resource.RLIMIT_FSIZE),
        }, sort_keys=True))
        return
    if len(sys.argv) != 2:
        raise SystemExit("Pass exactly one SMT-LIB2 path, or --probe")
    query = Path(sys.argv[1]).read_bytes()
    if len(query) > 16384 or b"\0" in query:
        raise SystemExit("Refused oversized input or embedded NUL")
    pointer = ctypes.c_void_p
    library.Z3_mk_config.argtypes = []
    library.Z3_mk_config.restype = pointer
    library.Z3_del_config.argtypes = [pointer]
    library.Z3_mk_context.argtypes = [pointer]
    library.Z3_mk_context.restype = pointer
    library.Z3_del_context.argtypes = [pointer]
    library.Z3_eval_smtlib2_string.argtypes = [pointer, ctypes.c_char_p]
    library.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    config = library.Z3_mk_config()
    if not config:
        raise SystemExit("Z3_mk_config returned null")
    context = library.Z3_mk_context(config)
    library.Z3_del_config(config)
    if not context:
        raise SystemExit("Z3_mk_context returned null")
    try:
        # The returned string belongs to the context; copy it before deletion.
        output = library.Z3_eval_smtlib2_string(context, query)
        if output is None:
            raise SystemExit("Z3_eval_smtlib2_string returned null")
        sys.stdout.write(output.decode("utf-8"))
    finally:
        library.Z3_del_context(context)


if __name__ == "__main__":
    main()
