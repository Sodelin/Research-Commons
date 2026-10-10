#!/usr/bin/env python3
"""Bounded literal natural-cell compiler/solver with source-admission gate.

Uses --request PATH --output NEWDIR --binary PATH [--expected-binary-sha256 SHA].
The complete chart is independently recompiled and checked by a pinned
Fraction helper. The shared native adapter supplies process limits, actual
start provenance and fresh-output preservation. MATRIX_WITNESS/EXCLUSION
never promotes SOURCE_ADMISSION_NOT_ESTABLISHED.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import native_component as component


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--expected-binary-sha256")
    args = parser.parse_args()
    try:
        result = component.execute(args.request, args.output, args.binary, args.expected_binary_sha256,
                                   operation="CHART")
    except (ValueError, OSError) as error:
        print(json.dumps({"schema": component.CHART_SCHEMA, "status": "REFUSED_REQUEST", "error": str(error),
                          "solver_called": False, "checker_called": False, "source_admission_verified": False}))
        raise SystemExit(1)
    print(json.dumps({"schema": component.CHART_SCHEMA, "status": result["status"], "output": str(args.output.absolute()),
                      "source_admission": result["source_admission"]}))
    raise SystemExit(result["exit_code"])


if __name__ == "__main__":
    main()
