#!/usr/bin/env python3
"""Check a caller-owned UTF-8 document from stdin without a source temp file.

Requires its expected SHA256 and the existing record codec/identity. The exact
input is encrypted before launching the unchanged full-context client. Native
exporter/controller origin and package/object acceptance remain separate.
"""
import argparse
from pathlib import Path
import sys
from online_capture import MEMORY_SOURCE_BOUND, run_memory_case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-sha256', required=True)
    parser.add_argument('--audit', action='append', required=True)
    parser.add_argument('--record-codec', type=Path, required=True)
    parser.add_argument('--codec-sha256', required=True)
    args = parser.parse_args()
    # One extra byte proves oversize without reading an unbounded input stream.
    source = sys.stdin.buffer.read(MEMORY_SOURCE_BOUND + 1)
    return run_memory_case(Path(__file__).resolve().parent, source,
        args.source_sha256, args.audit, args.record_codec, args.codec_sha256)


if __name__ == '__main__':
    raise SystemExit(main())
