#!/bin/sh
# Mandatory OUTER entrypoint for every proposed new native source context.
# This script has no admission override: a claimed flag or environment value
# does not bind an authenticated recipient, controller sequence or first writer.
# No Lake/config loader, compiler, native child, runtime or record file is opened.
# A future owner-bound implementation requires separately reviewed source.
printf '%s\n' 'REFUSED: native first-persistence writer/controller binding is UNBOUND; Lake was not started.' >&2
exit 78
