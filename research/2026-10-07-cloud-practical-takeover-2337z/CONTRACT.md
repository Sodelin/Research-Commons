# Exact scalar count contract and C ABI

Status: implementation contract, inherited mathematics. Authority:
[rc_count.h](include/rc_count.h); Python reference
[`count_certificate.py` at c9a6934](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py),
SHA256 `4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4`.
The earlier [independent mathematics/code acceptance](../2026-10-07-cloud-independent-auditor-1616z/COUNT-CERTIFICATE-REVIEW.md)
is acceptance of that reference, not this new port.

For exact rationals a>=0 and 0<epsilon<1, let t_k=a^k/k! and
S_K=sum_{k=0}^K t_k. Inspect K=0,1,... in that order. The first qualifying
cutoff satisfies K+2>=2a and delta=2t_(K+1)/(S_K+2t_(K+1))<=epsilon.
Return exactly the reference's fields `status`, `law`, `a`, `epsilon`, `K`,
`S`, `T`, `U`, `delta`, `inspected`; T=t_(K+1), U=S_K+2T and inspected=K+1.
Optional weights are precisely t_k/S_K for k=0,...,K. They sum to one.
The law tag is `normalized_prefix`. Residual-lumped truncation is a distinct
law and is never substituted.

A finite step budget counts inspected candidate cutoffs. Exhaustion returns
`RESOURCE_LIMIT`, `law`, normalized `a`/`epsilon`, `inspected`, `next_K`,
with no weights or scientific negative conclusion. Budget zero inspects
nothing, including at a=0. Unlimited mode preserves the mathematical search;
it has no promised uniform runtime or intermediate arithmetic size. At the
otherwise unreachable uint64 inspection limit the C receiver returns
RESOURCE_LIMIT with an additional `resource_reason=UINT64_COUNTER`, instead
of wrapping counters. Fractions/cutoff arithmetic remain exact.

The ABI returns 0 for CERTIFIED or RESOURCE_LIMIT, 2 for INVALID_INPUT JSON,
and 3 for allocation/internal failure. `char **out_json` must be non-NULL;
it is cleared before work. Returned JSON is caller-owned and released only
with `rc_count_free`, which accepts NULL. Flags `has_limit` and
`include_weights` must each be 0 or 1. Unlimited mode ignores max_steps.
The CLI maps ABI codes to exit codes and prints complete JSON only when
available. It rejects duplicate/unknown flags and uint64 parse overflow.
JSON member order is immaterial; complete decoded objects must match.

The input parser deliberately supports a bounded subset of Python Fraction's
text syntax: ASCII `-?[0-9]{1,78}(/[0-9]{1,78})?`, positive nonzero denominator,
at most158 raw characters and at most256 raw numerator/denominator bits.
Leading zeros and negative zero are accepted then normalized. No plus sign,
whitespace, decimal, exponent, Unicode digit, negative denominator or trailing
content is accepted. Grammar/length checks precede GMP integer conversion;
bounded raw integers and positive denominator checks precede rational
canonicalization. Output uses Python str(Fraction) form: an integer when the
denominator is one, otherwise reduced numerator/positive-denominator.

The JSON builder checks size arithmetic and realloc failure, frees partial
output and returns3/NULL; a focused linker-wrapped allocation control exercises
this path. GMP itself uses its default allocation policy: GMP allocation
failure terminates the process. This library does not install invasive global
allocator hooks or pretend that such a failure produced a result. External
CPU/wall/memory limits and any failed process must be recorded as execution
failure/UNKNOWN, never as a count certificate. Bounded text allocation does
not establish a universal arithmetic-memory/runtime bound.

Only this scalar component is exposed by this ABI. A future source backend,
statistical mean band and complete interval cover each need their own typed
contracts and independent checks; sharing the library does not discharge
those obligations.
