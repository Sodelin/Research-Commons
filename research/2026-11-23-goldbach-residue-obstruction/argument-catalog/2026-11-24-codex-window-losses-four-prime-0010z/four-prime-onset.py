"""Check the first cutoff-feasible four-prime endpoint in the reflected row."""

import json
import math
from mpmath import iv

iv.dps = 140


def integer_power_floor(k, numerator, denominator):
    target = 1 << (k * numerator)
    low, high = 0, 1 << (k * numerator // denominator + 1)
    while high-low > 1:
        mid = (low+high)//2
        if mid**denominator <= target:
            low = mid
        else:
            high = mid
    return low


def parameters(k):
    L = k * iv.ln(2)
    u = iv.exp(L/40)
    z = iv.exp(L * iv.sqrt(iv.ln(iv.ln(L))) / iv.ln(L))
    d = iv.exp(L * (799/iv.mpf(1520)))
    p = iv.exp(L * (21/iv.mpf(40)))
    return u, z, d, p


def odd_q_min(n):
    low = math.isqrt(n//4)+1
    return low if low % 2 else low+1


def floor_interval(x):
    a, b = int(x.a), int(x.b)
    if a != b:
        raise ArithmeticError("floor interval straddles an integer")
    return a


def proth_after(lower):
    """Construct a prime p=a2^t+1, with odd a<2^t and a Proth witness."""
    t = (lower.bit_length()+2)//2
    power = 1 << t
    a = (lower-1)//power+1
    a |= 1
    while a < power:
        p = a * power + 1
        assert p > lower
        for witness in (2, 3, 5, 7, 11, 13, 17):
            if pow(witness, (p-1)//2, p) == p-1:
                return {"prime": str(p), "odd_multiplier": str(a),
                        "two_power": t, "witness": witness}
        a += 2
    raise ArithmeticError("no Proth prime in this construction range")


def analyze():
    # N is too small to support four distinct odd primes for k<=7.
    assert (1 << 7) < math.prod((3, 5, 7, 11))
    excluded = {}
    for k in range(8, 363):
        u, z, d, _ = parameters(k)
        assert z.a > u.b
        ratio = d*z*z / (iv.mpf(3)*(1 << (k-2)))
        assert ratio.a > 1
        if k in (8, 361, 362):
            excluded[k] = str(ratio)

    k = 363
    n_target = 1 << k
    u, z, d, p = parameters(k)
    q_low = odd_q_min(n_target)
    n_max = n_target - q_low*(q_low+2)
    assert z.a > u.b
    assert (d*z*z).b < n_max
    assert (z**3).a > p.b
    assert (z*(d**(iv.mpf(3)/2))).a > n_max
    assert (d*z**3).a > n_max

    z_limit = floor_interval(z)
    root_d = integer_power_floor(k, 799, 3040)
    certificates = [proth_after(z_limit)]
    certificates.append(proth_after(int(certificates[-1]["prime"])))
    certificates.append(proth_after(root_d))
    certificates.append(proth_after(int(certificates[-1]["prime"])))
    q = [int(entry["prime"]) for entry in certificates]
    assert sorted(set(q)) == q
    for item, prime in zip(certificates, q):
        a, t, witness = int(item["odd_multiplier"]), item["two_power"], item["witness"]
        assert a % 2 == 1 and 0 < a < (1 << t)
        assert prime == a*(1 << t)+1 and pow(witness, (prime-1)//2, prime)==prime-1
    endpoint = math.prod(q)
    assert endpoint <= n_max
    assert min(q) > z_limit
    eligible = []
    for p_mark in q:
        for w in q:
            if p_mark == w:
                continue
            s = endpoint // (p_mark*w)
            r = w*s
            assert p_mark**40 <= 1 << (k*19)
            assert w**40 > 1 << k and s**40 > 1 << k
            assert r**40 > 1 << (k*21)
            if (p_mark*w)**1520 > 1 << (k*799):
                eligible.append((p_mark, w))
    assert eligible == [(q[2], q[3]), (q[3], q[2])]
    G = -sum((iv.ln(a)*iv.ln(b)/iv.ln(endpoint//a) for a,b in eligible), iv.mpf(0))
    return {
        "excluded_k_le": 362, "selected_exclusion_ratios": excluded,
        "first_cutoff_feasible_k": k, "endpoint": str(endpoint),
        "prime_certificates": certificates,
        "endpoint_over_N": str(iv.mpf(endpoint)/n_target),
        "eligible_ordered_p_w": [[str(a),str(b)] for a,b in eligible],
        "G_D_interval": str(G), "minimum_endpoint_over_N": str(d*z*z/n_target),
        "cofactor_pair_status": "unchecked",
    }


if __name__ == "__main__":
    print(json.dumps(analyze(), indent=2, sort_keys=True))
