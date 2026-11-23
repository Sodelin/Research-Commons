from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from math import fsum, gcd, isclose, isqrt, log


def arithmetic_tables(limit):
    least_prime = list(range(limit + 1))
    for prime in range(2, isqrt(limit) + 1):
        if least_prime[prime] == prime:
            for multiple in range(prime * prime, limit + 1, prime):
                if least_prime[multiple] == multiple:
                    least_prime[multiple] = prime

    phi = [0, 1] + [0] * (limit - 1)
    mu = [0, 1] + [0] * (limit - 1)
    distinct_factors = [0] * (limit + 1)
    prime_base = [0] * (limit + 1)
    for value in range(2, limit + 1):
        prime = least_prime[value]
        quotient = value // prime
        if quotient % prime == 0:
            phi[value] = prime * phi[quotient]
            distinct_factors[value] = distinct_factors[quotient]
        else:
            phi[value] = (prime - 1) * phi[quotient]
            mu[value] = -mu[quotient]
            distinct_factors[value] = 1 + distinct_factors[quotient]
        if quotient == 1 or prime_base[quotient] == prime:
            prime_base[value] = prime
    return phi, mu, distinct_factors, prime_base


def cell_types(mu, distinct_factors):
    names = ('unit', 'prime', 'squarefree semiprime', 'squarefree >=3 factors')
    return [names[min(count, 3)] if value else 'nonsquarefree cell'
            for value, count in zip(mu, distinct_factors)]


def divisors(value):
    for divisor in range(1, isqrt(value) + 1):
        if value % divisor == 0:
            yield divisor
            paired_divisor = value // divisor
            if paired_divisor != divisor:
                yield paired_divisor


def check_buckets(primary, independent):
    assert primary.keys() == independent.keys()
    for bucket, weights in primary.items():
        other = independent[bucket]
        assert len(weights) == len(other), bucket
        assert isclose(fsum(weights), fsum(other), rel_tol=1e-12, abs_tol=1e-10), bucket


def show_partition(actual, model, target, keys):
    print(f'{"modulus":10} {"cofactor cell":25} {"actual/N":>12} {"model/N":>12} '
          f'{"(actual-model)/N":>17} {"actual terms":>12} {"model terms":>12}')
    for modulus, bucket in keys:
        a, m = actual.get((modulus, bucket), []), model.get((modulus, bucket), [])
        a_sum, m_sum = fsum(a), fsum(m)
        print(f'{modulus:10} {bucket:25} {a_sum / target:12.9f} {m_sum / target:12.9f} '
              f'{(a_sum - m_sum) / target:17.9f} {len(a):12} {len(m):12}')


def replay(target, alpha, band):
    phi, mu, distinct_factors, prime_base = arithmetic_tables(target - 1)
    buckets = cell_types(mu, distinct_factors)
    logarithms = [0.0] + [log(value) for value in range(1, target)]
    powers = [(n, logarithms[base]) for n, base in enumerate(prime_base) if base]
    numerator, denominator = alpha.numerator, alpha.denominator

    actual, model = defaultdict(list), defaultdict(list)
    rows = []
    max_q = (denominator * (target - 1) - 1) // numerator
    if band == 'low':
        first_q = 2
        max_q = min(max_q, (denominator * target - 1) // (4 * numerator))
    else:
        first_q = 1
    for q in range(first_q, max_q + 1):
        if mu[q] == 0 or gcd(q, target) != 1:
            continue
        rows.append(q)
        endpoint = target - numerator * q // denominator - 1
        modulus = 'prime' if distinct_factors[q] == 1 else 'composite' if q > 1 else 'unit'
        for n, lambda_n in powers:
            if n > endpoint:
                break
            partner = target - n
            if mu[partner] == 0:
                continue
            cell, remainder = divmod(partner, q)
            weight = mu[q] * mu[partner] * lambda_n * (logarithms[q] - logarithms[partner])
            model[modulus, buckets[cell]].append(weight / phi[q])
            if remainder == 0:
                actual[modulus, buckets[cell]].append(weight)

    independent_actual, independent_model = defaultdict(list), defaultdict(list)
    row_types = {q: ('prime' if prime_base[q] == q else 'composite' if q > 1 else 'unit')
                 for q in rows}
    for n, lambda_n in powers:
        partner = target - n
        if mu[partner] == 0:
            continue
        for cofactor in divisors(partner):
            q = partner // cofactor
            if denominator * cofactor > numerator and q in row_types:
                weight = -mu[cofactor] * lambda_n * logarithms[cofactor]
                independent_actual[row_types[q], buckets[cofactor]].append(weight)

        for q in rows:
            if denominator * partner <= numerator * q:
                break
            cell = partner // q
            weight = -mu[q] * mu[partner] * lambda_n * log(partner / q) / phi[q]
            independent_model[row_types[q], buckets[cell]].append(weight)

    check_buckets(actual, independent_actual)
    check_buckets(model, independent_model)
    print(f'N={target} alpha={alpha} band={band} reduced squarefree moduli={len(rows)}')
    keys = sorted(actual.keys() | model.keys())
    show_partition(actual, model, target, keys)

    print()
    actual_totals, model_totals = defaultdict(list), defaultdict(list)
    for modulus, bucket in keys:
        actual_totals['all', bucket].extend(actual.get((modulus, bucket), []))
        model_totals['all', bucket].extend(model.get((modulus, bucket), []))
    assert not actual_totals.get(('all', 'nonsquarefree cell'))
    assert all(weight < 0 for weight in actual_totals.get(('all', 'squarefree semiprime'), ()))
    show_partition(actual_totals, model_totals, target,
                   [('all', bucket) for bucket in sorted({bucket for _, bucket in keys})])
    a_total, m_total = fsum(map(fsum, actual.values())), fsum(map(fsum, model.values()))
    print(f'{"total":10} {"":25} {a_total / target:12.9f} {m_total / target:12.9f} '
          f'{(a_total - m_total) / target:17.9f}')
    print('Independent divisor and model enumerations agree in every cell type.')


if __name__ == '__main__':
    parser = ArgumentParser(description='Replay the strict Goldbach moving-prefix cofactor split.')
    parser.add_argument('--target', type=int, default=9602)
    parser.add_argument('--alpha', type=Fraction, help='Default: isqrt(target) // 2.')
    parser.add_argument('--band', choices=('low', 'all'), default='low',
                        help='Low uses 2 <= q and 4 * alpha * q < target.')
    args = parser.parse_args()
    if args.target < 4 or args.target % 2:
        parser.error('target must be an even integer at least 4')
    alpha = args.alpha if args.alpha is not None else Fraction(isqrt(args.target) // 2)
    if alpha < 1:
        parser.error('alpha must be at least 1')
    replay(args.target, alpha, args.band)
