from fractions import Fraction
from math import fsum, gcd, isclose, log

from replay_goldbach import arithmetic_tables


def cell_terms(target, alpha, cells, mu, prime_base):
    lanes = [[], [], []]
    for h in sorted(cells):
        for offset, weights in enumerate(lanes):
            partner = 3 * h + offset
            if 3 * alpha < partner < target and mu[partner]:
                base = prime_base[target - partner]
                if base:
                    weights.append(mu[partner] * log(base) * log(partner / 3))
    return lanes


def check_offset_support(target, alpha, cells, mu, prime_base, lanes):
    diagonal = []
    for h in sorted(cells):
        n = target - 3 * h
        if alpha < h and n > 0 and h % 3 and prime_base[n]:
            diagonal.append(-log(prime_base[n]) * log(h))

    independent = [diagonal]
    for offset, prime in ((1, 2), (2, 3)):
        weights = []
        n = prime
        while n < target:
            partner = target - n
            h, remainder = divmod(partner, 3)
            if remainder == offset and h in cells and partner > 3 * alpha and mu[partner]:
                weights.append(mu[partner] * log(prime) * log(partner / 3))
            n *= prime
        independent.append(weights)

    for direct, reduced in zip(lanes, independent):
        assert len(direct) == len(reduced)
        assert isclose(fsum(direct), fsum(reduced), rel_tol=1e-12, abs_tol=1e-10)

    off_diagonal_model_mass = fsum(abs(weight) for lane in lanes[1:] for weight in lane) / 2
    assert off_diagonal_model_mass <= log(target) ** 2


def run_case(target, alpha, kind, cells, mu, prime_base):
    assert target % 6 == 2 and 12 * alpha < target
    lanes = cell_terms(target, alpha, cells, mu, prime_base)
    check_offset_support(target, alpha, cells, mu, prime_base, lanes)
    actual = fsum(lanes[0])
    diagonal_model = actual / 2
    off_model = fsum(lanes[1] + lanes[2]) / 2
    model = diagonal_model + off_model
    print(f'N={target} alpha={alpha} {kind}')
    print(f'  terms j=0,1,2: {tuple(map(len, lanes))}')
    print(f'  actual/N={actual / target:+.9f} model/N={model / target:+.9f}')
    print(f'  diagonal model/N={diagonal_model / target:+.9f} '
          f'off-diagonal model/N={off_model / target:+.9f}')
    print(f'  error/N={(actual - model) / target:+.9f}')
    return tuple(map(len, lanes))


def main():
    target = 9602
    _, mu, distinct, prime_base = arithmetic_tables(target - 1)
    cells = {h for h in range(3, (target - 1) // 3 + 1, 2)
             if mu[h] == 1 and distinct[h] == 2}
    five_times_prime = {h for h in cells if h % 5 == 0 and h // 5 > 5}
    run_case(target, Fraction(48), 'h=5p, prime p>5', five_times_prime, mu, prime_base)
    run_case(target, Fraction(48), 'all odd squarefree semiprime cells', cells, mu, prime_base)

    # The actual point is at or beyond the strict endpoint in both fixtures.
    # One off-diagonal model term remains in each.
    for target, alpha, expected in ((4202, Fraction(35), (0, 1, 0)),
                                    (2294, Fraction(211, 6), (0, 0, 1))):
        _, mu, _, prime_base = arithmetic_tables(target - 1)
        assert run_case(target, alpha, 'boundary cell h=35', {35}, mu, prime_base) == expected

    target = 1328
    _, mu, _, prime_base = arithmetic_tables(target - 1)
    assert prime_base[target - 105] == target - 105 and mu[105] == -1
    assert cell_terms(target, Fraction(35), {35}, mu, prime_base)[0] == []
    assert len(cell_terms(target, Fraction(209, 6), {35}, mu, prime_base)[0]) == 1
    print('Changing alpha from 35 to 209/6 admits the nonzero diagonal at m=105.')

    # The progression p ranges across both units modulo 6, and the other
    # variable is always in class 5. The mean singular series on N=2 mod 6 is 3/2.
    smaller_primes = (5, 7, 11, 13)
    mean_singular_series = 2 * (1 - Fraction(1, (3 - 1) ** 2))
    budget_coefficient = mean_singular_series / 12
    unit_classes = [u for u in range(6) if gcd(u, 6) == 1]
    coefficient = 0
    for prime in smaller_primes:
        assert {(2 - 3 * prime * u) % 6 for u in unit_classes} == {5}
        mass_coefficient = Fraction(1, 12 * prime)
        contribution = mass_coefficient / (2 * budget_coefficient)
        assert contribution == Fraction(1, 3 * prime)
        coefficient += contribution
    assert coefficient > Fraction(1, 6)
    print(f'For r={smaller_primes}, sum 1/(3r)={coefficient} '
          f'= {float(coefficient):.9f} > 1/6.')
    print('Direct and reindexed lane counts and weights agree.')


if __name__ == '__main__':
    main()
