#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

#include <quadmath.h>

using u64 = std::uint64_t;
using u128 = __uint128_t;

struct Cutoffs {
    unsigned k;
    u64 target, low, high, endpointMax, rough, shortDivisor, longDivisor;
    u64 smallPrimeMax, groupedIndex, middleLo, middleHi, markLo, markHi;
    u64 below9896, below95;
    unsigned middleMin, middleMax, below9896Min, below95Min;
};

struct PrimeTable {
    std::vector<unsigned> smallest;
    std::vector<unsigned> primes;

    explicit PrimeTable(unsigned limit) : smallest(limit + 1) {
        for (unsigned n = 2; n <= limit; ++n) {
            if (smallest[n] == 0) {
                smallest[n] = n;
                primes.push_back(n);
            }
            for (unsigned p : primes) {
                if (p > smallest[n] || u64(n) * p > limit) break;
                smallest[n * p] = p;
            }
        }
    }
};

u64 mul(u64 a, u64 b, u64 n) {
    return u64(u128(a) * b % n);
}

u64 power(u64 a, u64 e, u64 n) {
    u64 out = 1;
    for (; e; e >>= 1, a = mul(a, a, n))
        if (e & 1) out = mul(out, a, n);
    return out;
}

// The first seven prime bases suffice for n < 341550071728321.
bool is_prime(u64 n) {
    if (n < 2) return false;
    constexpr std::array<unsigned, 7> bases{2, 3, 5, 7, 11, 13, 17};
    for (unsigned p : bases)
        if (n % p == 0) return n == p;
    unsigned levels = __builtin_ctzll(n - 1);
    u64 d = (n - 1) >> levels;
    for (unsigned p : bases) {
        u64 a = power(p, d, n);
        if (a == 1 || a == n - 1) continue;
        for (unsigned j = 1; j < levels && a != n - 1; ++j) a = mul(a, a, n);
        if (a != n - 1) return false;
    }
    return true;
}

// Brent's factor search returns only a verified proper divisor.
// An ordinary prime trial fallback handles a failed search.
u64 find_factor(u64 n, const PrimeTable& table) {
    constexpr u64 batch = 32;
    for (u64 c = 1; c <= 8; ++c) {
        auto step = [&](u64 x) { return (mul(x, x, n) + c) % n; };
        u64 x = 0, y = 2 + c, prior = 0, g = 1;
        for (u64 block = 1; block <= 8192 && g == 1; block *= 2) {
            x = y;
            for (u64 i = 0; i < block; ++i) y = step(y);
            for (u64 i = 0; i < block && g == 1; i += batch) {
                prior = y;
                u64 product = 1;
                for (u64 j = 0; j < std::min(batch, block - i); ++j) {
                    y = step(y);
                    product = mul(product, x > y ? x - y : y - x, n);
                }
                g = std::gcd(product, n);
            }
        }
        if (g == n) {
            do {
                prior = step(prior);
                g = std::gcd(x > prior ? x - prior : prior - x, n);
            } while (g == 1);
        }
        if (g > 1 && g < n && n % g == 0) return g;
    }
    for (u64 p : table.primes) {
        if (p * p > n) break;
        if (n % p == 0) return p;
    }
    throw std::runtime_error("Unable to split a composite");
}

bool collect_factors(u64 n, const PrimeTable& table, std::vector<u64>& factors) {
    if (n < table.smallest.size()) {
        while (n > 1) {
            u64 p = table.smallest[n];
            factors.push_back(p);
            n /= p;
        }
        return true;
    }
    if (is_prime(n)) return false;
    const u64 a = find_factor(n, table);
    return collect_factors(a, table, factors) && collect_factors(n / a, table, factors);
}

bool squarefree_balanced_factors(u64 m, const PrimeTable& table, std::vector<u64>& factors) {
    factors.clear();
    u64 n = m;
    for (u64 p : table.primes) {
        if (p > 71 || n == 1) break;
        if (n % p != 0) continue;
        n /= p;
        if (n % p == 0) return false;
        factors.push_back(p);
    }
    if (!collect_factors(n, table, factors)) return false;
    std::sort(factors.begin(), factors.end());
    u64 check = 1;
    for (u64 p : factors) {
        assert(p < table.smallest.size() && table.smallest[p] == p);
        check *= p;
    }
    assert(check == m);
    return std::adjacent_find(factors.begin(), factors.end()) == factors.end();
}

bool center_mask(const Cutoffs& c, const std::vector<u64>& factors) {
    unsigned middle = 0, mark = 0, low9896 = 0, low95 = 0;
    for (u64 p : factors) {
        middle += c.middleLo < p && p <= c.middleHi;
        mark += c.markLo < p && p <= c.markHi;
        low9896 += p <= c.below9896;
        low95 += p <= c.below95;
    }
    return c.middleMin <= middle && middle <= c.middleMax && mark <= 1
           && low9896 >= c.below9896Min
           && (factors.size() % 2 == 0 || low95 >= c.below95Min);
}

struct Pair { u64 q, h; int hSign; };

void collect_pairs(const Cutoffs& c, const std::vector<u64>& factors, u64 m,
                   std::size_t index, u64 q, int qSign, std::vector<Pair>& pairs) {
    if (index == factors.size()) {
        u64 h = m / q;
        if (c.low <= q && q < h && h <= c.high) {
            const int mSign = factors.size() % 2 ? -1 : 1;
            pairs.push_back({q, h, mSign * qSign});
        }
        return;
    }
    collect_pairs(c, factors, m, index + 1, q, qSign, pairs);
    if (q * factors[index] <= c.high)
        collect_pairs(c, factors, m, index + 1, q * factors[index], -qSign, pairs);
}

long double small_log(const std::vector<Pair>& pairs, const std::vector<u64>& factors) {
    __float128 value = 0;
    bool is_zero = true;
    for (u64 p : factors) {
        int exponent = 0;
        for (const auto& a : pairs) exponent += (a.h % p == 0 ? 1 : -1) * a.hSign;
        is_zero &= exponent == 0;
        if (exponent) value += exponent * logq(static_cast<__float128>(p));
    }
    if (is_zero) return 0;
    if (fabsq(value) < 1e-24L) throw std::runtime_error("Unresolved numerical sign");
    return static_cast<long double>(value);
}

struct Sum {
    long double value = 0, residual = 0;
    void add(long double term) {
        const long double adjusted = term - residual;
        const long double next = value + adjusted;
        residual = (next - value) - adjusted;
        value = next;
    }
};

struct Stats {
    u64 pairs = 0, mixed = 0, zero = 0;
    Sum before, endpointAbs, positive, negative, final;
    std::vector<std::pair<u64, long double>> endpoints;
    long double prefixMax = 0;
    u64 prefixAt = 0;

    void update(u64 n, long double beforeGrouping, long double signedWeight,
                u64 pairsAtN, bool mixedAtN) {
        pairs += pairsAtN;
        mixed += mixedAtN;
        zero += signedWeight == 0;
        before.add(beforeGrouping);
        endpointAbs.add(std::abs(signedWeight));
        positive.add(std::max(0.0L, signedWeight));
        negative.add(std::max(0.0L, -signedWeight));
        endpoints.emplace_back(n, signedWeight);
    }

    void print(unsigned k, int parity, const char* mask, u64 triples) {
        std::sort(endpoints.begin(), endpoints.end());
        for (const auto& [n, weight] : endpoints) {
            final.add(weight);
            if (std::abs(final.value) > prefixMax) {
                prefixMax = std::abs(final.value);
                prefixAt = n;
            }
        }
        std::cout << k << ',' << parity << ',' << mask << ',' << triples << ','
                  << endpoints.size() << ',' << pairs << ',' << mixed << ',' << zero << ','
                  << before.value << ',' << endpointAbs.value << ',' << positive.value << ','
                  << negative.value << ',' << final.value << ',' << prefixMax << ',' << prefixAt << '\n';
    }
};

void run(const Cutoffs& c) {
    assert(c.target < 341550071728321ULL && c.high < (1ULL << 32));
    const u128 smallest = c.rough + 1;
    std::array<std::array<Stats, 2>, 2> rows;
    u64 triples = 0;
    long double formulaError = 0;
    if (smallest * smallest * smallest <= c.endpointMax) {
        assert(smallest * smallest * smallest * smallest > c.endpointMax);
        assert(smallest > c.shortDivisor);
        assert(smallest * smallest > c.groupedIndex && smallest * smallest > c.longDivisor);
        const PrimeTable table(c.high);
        const auto& primes = table.primes;
        auto first = std::upper_bound(primes.begin(), primes.end(), c.rough);
        auto limit = std::upper_bound(primes.begin(), primes.end(),
                                     u64(c.endpointMax / (smallest * smallest)));
        std::vector<u64> factors;
        std::vector<Pair> pairs;
        for (auto i = first; i != limit && u128(*i)*(*i)*(*i) <= c.endpointMax; ++i) {
            for (auto j = i + 1; j < limit && u128(*i)*(*j)*(*j) <= c.endpointMax; ++j) {
                const u64 ab = u64(*i) * (*j);
                const auto end = std::upper_bound(j + 1, limit, c.endpointMax / ab);
                for (auto t = j + 1; t != end; ++t) {
                    ++triples;
                    const u64 n = ab * (*t), m = c.target - n;
                    if (!squarefree_balanced_factors(m, table, factors)) continue;
                    pairs.clear();
                    collect_pairs(c, factors, m, 0, 1, 1, pairs);
                    if (pairs.empty()) continue;
                    const bool mask = center_mask(c, factors);
                    const bool odd = factors.size() % 2 != 0;
                    const long double logm = std::log((long double)m);
                    const long double logn = std::log((long double)n);
                    const std::array<u64, 3> marks{*i, *j, *t};
                    Sum direct, pairAbs, cofactor;
                    for (u64 p : marks) for (u64 w : marks) {
                        if (p == w) continue;
                        const u64 s = n / (p * w);
                        assert(c.rough < p && p <= c.smallPrimeMax && w > c.shortDivisor);
                        assert(s > c.shortDivisor && w*s > c.longDivisor && p*w > c.groupedIndex);
                        direct.add(-std::log((long double)p)*std::log((long double)w)
                                   / std::log((long double)(w*s)));
                    }
                    formulaError = std::max(formulaError, std::abs(direct.value + logn));
                    assert(std::abs(direct.value + logn) < 1e-12L);
                    unsigned positive = 0;
                    for (const auto& a : pairs) {
                        const long double cweight = odd ? std::log((long double)a.h/a.q) : logm;
                        cofactor.add(a.hSign * cweight);
                        pairAbs.add(cweight);
                        positive += a.hSign > 0;
                    }
                    const bool mixed = positive > 0 && positive < pairs.size();
                    if (!odd)
                        cofactor.value = (2 * (long long)positive - (long long)pairs.size()) * logm;
                    else if (mixed && std::abs(cofactor.value) < 1e-12L)
                        cofactor.value = small_log(pairs, factors);
                    const long double beforeGrouping = logn * pairAbs.value;
                    const long double signedWeight = -logn * cofactor.value;
                    rows[0][odd].update(n, beforeGrouping, signedWeight, pairs.size(), mixed);
                    if (mask) rows[1][odd].update(n, beforeGrouping, signedWeight, pairs.size(), mixed);
                }
            }
        }
    }
    for (int mask = 0; mask < 2; ++mask)
        for (int odd = 0; odd < 2; ++odd)
            rows[mask][odd].print(c.k, odd ? -1 : 1, mask ? "center" : "raw", triples);
    std::cerr << "k=" << c.k << " candidate_triples=" << triples
              << " max_direct_weight_error=" << std::setprecision(5) << formulaError << '\n';
}

int main() {
    std::cout << std::setprecision(18)
              << "k,qh_parity,mask,candidate_triples,endpoints,qh_pairs,mixed_endpoints,zero_endpoints,"
                 "placement_abs,endpoint_abs,positive,negative_abs,signed,max_abs_prefix,prefix_endpoint\n";
    Cutoffs c;
    while (std::cin >> c.k >> c.target >> c.low >> c.high >> c.endpointMax >> c.rough
           >> c.shortDivisor >> c.longDivisor >> c.smallPrimeMax >> c.groupedIndex
           >> c.middleLo >> c.middleHi >> c.markLo >> c.markHi >> c.below9896 >> c.below95
           >> c.middleMin >> c.middleMax >> c.below9896Min >> c.below95Min) {
        run(c);
        std::cout.flush();
    }
}
