#define main prior_endpoint_balance_main
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"
#include "../2026-11-23-codex-signed-endpoint-balance-2336z/endpoint-balance.cpp"
#pragma GCC diagnostic pop
#undef main

#include <cstddef>
#include <string>
#include <omp.h>

constexpr unsigned grid = 1024;
constexpr unsigned primary_bins = 32;

struct EndpointCell {
    Sum weight, signedContribution, absoluteContribution;
    u64 triples = 0, endpoints = 0;
};

void scan_triples(const Cutoffs& c, const PrimeTable& table,
                  std::array<EndpointCell, grid>& cells) {
    const u128 z = c.rough + 1;
    if (z*z*z > c.endpointMax) return;
    assert(z*z*z*z > c.endpointMax);
    assert(z > c.shortDivisor && z*z > c.longDivisor && z*z > c.groupedIndex);
    const auto& primes = table.primes;
    auto first = std::upper_bound(primes.begin(), primes.end(), c.rough);
    auto limit = std::upper_bound(primes.begin(), primes.end(), u64(c.endpointMax/(z*z)));
    auto outerEnd = first;
    while (outerEnd < limit && u128(*outerEnd)*(*outerEnd)*(*outerEnd) <= c.endpointMax) ++outerEnd;
    const auto jobs = outerEnd - first;
    std::vector<std::array<EndpointCell, grid>> partial(jobs);

    #pragma omp parallel for schedule(dynamic, 1)
    for (std::ptrdiff_t job = 0; job < jobs; ++job) {
        const auto i = first + job;
        std::vector<u64> factors;
        std::vector<Pair> pairs;
        for (auto j = i + 1; j < limit && u128(*i)*(*j)*(*j) <= c.endpointMax; ++j) {
            const u64 ab = u64(*i)*(*j);
            const auto last = std::upper_bound(j + 1, limit, c.endpointMax / ab);
            for (auto t = j + 1; t != last; ++t) {
                const u64 n = ab * (*t), m = c.target - n;
                const long double logn = std::log((long double)n);
                auto& cell = partial[job][(n - 1) / (c.target / grid)];
                ++cell.triples;
                cell.weight.add(-logn);
                if (!squarefree_balanced_factors(m, table, factors) || factors.size() % 2) continue;
                pairs.clear();
                collect_pairs(c, factors, m, 0, 1, 1, pairs);
                if (pairs.empty()) continue;
                ++cell.endpoints;
                int cofactorSignSum = 0;
                for (const auto& a : pairs) cofactorSignSum += a.hSign;
                const long double value = -logn * std::log((long double)m) * cofactorSignSum;
                cell.signedContribution.add(value);
                cell.absoluteContribution.add(std::abs(value));
            }
        }
    }

    for (const auto& shard : partial) for (unsigned j = 0; j < grid; ++j) {
        cells[j].triples += shard[j].triples;
        cells[j].endpoints += shard[j].endpoints;
        cells[j].weight.add(shard[j].weight.value);
        cells[j].signedContribution.add(shard[j].signedContribution.value);
        cells[j].absoluteContribution.add(shard[j].absoluteContribution.value);
    }
}

std::vector<signed char> build_mu(const PrimeTable& table) {
    std::vector<signed char> mu(table.smallest.size());
    mu[1] = 1;
    for (u64 h = 2; h < mu.size(); ++h) {
        const auto p = table.smallest[h];
        const auto reduced = h / p;
        mu[h] = reduced % p == 0 ? 0 : -mu[reduced];
    }
    return mu;
}

struct PrefixValue {
    long double signLog = 0, squareLog = 0;
};

struct OddMultipleSpan {
    u64 first = 0, count = 0;
    std::size_t offset = 0;
};

struct OddMultiplePrefixes {
    std::vector<OddMultipleSpan> spans;
    std::vector<PrefixValue> data;

    OddMultiplePrefixes(const Cutoffs& c, const std::vector<signed char>& mu)
        : spans(c.high + 1) {
        std::size_t size = 0;
        for (u64 d = 1; d <= c.high; d += 2) {
            if (mu[d] == 0) continue;
            const u64 first = d * (((c.low + d - 1) / d) | 1);
            if (first > c.high) continue;
            const u64 count = 1 + (c.high - first) / (2*d);
            spans[d] = {first, count, size};
            size += count + 1;
        }
        data.resize(size);
        std::vector<long double> logs(c.high + 1);
        for (u64 h = c.low | 1; h <= c.high; h += 2)
            logs[h] = std::log((long double)h);
        for (u64 d = 1; d <= c.high; d += 2) {
            const auto row = spans[d];
            if (!row.count) continue;
            Sum sign, square;
            u64 h = row.first;
            for (u64 j = 0; j < row.count; ++j, h += 2*d) {
                sign.add(mu[h] * logs[h]);
                if (mu[h]) square.add(logs[h]);
                data[row.offset + j + 1] = {sign.value, square.value};
            }
        }
    }
};

struct CofactorCell {
    Sum signedSum, orderedAbsolute;
};

void sum_cofactors(const Cutoffs& c, const PrimeTable& table, unsigned begin, unsigned end,
                   std::array<CofactorCell, grid>& cells) {
    if (begin == end) return;
    const auto mu = build_mu(table);
    const OddMultiplePrefixes prefixes(c, mu);
    const u64 width = c.target / grid;
    const u64 leastQ = c.low | 1;
    const u64 qCount = 1 + (c.high - leastQ) / 2;
    constexpr unsigned shards = 96;
    std::vector<std::array<CofactorCell, grid>> partial(shards);

    #pragma omp parallel for schedule(dynamic, 1)
    for (unsigned shard = 0; shard < shards; ++shard) {
        std::vector<std::pair<u64, int>> divisors;
        std::array<u64, grid + 1> lower{};
        for (u64 i = (qCount * shard) / shards; i < (qCount * (shard + 1)) / shards; ++i) {
            const u64 q = leastQ + 2*i;
            if (mu[q] == 0) continue;
            for (unsigned j = begin; j <= end; ++j)
                lower[j] = std::clamp((c.target - width*j + q - 1) / q, c.low, c.high + 1);

            divisors.clear();
            divisors.emplace_back(1, 1);
            for (u64 t = q; t > 1;) {
                const u64 p = table.smallest[t];
                const auto previous = divisors.size();
                for (std::size_t k = 0; k < previous; ++k) {
                    const auto [d, sign] = divisors[k];
                    divisors.emplace_back(d*p, -sign);
                }
                t /= p;
            }

            for (const auto& [d, sign] : divisors) {
                const auto row = prefixes.spans[d];
                if (!row.count) continue;
                const auto index = [&](u64 lim) -> u64 {
                    if (lim <= row.first) return 0;
                    return 1 + (lim - row.first - 1) / (2*d);
                };
                u64 old = index(lower[begin]);
                for (unsigned j = begin; j < end; ++j) {
                    const u64 next = index(lower[j+1]);
                    if (next == old) continue;
                    const auto upper = prefixes.data[row.offset + old];
                    const auto base = prefixes.data[row.offset + next];
                    const long double z = upper.signLog - base.signLog;
                    const long double w = upper.squareLog - base.squareLog;
                    partial[shard][j].signedSum.add(0.5L * sign * (z + mu[q]*w));
                    partial[shard][j].orderedAbsolute.add(0.5L * sign * (w + mu[q]*z));
                    old = next;
                }
            }
        }
    }

    for (const auto& shard : partial) for (unsigned j = begin; j < end; ++j) {
        cells[j].signedSum.add(shard[j].signedSum.value);
        cells[j].orderedAbsolute.add(shard[j].orderedAbsolute.value);
    }
}

void prefix_self_test() {
    Cutoffs c{};
    c.target = 1u << 16;
    c.low = 129;
    c.high = 256;
    const PrimeTable table(c.high);
    const auto mu = build_mu(table);
    std::array<CofactorCell, grid> observed, direct;
    sum_cofactors(c, table, 0, grid, observed);
    for (u64 q = c.low | 1; q <= c.high; q += 2) {
        if (!mu[q]) continue;
        for (u64 h = c.low | 1; h <= c.high; h += 2) {
            if (std::gcd(q,h) != 1 || mu[q] != mu[h]) continue;
            const auto cell = (c.target - q*h - 1) / (c.target / grid);
            const auto weight = std::log((long double)h);
            direct[cell].signedSum.add(mu[h]*weight);
            direct[cell].orderedAbsolute.add(weight);
        }
    }
    for (std::size_t j = 0; j < grid; ++j) {
        assert(std::abs(observed[j].signedSum.value - direct[j].signedSum.value) < 1e-12L);
        assert(std::abs(observed[j].orderedAbsolute.value - direct[j].orderedAbsolute.value) < 1e-12L);
    }
    std::cerr << "direct ordered cofactor cross-check passed at every 2^16 grid cell\n";
}

template <unsigned bins>
std::array<long double, bins> interval_means(const Cutoffs& c,
                                            const std::array<EndpointCell, grid>& cells) {
    static_assert(grid % bins == 0);
    std::array<long double, bins> averages{};
    for (unsigned i = 0; i < bins; ++i) {
        Sum total;
        for (unsigned j = i*(grid/bins); j < (i+1)*(grid/bins); ++j) total.add(cells[j].weight.value);
        averages[i] = total.value / (c.target/bins);
    }
    return averages;
}

void run_prefix(const Cutoffs& c) {
    assert(c.target % grid == 0 && c.target < 341550071728321ULL);
    std::array<EndpointCell, grid> cells;
    std::array<CofactorCell, grid> cofactors;
    if (u128(c.rough + 1)*(c.rough + 1)*(c.rough + 1) <= c.endpointMax) {
        const PrimeTable table(c.high);
        scan_triples(c, table, cells);
        std::cerr << "k=" << c.k << " triple scan complete\n";
        const auto means = interval_means<primary_bins>(c, cells);
        unsigned first = primary_bins, last = 0;
        for (unsigned j = 0; j < means.size(); ++j) {
            if (means[j] != 0) {
                first = std::min(first, j);
                last = j + 1;
            }
        }
        if (first < last) sum_cofactors(c, table, first*(grid/primary_bins), last*(grid/primary_bins), cofactors);
    }
    const auto means32 = interval_means<32>(c, cells);
    const auto means64 = interval_means<64>(c, cells);
    Sum raw, center32, center64, absolute;
    u64 triples = 0, endpoints = 0;
    long double max32 = 0, max64 = 0, bound32 = 0, bound64 = 0;
    for (unsigned j = 0; j < grid; ++j) {
        const auto before32 = center32.value, before64 = center64.value;
        const auto& e = cells[j];
        const auto& a = cofactors[j];
        const auto mean32 = means32[j / (grid/32)], mean64 = means64[j / (grid/64)];
        const auto d32 = e.signedContribution.value - mean32*a.signedSum.value;
        const auto d64 = e.signedContribution.value - mean64*a.signedSum.value;
        const auto v32 = e.absoluteContribution.value + std::abs(mean32)*a.orderedAbsolute.value;
        const auto v64 = e.absoluteContribution.value + std::abs(mean64)*a.orderedAbsolute.value;
        assert(a.orderedAbsolute.value >= -1e-7L);
        assert(std::abs(d32) <= v32 + 1e-5L && std::abs(d64) <= v64 + 1e-5L);
        raw.add(e.signedContribution.value);
        center32.add(d32);
        center64.add(d64);
        absolute.add(e.absoluteContribution.value);
        triples += e.triples;
        endpoints += e.endpoints;
        max32 = std::max(max32, std::abs(center32.value));
        max64 = std::max(max64, std::abs(center64.value));
        bound32 = std::max(bound32, (std::abs(before32)+std::abs(center32.value)+v32)/2);
        bound64 = std::max(bound64, (std::abs(before64)+std::abs(center64.value)+v64)/2);
        std::cout << c.k << ',' << (j+1) << ',' << (j+1)*(c.target/grid) << ','
                  << e.triples << ',' << e.endpoints << ',' << e.weight.value << ','
                  << a.signedSum.value << ',' << a.orderedAbsolute.value << ','
                  << e.signedContribution.value << ',' << e.absoluteContribution.value << ','
                  << raw.value << ',' << center32.value << ',' << center64.value << ','
                  << mean32 << ',' << mean64 << ',' << v32 << ',' << v64 << '\n';
    }
    std::cout.flush();
    std::cerr << std::setprecision(14)
              << "k=" << c.k << " triples=" << triples << " endpoints=" << endpoints
              << " E=" << absolute.value << " raw=" << raw.value
              << " center32=" << center32.value << " sampled32=" << max32 << " bound32=" << bound32
              << " center64=" << center64.value << " sampled64=" << max64 << " bound64=" << bound64 << '\n';
}

int main(int argc, char** argv) {
    if (argc == 2 && std::string(argv[1]) == "--self-test") {
        prefix_self_test();
        return 0;
    }
    std::cout << std::setprecision(16)
              << "k,j,n,triples,endpoints,g_cell,a_cell,a_ordered_abs,raw_cell,raw_abs,"
                 "raw_prefix,center32,center64,g_mean32,g_mean64,variation32,variation64\n";
    Cutoffs c;
    while (std::cin >> c.k >> c.target >> c.low >> c.high >> c.endpointMax >> c.rough
           >> c.shortDivisor >> c.longDivisor >> c.smallPrimeMax >> c.groupedIndex
           >> c.middleLo >> c.middleHi >> c.markLo >> c.markHi >> c.below9896 >> c.below95
           >> c.middleMin >> c.middleMax >> c.below9896Min >> c.below95Min) {
        run_prefix(c);
    }
}
