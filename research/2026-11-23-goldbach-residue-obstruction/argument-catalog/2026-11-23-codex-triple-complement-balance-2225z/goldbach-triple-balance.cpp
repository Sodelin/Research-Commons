#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;
using real = long double;

struct Factors {
    std::array<u32, 16> primes{};
    unsigned size = 0;
    bool squarefree = true;
};

class OddFactors {
    std::vector<std::uint16_t> least;

public:
    explicit OddFactors(u32 limit) : least(limit / 2 + 1) {
        for (u32 p = 3; u64(p) * p <= limit; p += 2) {
            if (least[p / 2] != 0) continue;
            for (u64 j = u64(p) * p; j <= limit; j += 2 * p) {
                if (least[j / 2] == 0) least[j / 2] = p;
            }
        }
    }

    Factors operator()(u32 n) const {
        Factors result;
        while (n > 1) {
            u32 p = least[n / 2] == 0 ? n : least[n / 2];
            n /= p;
            if (n % p == 0) {
                result.squarefree = false;
                return result;
            }
            result.primes[result.size++] = p;
        }
        return result;
    }
};

struct Cofactor {
    u32 value;
    int mu;
    unsigned middle, mark, below_high, below_low;
};

struct Pair {
    u32 n, q;
};

struct PlacementSum {
    u64 count = 0;
    real signed_sum = 0, abs_sum = 0;

    void add(real value, int mu) {
        ++count;
        signed_sum += mu * value;
        abs_sum += value;
    }
};

struct Bracket {
    u64 count = 0;
    real abs_sum = 0;
    std::array<int, 16> coeff{};

    void add(unsigned mask, int sign, real log_ell) {
        ++count;
        abs_sum += log_ell;
        for (; mask; mask &= mask - 1) coeff[std::countr_zero(mask)] += sign;
    }

    real signed_sum(const Factors &n, std::vector<real> const &logs) const {
        real total = 0;
        for (unsigned j = 0; j < n.size; ++j) {
            if (coeff[j] != 0) {
                const u32 p = n.primes[j];
                if (p >= logs.size()) throw std::logic_error("admitted divisor log missing");
                total += coeff[j] * logs[p];
            }
        }
        return total;
    }

    bool exact_zero() const {
        return std::all_of(coeff.begin(), coeff.end(), [](int c) { return c == 0; });
    }
};

struct Balance {
    u64 products = 0, pairs = 0, terms = 0, zero_brackets = 0;
    u64 complete_products = 0, four_factor_products = 0;
    real raw = 0, after_divisors = 0, after_products = 0, final = 0;
    real zero_bracket_raw = 0, complete_raw = 0, four_factor_raw = 0;
    real low_order_after_products = 0, mixed_order_drop = 0;
    real prefix_low = 0, prefix_high = 0;
    std::array<real, 64> bins{};
    std::vector<real> by_ell;

    void add(const PlacementSum &placements, const Bracket &bracket,
             real bracket_sum, int mu_n, u32 n, u32 target,
             bool complete, bool four_factors) {
        ++products;
        pairs += placements.count;
        terms += placements.count * bracket.count;
        const real mass = placements.abs_sum * bracket.abs_sum;
        if (bracket.exact_zero()) {
            ++zero_brackets;
            zero_bracket_raw += mass;
        }
        if (complete) {
            ++complete_products;
            complete_raw += mass;
        }
        if (four_factors) {
            ++four_factor_products;
            four_factor_raw += mass;
        }
        raw += mass;
        after_divisors += placements.abs_sum * std::abs(bracket_sum);
        const real contribution = mu_n * placements.signed_sum * bracket_sum;
        after_products += std::abs(contribution);
        final += contribution;
        prefix_low = std::min(prefix_low, final);
        prefix_high = std::max(prefix_high, final);
        bins[(u64(n) * bins.size() - 1) / target] += contribution;
    }

    void print(std::string const &scenario, std::string const &sector) const {
        real ell_abs = 0, ell_prefix = 0, ell_low = 0, ell_high = 0;
        for (real value : by_ell) {
            ell_abs += std::abs(value);
            ell_prefix += value;
            ell_low = std::min(ell_low, ell_prefix);
            ell_high = std::max(ell_high, ell_prefix);
        }
        if (std::abs(ell_prefix - final) > 1e-12L * (1 + raw)) {
            throw std::logic_error("two summation orders disagree");
        }
        std::cout << scenario << '\t' << sector << '\t' << products << '\t' << pairs
                  << '\t' << terms << '\t' << zero_brackets << '\t'
                  << complete_products << '\t' << four_factor_products << '\t' << raw << '\t'
                  << after_divisors << '\t' << after_products << '\t' << final
                  << '\t' << prefix_low << '\t' << prefix_high << '\t' << ell_abs
                  << '\t' << ell_low << '\t' << ell_high
                  << '\t' << zero_bracket_raw << '\t' << complete_raw << '\t' << four_factor_raw
                  << '\t' << low_order_after_products << '\t' << mixed_order_drop;
        real prefix = 0;
        for (real value : bins) {
            prefix += value;
            std::cout << '\t' << prefix;
        }
        std::cout << '\n';
    }
};

enum Scenario { all_divisors, triple_divisors, witness_geometry, scenario_count };
enum Sector { total, odd_m, even_n, odd_m_even_n, sector_count };

int main(int argc, char **argv) {
    try {
        if (argc != 19) throw std::runtime_error("usage: run-triple-balance.py");
        std::array<u32, 18> input{};
        for (int i = 1; i < argc; ++i) input[i - 1] = std::stoul(argv[i]);
        const auto [N, H, cutoff, Y, Y0, Z, below_high, below_low, mark_low, mark_high,
                    kmin, kmax, min_high, min_low, ell_low, ell_high, d_small, d_min] = input;
        if (N % 2 != 0 || H < 4 || cutoff < H) throw std::runtime_error("invalid target");
        OddFactors factor(N);
        u32 first_missing = 3;
        for (;; first_missing += 2) {
            const auto f = factor(first_missing);
            if (N % first_missing != 0 && f.squarefree && f.size == 1) break;
        }

        const u32 max_ell = N / (cutoff + 1);
        std::vector<real> logs(std::max(H, max_ell) + 1);
        for (u32 j = 1; j < logs.size(); ++j) logs[j] = std::log(real(j));
        std::vector<Cofactor> cofactors(H + 1);
        std::vector<u32> values;
        for (u32 q = (H / 2 + 1) | 1U; q <= H; q += 2) {
            if (std::gcd(q, N) != 1) continue;
            const Factors f = factor(q);
            if (!f.squarefree) continue;
            Cofactor row{q, f.size % 2 ? -1 : 1, 0, 0, 0, 0};
            for (unsigned j = 0; j < f.size; ++j) {
                const u32 p = f.primes[j];
                row.middle += Y0 < p && p <= Z;
                row.mark += mark_low < p && p <= mark_high;
                row.below_high += p <= below_high;
                row.below_low += p <= below_low;
            }
            cofactors[q] = row;
            values.push_back(q);
        }
        std::vector<Pair> pairs;
        pairs.reserve(values.size() * (values.size() - 1) / 2);
        for (std::size_t i = 0; i < values.size(); ++i) {
            const auto q = cofactors[values[i]];
            for (std::size_t j = i + 1; j < values.size(); ++j) {
                const auto h = cofactors[values[j]];
                const unsigned middle = q.middle + h.middle;
                if (middle < kmin || middle > kmax || q.mark + h.mark > 1
                    || q.below_high + h.below_high < min_high
                    || (q.mu != h.mu && q.below_low + h.below_low < min_low)
                    || std::gcd(q.value, h.value) != 1) continue;
                const u32 n = N - q.value * h.value;
                if (n > cutoff) pairs.push_back({n, q.value});
            }
        }
        std::sort(pairs.begin(), pairs.end(), [](auto a, auto b) {
            return a.n < b.n || (a.n == b.n && a.q < b.q);
        });

        std::array<std::array<Balance, sector_count>, scenario_count> results;
        for (auto &scenario : results) {
            for (auto &s : scenario) s.by_ell.resize(max_ell + 1);
        }
        struct Divisor { u32 ell; unsigned mask; };
        std::array<Divisor, 1024> divisors;
        std::array<unsigned, 1024> active;
        for (std::size_t begin = 0; begin < pairs.size();) {
            const u32 n = pairs[begin].n;
            std::size_t end = begin + 1;
            while (end < pairs.size() && pairs[end].n == n) ++end;
            const std::size_t start = begin;
            begin = end;
            const Factors f = factor(n);
            const u32 limit = n / (cutoff + 1);
            if (!f.squarefree || f.size < 3 || f.primes[0] <= Y
                || u64(f.primes[0]) * f.primes[1] * f.primes[2] > limit) continue;
            const int mu_n = f.size % 2 ? -1 : 1;
            const u32 m = N - n;
            const u32 sample = pairs[start].q;
            const bool m_odd = cofactors[sample].mu != cofactors[m / sample].mu;
            const std::array<bool, sector_count> use_sector{true, m_odd, mu_n == 1,
                                                          m_odd && mu_n == 1};
            PlacementSum all, geometry;
            for (std::size_t i = start; i < end; ++i) {
                const u32 q = pairs[i].q, h = m / q;
                const real c = m_odd ? logs[h] - logs[q] : logs[h] + logs[q];
                const int mu_h = cofactors[h].mu;
                all.add(c, mu_h);
                if (u64(64) * q * q <= u64(25) * N && u64(16) * h * h > u64(9) * N
                    && u64(64) * h * h <= u64(49) * N && q % first_missing == 0
                    && cofactors[q].mark + cofactors[h].mark == 0) geometry.add(c, mu_h);
            }

            unsigned count = 1, small_mask = 0;
            u32 all_admitted_primes = 1;
            divisors[0] = {1, 0};
            for (unsigned j = 0; j < f.size; ++j) {
                const u32 p = f.primes[j];
                if (p <= d_small) small_mask |= 1U << j;
                if (p <= limit) all_admitted_primes *= p;
                const unsigned previous = count;
                for (unsigned k = 0; k < previous; ++k) {
                    const auto d = divisors[k];
                    const u64 ell = u64(d.ell) * p;
                    if (ell <= limit) divisors[count++] = {u32(ell), d.mask | (1U << j)};
                }
            }
            std::array<Bracket, scenario_count> b{};
            for (unsigned k = 1; k < count; ++k) {
                const auto [ell, mask] = divisors[k];
                const unsigned omega = std::popcount(mask);
                const int sign = omega % 2 ? 1 : -1;
                unsigned flags = 1U << all_divisors;
                if (omega >= 3) {
                    flags |= 1U << triple_divisors;
                    if (geometry.count && ell_low < ell && ell <= ell_high
                        && unsigned(std::popcount(small_mask & ~mask)) >= d_min) {
                        flags |= 1U << witness_geometry;
                    }
                }
                active[k] = flags;
                for (unsigned s = flags; s; s &= s - 1) {
                    b[std::countr_zero(s)].add(mask, sign, logs[ell]);
                }
            }
            const std::array<PlacementSum, scenario_count> co{all, all, geometry};
            const bool complete = all_admitted_primes <= limit;
            const bool four_factors = f.size == 4;
            if ((complete || four_factors) && !b[all_divisors].exact_zero()) {
                throw std::logic_error("complete divisor bracket is nonzero");
            }
            std::array<real, scenario_count> bracket_sum{};
            for (unsigned j = 0; j < scenario_count; ++j) {
                if (b[j].count == 0) continue;
                bracket_sum[j] = b[j].signed_sum(f, logs);
                for (unsigned s = 0; s < sector_count; ++s) {
                    if (use_sector[s]) {
                        results[j][s].add(co[j], b[j], bracket_sum[j], mu_n, n, N,
                                          complete, four_factors);
                    }
                }
            }
            const real low = std::abs(bracket_sum[all_divisors] - bracket_sum[triple_divisors]);
            const real mixed = low + std::abs(bracket_sum[triple_divisors])
                             - std::abs(bracket_sum[all_divisors]);
            for (unsigned s = 0; s < sector_count; ++s) {
                if (!use_sector[s]) continue;
                results[all_divisors][s].low_order_after_products += std::abs(all.signed_sum) * low;
                results[all_divisors][s].mixed_order_drop += std::abs(all.signed_sum) * mixed;
            }
            for (unsigned k = 1; k < count; ++k) {
                const auto [ell, mask] = divisors[k];
                const real a = mu_n * (std::popcount(mask) % 2 ? logs[ell] : -logs[ell]);
                for (unsigned f = active[k]; f; f &= f - 1) {
                    const unsigned j = std::countr_zero(f);
                    for (unsigned s = 0; s < sector_count; ++s) {
                        if (use_sector[s]) results[j][s].by_ell[ell] += a * co[j].signed_sum;
                    }
                }
            }
        }

        const std::array<std::string, scenario_count> names{
            "exact_triple_center", "triple_divisors_only", "witness_geometry"};
        const std::array<std::string, sector_count> sectors{
            "all", "mu_m_minus", "mu_n_plus", "mu_m_minus_mu_n_plus"};
        std::cout << std::setprecision(18);
        for (unsigned j = 0; j < scenario_count; ++j) {
            for (unsigned s = 0; s < sector_count; ++s) results[j][s].print(names[j], sectors[s]);
        }
    } catch (std::exception const &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
