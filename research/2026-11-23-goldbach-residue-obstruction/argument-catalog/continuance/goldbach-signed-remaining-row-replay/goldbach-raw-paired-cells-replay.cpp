#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;

struct Row {
    long double signed_weight = 0;
    long double absolute_weight = 0;
    u64 terms = 0;

    void add(long double weight) {
        signed_weight += weight;
        absolute_weight += std::abs(weight);
        ++terms;
    }
};

int cell(u32 value, u32 half_root, u32 root) {
    if (value <= half_root) return 0;
    if (value <= root) return 1;
    return 2;
}

void replay(int exponent) {
    if (exponent < 20 || exponent > 28 || exponent % 2 != 0) {
        throw std::runtime_error("Use an even exponent from 20 through 28.");
    }
    const u32 n = 1U << exponent;
    const u32 root = 1U << (exponent / 2);
    const long double log_n = std::log(static_cast<long double>(n));
    u32 q_min = 1;
    while (static_cast<u64>(q_min) * q_min * q_min * q_min < n) ++q_min;
    const long double alpha = root / std::pow(log_n, 5);
    if (alpha * q_min >= 1) throw std::runtime_error("The moving cutoff is active.");

    // A zero entry represents a prime for every odd argument greater than one.
    std::vector<std::uint16_t> least(n / 2, 0);
    for (u32 p = 3; p <= root; p += 2) {
        if (least[p / 2] != 0) continue;
        for (u32 m = p * p; m < n; m += 2 * p) {
            if (least[m / 2] == 0) least[m / 2] = static_cast<std::uint16_t>(p);
        }
    }
    const auto smallest_factor = [&least](u32 value) -> u32 {
        if (value % 2 == 0) return 2;
        return least[value / 2] == 0 ? value : least[value / 2];
    };

    Row rows[3][3];
    Row low_actual;
    Row a20_short, a20_overlap, wide_even, transition_even;
    Row wide_mixed, wide_pos_pos, wide_neg_neg;
    Row transition_mixed, transition_pos_pos, transition_neg_neg;
    long double mobius_correlation = 0;
    // At the even prime powers greater than two, N - p_power is a multiple of
    // four and makes every original summand zero.
    for (u32 p_power = 2; p_power < n; p_power += p_power == 2 ? 1 : 2) {
        const u32 p = smallest_factor(p_power);
        if (p != p_power) {
            u32 quotient = p_power;
            do { quotient /= p; } while (quotient > 1 && quotient % p == 0);
            if (quotient != 1) continue;
        }

        const u32 m = n - p_power;
        u32 factor[16];
        int factor_count = 0;
        u32 remainder = m;
        while (remainder > 1) {
            const u32 smallest = smallest_factor(remainder);
            remainder /= smallest;
            if (remainder % smallest == 0) break;
            factor[factor_count++] = smallest;
        }
        if (remainder != 1) continue;

        const int mu_m = factor_count % 2 == 0 ? 1 : -1;
        const long double log_prime = std::log(static_cast<double>(p));
        mobius_correlation += mu_m * log_prime;
        u32 divisor[1 << 10];
        int mu_divisor[1 << 10];
        divisor[0] = 1;
        mu_divisor[0] = 1;
        int divisor_count = 1;
        for (int i = 0; i < factor_count; ++i) {
            if (2 * divisor_count > (1 << 10)) throw std::runtime_error("Divisor capacity.");
            for (int j = 0; j < divisor_count; ++j) {
                divisor[divisor_count + j] = divisor[j] * factor[i];
                mu_divisor[divisor_count + j] = -mu_divisor[j];
            }
            divisor_count *= 2;
        }

        for (int d = 0; d < divisor_count; ++d) {
            const u32 q = divisor[d];
            if (q % 2 == 0) continue;
            const u32 h = m / q;
            if (h == 1) continue;  // The original log h is zero.
            const int mu_h = mu_m * mu_divisor[d];
            const long double weight = -mu_h * log_prime * std::log(static_cast<double>(h));
            if (q < q_min) {
                low_actual.add(weight);
                continue;
            }
            const int i = cell(q, root / 2, root);
            const int j = cell(h, root / 2, root);
            rows[i][j].add(weight);
            if (i == 2 && j == 0) {
                if (h < q_min) a20_short.add(weight);
                else a20_overlap.add(weight);
            }
            if (h % 2 == 0) {
                if ((i == 0 && j == 2) || (i == 2 && j == 0 && h >= q_min)) {
                    wide_even.add(weight);
                }
                if ((i == 1 && j == 2) || (i == 2 && j == 1)) {
                    transition_even.add(weight);
                }
                continue;
            }
            if ((i == 0 || i == 1) && j == 2) {
                const int mu_q = mu_divisor[d];
                const long double paired = -log_prime *
                    (mu_h * std::log(static_cast<double>(h)) +
                     mu_q * std::log(static_cast<double>(q)));
                if (i == 0) {
                    if (mu_q != mu_h) wide_mixed.add(paired);
                    else if (mu_q > 0) wide_pos_pos.add(paired);
                    else wide_neg_neg.add(paired);
                } else {
                    if (mu_q != mu_h) transition_mixed.add(paired);
                    else if (mu_q > 0) transition_pos_pos.add(paired);
                    else transition_neg_neg.add(paired);
                }
            }
        }
    }

    auto print = [exponent, n](const char* name, const Row& row) {
        std::cout << exponent << ',' << name << ',' << row.signed_weight / n << ','
                  << row.absolute_weight / n << ',' << row.terms << '\n';
    };
    std::cout << std::fixed << std::setprecision(12);
    const long double wide_sum = wide_even.signed_weight + wide_mixed.signed_weight
        + wide_pos_pos.signed_weight + wide_neg_neg.signed_weight;
    const long double transition_sum = transition_even.signed_weight + transition_mixed.signed_weight
        + transition_pos_pos.signed_weight + transition_neg_neg.signed_weight;
    if (std::abs(wide_sum - rows[0][2].signed_weight - a20_overlap.signed_weight) > 1e-8L * n
        || std::abs(transition_sum - rows[1][2].signed_weight - rows[2][1].signed_weight) > 1e-8L * n) {
        throw std::runtime_error("Paired weights do not agree with raw row sums.");
    }
    print("A20_h_below_Q", a20_short);
    print("A20_h_at_least_Q", a20_overlap);
    print("A02_plus_A20_overlap_mixed", wide_mixed);
    print("A02_plus_A20_overlap_both_plus", wide_pos_pos);
    print("A02_plus_A20_overlap_both_minus", wide_neg_neg);
    print("A02_plus_A20_overlap_even_h", wide_even);
    print("A12_plus_A21_mixed", transition_mixed);
    print("A12_plus_A21_both_plus", transition_pos_pos);
    print("A12_plus_A21_both_minus", transition_neg_neg);
    print("A12_plus_A21_even_h", transition_even);
}

int main(int argc, char** argv) {
    std::cout << "k,row,signed_per_N,absolute_per_N,nonzero_terms\n";
    for (int i = 1; i < argc; ++i) replay(std::atoi(argv[i]));
}
