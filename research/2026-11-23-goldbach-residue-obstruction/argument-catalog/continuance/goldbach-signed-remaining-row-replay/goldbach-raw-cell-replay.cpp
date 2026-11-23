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
    Row first_h[64];
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
            if (i == 2 && j == 0 && h < 64) first_h[h].add(weight);
        }
    }

    auto print = [exponent, n](const char* name, const Row& row) {
        std::cout << exponent << ',' << name << ',' << row.signed_weight / n << ','
                  << row.absolute_weight / n << ',' << row.terms << '\n';
    };
    std::cout << std::fixed << std::setprecision(12);
    for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
            const char name[] = {'A', static_cast<char>('0' + i), static_cast<char>('0' + j), '\0'};
            print(name, rows[i][j]);
        }
    }
    print("actual_low", low_actual);
    std::cout << exponent << ",mobius_correlation," << mobius_correlation / n << ",0,0\n";
    for (u32 h = 2; h < 64; ++h) {
        if (first_h[h].terms == 0) continue;
        const std::string name = "A20_h" + std::to_string(h);
        print(name.c_str(), first_h[h]);
    }
}

int main(int argc, char** argv) {
    std::cout << "k,row,signed_per_N,absolute_per_N,nonzero_terms\n";
    for (int i = 1; i < argc; ++i) replay(std::atoi(argv[i]));
}
