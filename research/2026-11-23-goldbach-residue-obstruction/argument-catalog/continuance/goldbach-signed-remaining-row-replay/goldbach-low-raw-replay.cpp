#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

struct Low {
    long double actual = 0;
    long double model = 0;
    long double q3 = 0;
};

std::uint32_t totient(std::uint32_t value) {
    std::uint32_t result = value;
    for (std::uint32_t p = 2; p * p <= value; ++p) {
        if (value % p != 0) continue;
        result -= result / p;
        do { value /= p; } while (value % p == 0);
    }
    if (value > 1) result -= result / value;
    return result;
}

int main(int argc, char** argv) {
    const unsigned max_k = argc == 2 ? std::stoul(argv[1]) : 28;
    assert(max_k >= 20 && max_k <= 28 && max_k % 2 == 0);
    const std::uint32_t limit = std::uint32_t{1} << max_k;
    std::vector<std::int8_t> mu(limit + 1);
    std::vector<std::uint32_t> primes;
    mu[1] = 1;
    {
        std::vector<std::uint32_t> least(limit + 1);
        for (std::uint32_t i = 2; i <= limit; ++i) {
            if (least[i] == 0) {
                least[i] = i;
                mu[i] = -1;
                primes.push_back(i);
            }
            for (std::uint32_t p : primes) {
                const std::uint64_t product = std::uint64_t(i) * p;
                if (product > limit || p > least[i]) break;
                least[product] = p;
                mu[product] = p == least[i] ? 0 : -mu[i];
            }
        }
    }

    long double log_series = std::log(2.L);
    std::vector<double> lambda(limit + 1);
    for (std::uint32_t prime : primes) {
        if (prime > 2) {
            const long double p_minus1 = prime - 1;
            log_series += std::log1p(-1.L / (p_minus1 * p_minus1));
        }
        const double log_prime = std::log(double(prime));
        for (std::uint64_t pow = prime; pow <= limit; pow *= prime) {
            lambda[pow] = log_prime;
        }
    }
    const long double series_hi = std::exp(log_series);
    const long double series_lo = series_hi * (1.L - 1.L / (limit - 1));
    std::cout << std::setprecision(13);
    std::cout << "# singular series interval " << series_lo << ' ' << series_hi << '\n';
    std::cout << "# k alphaQ C/N M0lo/N M0hi/N actual0/N model0/N E0/N E3_0/N "
                 "actualH/N modelH/N EH/N E3_H/N\n";
    for (unsigned k = 20; k <= max_k; k += 2) {
        const std::uint32_t N = std::uint32_t{1} << k;
        const std::uint32_t H = std::uint32_t{1} << (k / 2);
        const long double L = std::log(static_cast<long double>(N));
        const long double alphaQ = H * std::sqrt(static_cast<long double>(H)) / std::pow(L, 5);
        assert(alphaQ < 1);
        const std::uint32_t historical_alpha = H / 2;
        long double C = 0;
        long double C_log = 0;
        auto endpoint = [&](std::uint32_t m) -> long double {
            return static_cast<long double>(mu[m]) * lambda[N - m];
        };
        for (std::uint32_t m = 1; m < N; ++m) {
            const long double value = endpoint(m);
            if (value == 0) continue;
            C += value;
            C_log += value * std::log(double(m));
        }

        Low analytic, historical;
        std::uint32_t removed_m = 0;
        long double removed = 0;
        long double removed_log = 0;
        for (std::uint32_t q = 1; ; q += 2) {
            const std::uint64_t q_squared = std::uint64_t(q) * q;
            if (q_squared * q_squared >= N) break;
            if (mu[q] == 0) continue;
            const std::uint32_t threshold = q * historical_alpha;
            while (removed_m < threshold) {
                const auto m = ++removed_m;
                const long double value = endpoint(m);
                if (value == 0) continue;
                removed += value;
                removed_log += value * std::log(double(m));
            }
            const long double log_q = std::log(double(q));
            const long double model_multiplier = static_cast<long double>(mu[q]) / totient(q);
            const long double model0 = model_multiplier * (log_q * C - C_log);
            const long double model1 = model_multiplier *
                (log_q * (C - removed) - (C_log - removed_log));
            long double actual0 = 0;
            long double actual1 = 0;
            if (q == 1) {
                actual0 = model0;
                actual1 = model1;
            } else {
                for (std::uint32_t m = q, h = 1; m < N; m += q, ++h) {
                    if (mu[m] == 0 || lambda[N - m] == 0) continue;
                    const long double weight = -static_cast<long double>(mu[q]) *
                        endpoint(m) * std::log(double(h));
                    actual0 += weight;
                    if (h > historical_alpha) actual1 += weight;
                }
            }
            analytic.actual += actual0;
            analytic.model += model0;
            historical.actual += actual1;
            historical.model += model1;
            if (q == 3) {
                analytic.q3 = actual0 - model0;
                historical.q3 = actual1 - model1;
            }
        }
        if (k == 20) {
            long double independent[2] = {0, 0};
            for (std::uint32_t m = 1; m < N; ++m) {
                const long double value = endpoint(m);
                if (value == 0) continue;
                for (std::uint32_t q = 3; q < 32; q += 2) {
                    if (mu[q] == 0) continue;
                    const long double coeff = static_cast<long double>(m % q == 0)
                        - 1.L / totient(q);
                    const long double weight = value * mu[q] * coeff *
                        std::log(static_cast<long double>(q) / m);
                    independent[0] += weight;
                    if (m > q * historical_alpha) independent[1] += weight;
                }
            }
            assert(std::abs(independent[0] - (analytic.actual - analytic.model)) < 1e-6L);
            assert(std::abs(independent[1] - (historical.actual - historical.model)) < 1e-6L);
        }
        auto write = [&](const Low& row) {
            std::cout << ' ' << row.actual / N << ' ' << row.model / N
                      << ' ' << (row.actual - row.model) / N << ' ' << row.q3 / N;
        };
        std::cout << k << ' ' << alphaQ << ' ' << C / N << ' '
                  << series_lo * (1 - C / N) << ' ' << series_hi * (1 - C / N);
        write(analytic);
        write(historical);
        std::cout << std::endl;
    }
}
