#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

#include <gmpxx.h>

using Clock = std::chrono::steady_clock;

namespace {

using UInt = std::uint32_t;
using Wide = std::uint64_t;
constexpr std::size_t max_factors = 16;

enum Category { semiprime, higher_removed, higher_remainder, category_count };
const char* category_names[] = {"semiprime", "higher_045_slice", "higher_remainder"};

struct Factors {
    std::array<UInt, max_factors> primes{};
    std::size_t count = 0;
    bool squarefree = true;
};

struct Sum {
    long double total = 0;
    long double correction = 0;

    void add(long double term) {
        const long double residual = term - correction;
        const long double next = total + residual;
        correction = (next - total) - residual;
        total = next;
    }
};

struct Row {
    Wide candidates = 0;
    Wide positive = 0;
    Wide negative = 0;
    Sum signed_weight;
    Sum absolute_weight;

    void add(long double weight, int sign) {
        ++candidates;
        positive += sign > 0;
        negative += sign < 0;
        signed_weight.add(weight);
        absolute_weight.add(std::fabs(weight));
    }
};

struct Thresholds {
    UInt P_floor;
    UInt slice_min;
    UInt y0;
    UInt z1;
    UInt middle_lo;
    UInt middle_hi;
    UInt mark_lo;
    UInt mark_hi;
    UInt cutoff_9896;
    UInt cutoff_95;
    UInt min_middle;
    UInt max_middle;
    UInt min_9896;
    UInt min_95;

};

mpz_class power(UInt base, unsigned exponent) {
    mpz_class result;
    mpz_ui_pow_ui(result.get_mpz_t(), base, exponent);
    return result;
}

class OddFactorTable {
public:
    explicit OddFactorTable(UInt bound) : smallest_(bound / 2 + 1, 0) {
        for (UInt p = 3; Wide(p) * p <= bound; p += 2) {
            if (smallest_[p / 2] != 0) continue;
            const Wide step = 2 * Wide(p);
            for (Wide composite = Wide(p) * p; composite <= bound; composite += step) {
                auto& slot = smallest_[composite / 2];
                if (slot == 0) slot = static_cast<std::uint16_t>(p);
            }
        }
    }

    Factors factor(UInt value) const {
        Factors result;
        while (value > 1) {
            const UInt first = smallest_[value / 2];
            const UInt p = first == 0 ? value : first;
            result.primes[result.count++] = p;
            value /= p;
            while (value % p == 0) {
                result.squarefree = false;
                value /= p;
            }
        }
        return result;
    }

private:
    std::vector<std::uint16_t> smallest_;
};

struct CofactorData {
    int mu = 0;
    unsigned middle = 0;
    unsigned marks = 0;
    unsigned below_9896 = 0;
    unsigned below_95 = 0;
    long double logarithm = 0;
};

CofactorData cofactor_data(UInt value, const Factors& factors, const Thresholds& t) {
    CofactorData result;
    if (!factors.squarefree) return result;
    result.mu = factors.count % 2 == 0 ? 1 : -1;
    result.logarithm = std::log(static_cast<long double>(value));
    for (std::size_t index = 0; index < factors.count; ++index) {
        const UInt p = factors.primes[index];
        result.middle += p > t.middle_lo && p <= t.middle_hi;
        result.marks += p > t.mark_lo && p <= t.mark_hi;
        result.below_9896 += p <= t.cutoff_9896;
        result.below_95 += p <= t.cutoff_95;
    }
    return result;
}

bool center_masks(const CofactorData& q, const CofactorData& h,
                  bool odd_m, const Thresholds& t) {
    const unsigned middle = q.middle + h.middle;
    return t.min_middle <= middle && middle <= t.max_middle
        && q.marks + h.marks <= 1
        && q.below_9896 + h.below_9896 >= t.min_9896
        && (!odd_m || q.below_95 + h.below_95 >= t.min_95);
}

struct Bracket {
    long double logarithm = 0;
    int sign = 0;
};

struct DivisorEnumerator {
    const Factors& factors;
    UInt limit;
    std::array<int, max_factors> coefficients{};
    std::array<std::size_t, max_factors> included{};

    void visit(std::size_t index, UInt divisor, std::size_t occupied) {
        if (index == factors.count) {
            const int weight = occupied % 2 == 0 ? -1 : 1;
            for (std::size_t i = 0; i < occupied; ++i) coefficients[included[i]] += weight;
            return;
        }
        visit(index + 1, divisor, occupied);
        const UInt p = factors.primes[index];
        if (divisor <= limit / p) {
            included[occupied] = index;
            visit(index + 1, divisor * p, occupied + 1);
        }
    }

    Bracket evaluate() {
        visit(0, 1, 0);
        long double logarithm = 0;
        bool nonzero = false;
        for (std::size_t index = 0; index < factors.count; ++index) {
            if (coefficients[index] == 0) continue;
            nonzero = true;
            logarithm += coefficients[index] *
                std::log(static_cast<long double>(factors.primes[index]));
        }
        if (!nonzero) return {};
        if (std::fabs(logarithm) > 1e-10L) return {logarithm, logarithm < 0 ? -1 : 1};

        mpz_class numerator = 1;
        mpz_class denominator = 1;
        for (std::size_t index = 0; index < factors.count; ++index) {
            const int exponent = coefficients[index];
            if (exponent > 0) numerator *= power(factors.primes[index], exponent);
            if (exponent < 0) denominator *= power(factors.primes[index], -exponent);
        }
        return {logarithm, numerator < denominator ? -1 : 1};
    }
};

void print_row(const Row& row, UInt target) {
    std::cout << "{\"placements\":" << row.candidates
              << ",\"positive\":" << row.positive
              << ",\"negative\":" << row.negative
              << ",\"signed\":" << row.signed_weight.total
              << ",\"absolute\":" << row.absolute_weight.total
              << ",\"doubled_signed_over_N\":" << 2 * row.signed_weight.total / target
              << ",\"doubled_absolute_over_N\":" << 2 * row.absolute_weight.total / target
              << '}';
}

void run(unsigned k, const Thresholds& t) {
    if (k < 8 || k > 30) throw std::invalid_argument("exponent must be in [8,30]");
    const UInt N = UInt{1} << k;
    UInt H = static_cast<UInt>(std::sqrt(static_cast<long double>(N)));
    while (Wide(H + 1) * (H + 1) <= N) ++H;
    while (Wide(H) * H > N) --H;
    const UInt first = (H / 2 + 1) | 1U;
    const UInt last = H % 2 == 0 ? H - 1 : H;
    const UInt d_cut = t.P_floor;
    const UInt rough_slice = t.slice_min;

    const auto start = Clock::now();
    const OddFactorTable sieve(N - first * (first + 2));
    std::vector<CofactorData> factored(H + 1);
    for (UInt q = first; q <= last; q += 2) factored[q] = cofactor_data(q, sieve.factor(q), t);
    const auto sieve_end = Clock::now();

    // Cutoff, mask, block parity, and endpoint category, in that order.
    Row rows[2][2][2][category_count];
    Row raw_actual[2];
    Row marked_actual[2];
    Wide total = 0;
    for (UInt q = first; q < last; q += 2) {
        const auto& q_data = factored[q];
        if (q_data.mu == 0) continue;
        for (UInt h = q + 2; h <= last; h += 2) {
            const auto& h_data = factored[h];
            if (h_data.mu == 0 || std::gcd(q, h) != 1) continue;
            ++total;
            const UInt n = N - q * h;
            const bool odd_m = q_data.mu != h_data.mu;
            const int parity = odd_m ? 1 : 0;
            const bool marked = center_masks(q_data, h_data, odd_m, t);
            const long double paired = h_data.mu *
                (odd_m ? h_data.logarithm - q_data.logarithm
                       : h_data.logarithm + q_data.logarithm);
            const Factors factors = sieve.factor(n);
            if (factors.count == 1) {
                const long double term = -paired *
                    std::log(static_cast<long double>(factors.primes[0]));
                raw_actual[parity].add(term, -h_data.mu);
                if (marked) marked_actual[parity].add(term, -h_data.mu);
            }
            if (!factors.squarefree || factors.count == 0 || factors.count % 2 != 0) continue;
            if (factors.primes[0] <= t.y0) continue;
            const bool raised = factors.primes[0] > t.z1;
            const bool semiprime_n = factors.count == 2;
            const Category category = semiprime_n ? semiprime :
                (odd_m && factors.primes[0] >= rough_slice ? higher_removed : higher_remainder);
            Bracket bracket;
            if (semiprime_n) {
                if (factors.primes[1] > d_cut) {
                    bracket = {std::log(static_cast<long double>(factors.primes[0])), 1};
                }
            } else {
                DivisorEnumerator enumerator{factors, n / (d_cut + 1)};
                bracket = enumerator.evaluate();
            }
            const long double weight = paired * bracket.logarithm;
            const int sign = h_data.mu * bracket.sign;
            rows[0][0][parity][category].add(weight, sign);
            if (marked) rows[0][1][parity][category].add(weight, sign);
            if (raised) {
                rows[1][0][parity][category].add(weight, sign);
                if (marked) rows[1][1][parity][category].add(weight, sign);
            }
        }
    }
    const auto end = Clock::now();
    std::cout << std::setprecision(18) << "{\"k\":" << k << ",\"N\":" << N
              << ",\"P_floor\":" << d_cut << ",\"Y0_floor\":" << t.y0
              << ",\"Z1_floor\":" << t.z1 << ",\"slice_min_prime\":" << rough_slice
              << ",\"total_squarefree_pairs\":" << total
              << ",\"sieve_seconds\":" << std::chrono::duration<double>(sieve_end - start).count()
              << ",\"enumeration_seconds\":" << std::chrono::duration<double>(end - sieve_end).count()
              << ",\"raw_actual_A11\":{";
    for (int p = 0; p < 2; ++p) {
        if (p != 0) std::cout << ',';
        std::cout << (p == 0 ? "\"even\":" : "\"odd\":");
        print_row(raw_actual[p], N);
    }
    std::cout << "},\"marked_actual_A11\":{";
    for (int p = 0; p < 2; ++p) {
        if (p != 0) std::cout << ',';
        std::cout << (p == 0 ? "\"even\":" : "\"odd\":");
        print_row(marked_actual[p], N);
    }
    std::cout << "},\"rows\":{";
    for (int rough = 0; rough < 2; ++rough) {
        if (rough != 0) std::cout << ',';
        std::cout << (rough == 0 ? "\"Y0\":{" : "\"Z1\":{");
        for (int mask = 0; mask < 2; ++mask) {
            if (mask != 0) std::cout << ',';
            std::cout << (mask == 0 ? "\"raw\":{" : "\"marked\":{");
            for (int p = 0; p < 2; ++p) {
                if (p != 0) std::cout << ',';
                std::cout << (p == 0 ? "\"even\":{" : "\"odd\":{");
                for (int cat = 0; cat < category_count; ++cat) {
                    if (cat != 0) std::cout << ',';
                    std::cout << '"' << category_names[cat] << "\":";
                    print_row(rows[rough][mask][p][cat], N);
                }
                std::cout << '}';
            }
            std::cout << '}';
        }
        std::cout << '}';
    }
    std::cout << "}}\n";
}

}  // namespace

int main() {
    try {
        unsigned k;
        while (std::cin >> k) {
            Thresholds t{};
            if (!(std::cin >> t.P_floor >> t.slice_min >> t.y0 >> t.z1 >> t.middle_lo
                  >> t.middle_hi >> t.mark_lo >> t.mark_hi >> t.cutoff_9896 >> t.cutoff_95
                  >> t.min_middle >> t.max_middle >> t.min_9896 >> t.min_95)) {
                throw std::invalid_argument("incomplete threshold row");
            }
            run(k, t);
        }
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
    return 0;
}
