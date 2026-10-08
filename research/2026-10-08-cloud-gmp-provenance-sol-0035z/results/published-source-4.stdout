#include "certified_forward_gmp.hpp"
#include <algorithm>
#include <array>
#include <utility>

namespace certified_forward_gmp {
namespace {
mpq_class canonical(mpq_class value) {
  if (value.get_den() == 0) throw Refusal("ZeroDivisionError", "");
  value.canonicalize();
  return value;
}
mpq_class fraction(const mpz_class& numerator, const mpz_class& denominator) {
  return canonical(mpq_class(numerator, denominator));
}
mpz_class power_two(unsigned long bits) {
  mpz_class scale = 1;
  mpz_mul_2exp(scale.get_mpz_t(), scale.get_mpz_t(), bits);
  return scale;
}
}  // namespace

Refusal::Refusal(std::string status, std::string message)
    : std::runtime_error(std::move(message)), status_(std::move(status)) {}

RationalInterval::RationalInterval(mpq_class lo, mpq_class hi)
    : lo_(canonical(std::move(lo))), hi_(canonical(std::move(hi))) {
  if (lo_ > hi_) throw Refusal("ValueError", "reversed interval");
}
RationalInterval RationalInterval::point(const mpq_class& value) { return {value, value}; }
mpq_class RationalInterval::width() const { return hi_ - lo_; }
bool RationalInterval::contains(const mpq_class& value) const {
  const mpq_class v = canonical(value);
  return lo_ <= v && v <= hi_;
}
bool RationalInterval::intersects(const RationalInterval& other) const {
  return std::max(lo_, other.lo_) <= std::min(hi_, other.hi_);
}
RationalInterval RationalInterval::dyadic(long bits) const {
  if (bits < 0) throw Refusal("ValueError", "negative shift count");
  const mpz_class scale = power_two(static_cast<unsigned long>(bits));
  const mpz_class lo_scaled = lo_.get_num() * scale;
  const mpz_class hi_scaled = hi_.get_num() * scale;
  mpz_class lower, upper;
  mpz_fdiv_q(lower.get_mpz_t(), lo_scaled.get_mpz_t(), lo_.get_den_mpz_t());
  mpz_cdiv_q(upper.get_mpz_t(), hi_scaled.get_mpz_t(), hi_.get_den_mpz_t());
  return {fraction(lower, scale), fraction(upper, scale)};
}
RationalInterval RationalInterval::unit_intersection() const {
  return {std::max(mpq_class(0), lo_), std::min(mpq_class(1), hi_)};
}
RationalInterval operator+(const RationalInterval& a, const RationalInterval& b) {
  return {a.lo() + b.lo(), a.hi() + b.hi()};
}
RationalInterval operator-(const RationalInterval& a) { return {-a.hi(), -a.lo()}; }
RationalInterval operator-(const RationalInterval& a, const RationalInterval& b) {
  return a + -b;
}
RationalInterval operator*(const RationalInterval& a, const RationalInterval& b) {
  const std::array<mpq_class, 4> products = {
      a.lo()*b.lo(), a.lo()*b.hi(), a.hi()*b.lo(), a.hi()*b.hi()};
  const auto extrema = std::minmax_element(products.begin(), products.end());
  return {*extrema.first, *extrema.second};
}
RationalInterval operator/(const RationalInterval& a, const mpq_class& scalar) {
  const mpq_class value = canonical(scalar);
  if (value == 0) throw Refusal("ZeroDivisionError", "");
  return a * (mpq_class(1) / value);
}
RationalInterval operator+(const RationalInterval& a, const mpq_class& scalar) {
  return a + RationalInterval::point(scalar);
}
RationalInterval operator+(const mpq_class& scalar, const RationalInterval& a) { return a + scalar; }
RationalInterval operator-(const RationalInterval& a, const mpq_class& scalar) {
  return a - RationalInterval::point(scalar);
}
RationalInterval operator-(const mpq_class& scalar, const RationalInterval& a) {
  return RationalInterval::point(scalar) - a;
}
RationalInterval operator*(const RationalInterval& a, const mpq_class& scalar) {
  return a * RationalInterval::point(scalar);
}
RationalInterval operator*(const mpq_class& scalar, const RationalInterval& a) { return a * scalar; }

RationalInterval exp_neg(const ForwardInput& x, const ForwardInput& bits) {
  mpq_class value;
  if (const auto* q = std::get_if<mpq_class>(&x)) value = canonical(*q);
  else if (const auto* z = std::get_if<mpz_class>(&x)) value = mpq_class(*z);
  else throw Refusal("DomainError", "exact rational exponential input required");
  const auto* precision = std::get_if<mpz_class>(&bits);
  if (value < 0 || precision == nullptr || *precision < 8 || *precision > 192)
    throw Refusal("DomainError", "exponential domain/precision");
  const unsigned long output_bits = precision->get_ui();
  if (value == 0) return RationalInterval::point(mpq_class(1));
  if (value >= mpq_class(*precision))
    return {mpq_class(0), fraction(mpz_class(1), power_two(output_bits))};

  mpq_class u = value;
  unsigned long m = 0;
  while (u > 1) { u /= 2; ++m; }
  const unsigned long q = output_bits + m + 4;
  const mpq_class tolerance = fraction(mpz_class(1), power_two(q));
  mpq_class lower = 0, upper = 1, sum = 1, term = 1;
  bool stopped = false;
  for (unsigned long j = 1; j <= 512; ++j) {
    term *= u / j;
    if (j % 2) { sum -= term; lower = sum; }
    else { sum += term; upper = sum; }
    if (upper - lower <= tolerance) { stopped = true; break; }
  }
  if (!stopped) throw Refusal("ResourceBound", "Taylor term cap exceeded");
  RationalInterval answer = RationalInterval(lower, upper).dyadic(static_cast<long>(q)).unit_intersection();
  for (unsigned long i = 0; i < m; ++i)
    answer = RationalInterval(answer.lo()*answer.lo(), answer.hi()*answer.hi())
        .dyadic(static_cast<long>(q)).unit_intersection();
  if (answer.width() > fraction(mpz_class(1), power_two(output_bits)))
    throw Refusal("ArithmeticError", "exponential width contract failed");
  return answer;
}
std::string rational_text(const mpq_class& value) { return canonical(value).get_str(); }

}  // namespace certified_forward_gmp
