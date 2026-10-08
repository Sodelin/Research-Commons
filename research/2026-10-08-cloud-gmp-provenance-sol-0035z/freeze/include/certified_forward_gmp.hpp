#pragma once

// CLOUD-GMP-INTERVAL-SOL-2354Z. Exact port of pinned Python c8487100 lines34-89.
// The library has no reduced-rational bit cap. Probe limits are separate.
#include <gmpxx.h>
#include <stdexcept>
#include <string>
#include <variant>

namespace certified_forward_gmp {

class Refusal : public std::runtime_error {
 public:
  Refusal(std::string status, std::string message);
  const std::string& status() const noexcept { return status_; }
 private:
  std::string status_;
};

class RationalInterval {
 public:
  RationalInterval(mpq_class lo, mpq_class hi);
  static RationalInterval point(const mpq_class& value);
  const mpq_class& lo() const noexcept { return lo_; }
  const mpq_class& hi() const noexcept { return hi_; }
  mpq_class width() const;
  bool contains(const mpq_class& value) const;
  bool intersects(const RationalInterval& other) const;
  RationalInterval dyadic(long bits) const;
  RationalInterval unit_intersection() const;
 private:
  mpq_class lo_, hi_;
};

RationalInterval operator+(const RationalInterval& a, const RationalInterval& b);
RationalInterval operator-(const RationalInterval& a);
RationalInterval operator-(const RationalInterval& a, const RationalInterval& b);
RationalInterval operator*(const RationalInterval& a, const RationalInterval& b);
RationalInterval operator/(const RationalInterval& a, const mpq_class& scalar);
RationalInterval operator+(const RationalInterval& a, const mpq_class& scalar);
RationalInterval operator+(const mpq_class& scalar, const RationalInterval& a);
RationalInterval operator-(const RationalInterval& a, const mpq_class& scalar);
RationalInterval operator-(const mpq_class& scalar, const RationalInterval& a);
RationalInterval operator*(const RationalInterval& a, const mpq_class& scalar);
RationalInterval operator*(const mpq_class& scalar, const RationalInterval& a);

// Invalid Python-type descriptors need no floating-point payload/computation.
enum class NonExactType { boolean, floating, string, other };
using ForwardInput = std::variant<mpz_class, mpq_class, NonExactType>;
RationalInterval exp_neg(const ForwardInput& x, const ForwardInput& bits);
std::string rational_text(const mpq_class& value);

}  // namespace certified_forward_gmp
