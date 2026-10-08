#include "certified_forward_gmp.hpp"
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using namespace certified_forward_gmp;
namespace {
constexpr std::size_t max_line = 65536, max_numeric = 8192;
constexpr unsigned long max_probe_shift = 65536;
class ParserRefusal : public Refusal { public: using Refusal::Refusal; };

bool read_line(std::string& line, bool& overflow) {
  line.clear(); overflow = false;
  char c;
  bool any = false;
  while (std::cin.get(c)) {
    any = true;
    if (c == '\n') break;
    if (line.size() < max_line) line.push_back(c);
    else overflow = true;
  }
  return any;
}
bool digits(const std::string& text, std::size_t start) {
  if (start == text.size()) return false;
  for (std::size_t i = start; i < text.size(); ++i)
    if (text[i] < '0' || text[i] > '9') return false;
  return true;
}
void text_bound(const std::string& text) {
  if (text.size() > max_numeric)
    throw ParserRefusal("ResourceBound", "probe numeric text exceeds8192 characters");
}
mpz_class integer(const std::string& text) {
  text_bound(text);
  if (text.empty() || !digits(text, text[0] == '-' ? 1 : 0))
    throw ParserRefusal("DomainError", "integer decimal string required");
  return mpz_class(text, 10);
}
mpq_class rational(const std::string& text) {
  text_bound(text);
  const auto slash = text.find('/');
  const std::string num = text.substr(0, slash);
  if (num.empty() || !digits(num, num[0] == '-' ? 1 : 0))
    throw ParserRefusal("DomainError", "integer or rational n/d string required");
  mpz_class denominator = 1;
  if (slash != std::string::npos) {
    const std::string den = text.substr(slash + 1);
    if (den.empty() || den[0] < '1' || den[0] > '9' || !digits(den, 0))
      throw ParserRefusal("DomainError", "integer or rational n/d string required");
    denominator = mpz_class(den, 10);
  }
  mpq_class result(mpz_class(num, 10), denominator);
  result.canonicalize();
  return result;
}
ForwardInput typed(const std::string& text) {
  if (text.size() < 2 || text[1] != ':')
    throw ParserRefusal("DomainError", "typed exponential token required");
  const std::string value = text.substr(2);
  switch (text[0]) {
    case 'i': return integer(value);
    case 'q': return rational(value);
    case 'b': return NonExactType::boolean;
    case 'f': return NonExactType::floating;
    case 's': return NonExactType::string;
    default: throw ParserRefusal("DomainError", "unknown exponential type tag");
  }
}
std::string quote(const std::string& text) {
  static constexpr char hex[] = "0123456789abcdef";
  std::string out = "\"";
  for (unsigned char c : text) {
    if (c == '"' || c == '\\') { out.push_back('\\'); out.push_back(static_cast<char>(c)); }
    else if (c < 32) { out += "\\u00"; out.push_back(hex[c >> 4]); out.push_back(hex[c & 15]); }
    else out.push_back(static_cast<char>(c));
  }
  return out + '"';
}
void interval_record(const RationalInterval& value) {
  std::cout << "{\"status\":\"ok\",\"kind\":\"interval\",\"lower\":" << quote(rational_text(value.lo()))
    << ",\"upper\":" << quote(rational_text(value.hi()))
    << ",\"width\":" << quote(rational_text(value.width())) << "}\n";
}
void boolean_record(bool value) {
  std::cout << "{\"status\":\"ok\",\"kind\":\"boolean\",\"value\":" << (value ? "true" : "false") << "}\n";
}
void refusal_record(const Refusal& error, const char* phase) {
  std::cout << "{\"status\":" << quote(error.status()) << ",\"message\":" << quote(error.what())
    << ",\"phase\":" << quote(phase) << "}\n";
}
void count(const std::vector<std::string>& tokens, std::size_t expected) {
  if (tokens.size() != expected) throw ParserRefusal("DomainError", "probe argument count");
}
void run(const std::vector<std::string>& t) {
  if (t.empty()) throw ParserRefusal("DomainError", "empty probe command");
  const std::string& op = t[0];
  if (op == "exp") { count(t, 3); interval_record(exp_neg(typed(t[1]), typed(t[2]))); return; }
  if (op == "point") { count(t, 2); interval_record(RationalInterval::point(rational(t[1]))); return; }
  if (op == "add" || op == "sub" || op == "mul" || op == "intersects") {
    count(t, 5);
    const RationalInterval a(rational(t[1]), rational(t[2])), b(rational(t[3]), rational(t[4]));
    if (op == "add") interval_record(a+b);
    else if (op == "sub") interval_record(a-b);
    else if (op == "mul") interval_record(a*b);
    else boolean_record(a.intersects(b));
    return;
  }
  if (op == "neg" || op == "width" || op == "unit") {
    count(t, 3); const RationalInterval a(rational(t[1]), rational(t[2]));
    if (op == "neg") interval_record(-a);
    else if (op == "unit") interval_record(a.unit_intersection());
    else std::cout << "{\"status\":\"ok\",\"kind\":\"rational\",\"value\":" << quote(rational_text(a.width())) << "}\n";
    return;
  }
  if (op == "dyadic") {
    count(t, 4); const RationalInterval a(rational(t[1]), rational(t[2]));
    const mpz_class bits = integer(t[3]);
    if (bits < 0) interval_record(a.dyadic(-1));
    else if (bits > max_probe_shift) throw ParserRefusal("ResourceBound", "probe dyadic shift exceeds65536");
    else interval_record(a.dyadic(bits.get_si()));
    return;
  }
  if (op == "div" || op == "contains" || op == "add_scalar" || op == "radd" ||
      op == "sub_scalar" || op == "rsub" || op == "mul_scalar" || op == "rmul") {
    count(t, 4); const RationalInterval a(rational(t[1]), rational(t[2]));
    const mpq_class scalar = rational(t[3]);
    if (op == "div") interval_record(a/scalar);
    else if (op == "contains") boolean_record(a.contains(scalar));
    else if (op == "add_scalar") interval_record(a+scalar);
    else if (op == "radd") interval_record(scalar+a);
    else if (op == "sub_scalar") interval_record(a-scalar);
    else if (op == "rsub") interval_record(scalar-a);
    else if (op == "mul_scalar") interval_record(a*scalar);
    else interval_record(scalar*a);
    return;
  }
  throw ParserRefusal("DomainError", "unknown probe command");
}
}  // namespace

int main() {
  std::string line; bool overflow;
  while (read_line(line, overflow)) {
    try {
      if (overflow) throw ParserRefusal("ResourceBound", "probe line exceeds65536 bytes");
      std::istringstream input(line); std::vector<std::string> tokens; std::string token;
      while (input >> token) tokens.push_back(token);
      run(tokens);
    } catch (const ParserRefusal& error) { refusal_record(error, "parser"); }
      catch (const Refusal& error) { refusal_record(error, "primitive"); }
      catch (const std::exception& error) {
        std::cout << "{\"status\":\"InternalError\",\"message\":" << quote(error.what()) << "}\n";
      }
  }
  return 0;
}
