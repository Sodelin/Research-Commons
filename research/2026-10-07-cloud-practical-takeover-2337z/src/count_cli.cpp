#include "rc_count.h"
#include <charconv>
#include <cstdint>
#include <cstdio>
#include <cstring>

static int invalid_arguments() {
    std::puts("{\"status\":\"INVALID_INPUT\",\"error\":\"ARGUMENTS\"}");
    return 2;
}

int main(int argc, char **argv) {
    if (argc < 3) return invalid_arguments();
    std::uint64_t max_steps = 0;
    int has_limit = 0, include_weights = 0;
    for (int i = 3; i < argc; ++i) {
        if (std::strcmp(argv[i], "--weights") == 0 && !include_weights) include_weights = 1;
        else if (std::strcmp(argv[i], "--max-steps") == 0 && !has_limit && i + 1 < argc) {
            const char *begin = argv[++i], *end = begin + std::strlen(begin);
            auto parsed = std::from_chars(begin, end, max_steps);
            if (begin == end || parsed.ec != std::errc() || parsed.ptr != end) return invalid_arguments();
            has_limit = 1;
        } else return invalid_arguments();
    }
    char *json = nullptr;
    int code = rc_count_certificate_json(argv[1], argv[2], max_steps, has_limit, include_weights, &json);
    if (json) { std::puts(json); rc_count_free(json); }
    else std::fputs("count kernel allocation/internal failure; no certificate\n", stderr);
    return code;
}
