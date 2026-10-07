#include "rc_count.h"
#include <gmp.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define RAW_LIMIT 158U
#define DIGIT_LIMIT 78U
#define INPUT_BITS 256U

typedef struct { char *data; size_t used, capacity; int failed; } Buffer;

static void append(Buffer *b, const char *text) {
    size_t n, required, capacity;
    char *next;
    if (b->failed) return;
    n = strlen(text);
    if (n > SIZE_MAX - b->used - 1U) { b->failed = 1; return; }
    required = b->used + n + 1U;
    if (required > b->capacity) {
        capacity = b->capacity ? b->capacity : 256U;
        while (capacity < required) {
            if (capacity > SIZE_MAX / 2U) { capacity = required; break; }
            capacity *= 2U;
        }
        next = (char *)realloc(b->data, capacity);
        if (!next) { b->failed = 1; return; }
        b->data = next; b->capacity = capacity;
    }
    memcpy(b->data + b->used, text, n + 1U); b->used += n;
}

static void append_uint(Buffer *b, uint64_t value) {
    char text[32];
    (void)snprintf(text, sizeof text, "%" PRIu64, value); append(b, text);
}

static void append_q(Buffer *b, const mpq_t value) {
    void (*release)(void *, size_t);
    char *text = mpq_get_str(NULL, 10, value);
    if (!text) { b->failed = 1; return; }
    append(b, "\""); append(b, text); append(b, "\"");
    mp_get_memory_functions(NULL, NULL, &release);
    release(text, strlen(text) + 1U);
}

static void set_uint(mpq_t value, uint64_t integer, unsigned offset) {
    mpz_import(mpq_numref(value), 1U, 1, sizeof integer, 0, 0U, &integer);
    mpz_add_ui(mpq_numref(value), mpq_numref(value), offset);
    mpz_set_ui(mpq_denref(value), 1U);
}

/* Bound the raw grammar before integer or rational allocation. */
static int parse_q(mpq_t result, const char *text) {
    char copy[RAW_LIMIT + 1U];
    size_t n = 0U, at = 0U, digits = 0U, slash = 0U;
    int has_slash = 0;
    if (!text) return 0;
    while (n <= RAW_LIMIT && text[n] != '\0') ++n;
    if (n == 0U || n > RAW_LIMIT) return 0;
    if (text[at] == '-') ++at;
    while (at < n && text[at] >= '0' && text[at] <= '9') { ++at; ++digits; }
    if (digits == 0U || digits > DIGIT_LIMIT) return 0;
    if (at < n && text[at] == '/') {
        has_slash = 1; slash = at++; digits = 0U;
        while (at < n && text[at] >= '0' && text[at] <= '9') { ++at; ++digits; }
        if (digits == 0U || digits > DIGIT_LIMIT) return 0;
    }
    if (at != n) return 0;
    memcpy(copy, text, n); copy[n] = '\0';
    if (has_slash) copy[slash] = '\0';
    if (mpz_set_str(mpq_numref(result), copy, 10) != 0) return 0;
    if (has_slash) {
        if (mpz_set_str(mpq_denref(result), copy + slash + 1U, 10) != 0) return 0;
    } else mpz_set_ui(mpq_denref(result), 1U);
    if (mpz_sgn(mpq_denref(result)) <= 0 ||
        mpz_sizeinbase(mpq_numref(result), 2) > INPUT_BITS ||
        mpz_sizeinbase(mpq_denref(result), 2) > INPUT_BITS) return 0;
    mpq_canonicalize(result); return 1;
}

static int invalid(char **out, const char *reason) {
    Buffer b = {NULL, 0U, 0U, 0};
    append(&b, "{\"status\":\"INVALID_INPUT\",\"error\":\"");
    append(&b, reason); append(&b, "\"}");
    if (b.failed) { free(b.data); return 3; }
    *out = b.data; return 2;
}

void rc_count_free(char *json) { free(json); }

int rc_count_certificate_json(const char *a_text, const char *epsilon_text,
                              uint64_t max_steps, int has_limit,
                              int include_weights, char **out_json) {
    mpq_t a, epsilon, term, prefix, next, twice_next, upper, delta, divisor, twice_a, weight;
    uint64_t k = 0U, inspected = 0U, i;
    int certified = 0, code = 0, counter_limit = 0;
    Buffer b = {NULL, 0U, 0U, 0};
    if (!out_json) return 3;
    *out_json = NULL;
    if ((has_limit != 0 && has_limit != 1) ||
        (include_weights != 0 && include_weights != 1)) return invalid(out_json, "FLAGS");
    mpq_inits(a, epsilon, term, prefix, next, twice_next, upper, delta, divisor, twice_a, weight, NULL);
    if (!parse_q(a, a_text) || !parse_q(epsilon, epsilon_text)) {
        code = invalid(out_json, "RATIONAL_SYNTAX_OR_BITS"); goto done;
    }
    if (mpq_sgn(a) < 0 || mpq_sgn(epsilon) <= 0 || mpq_cmp_ui(epsilon, 1U, 1U) >= 0) {
        code = invalid(out_json, "NUMERICAL_DOMAIN"); goto done;
    }
    mpq_set_ui(term, 1U, 1U); mpq_set_ui(prefix, 1U, 1U); mpq_add(twice_a, a, a);
    while (!has_limit || inspected < max_steps) {
        if (inspected == UINT64_MAX) { counter_limit = 1; break; }
        set_uint(divisor, k, 1U); mpq_mul(next, term, a); mpq_div(next, next, divisor);
        mpq_add(twice_next, next, next); mpq_add(upper, prefix, twice_next);
        mpq_div(delta, twice_next, upper); ++inspected;
        set_uint(divisor, k, 2U);
        if (mpq_cmp(divisor, twice_a) >= 0 && mpq_cmp(delta, epsilon) <= 0) {
            certified = 1; break;
        }
        ++k; mpq_set(term, next); mpq_add(prefix, prefix, term);
    }
    append(&b, certified ? "{\"status\":\"CERTIFIED\"" : "{\"status\":\"RESOURCE_LIMIT\"");
    append(&b, ",\"law\":\"normalized_prefix\",\"a\":"); append_q(&b, a);
    append(&b, ",\"epsilon\":"); append_q(&b, epsilon);
    append(&b, ",\"inspected\":"); append_uint(&b, inspected);
    if (certified) {
        append(&b, ",\"K\":"); append_uint(&b, k);
        append(&b, ",\"S\":"); append_q(&b, prefix);
        append(&b, ",\"T\":"); append_q(&b, next);
        append(&b, ",\"U\":"); append_q(&b, upper);
        append(&b, ",\"delta\":"); append_q(&b, delta);
        if (include_weights) {
            append(&b, ",\"weights\":["); mpq_set_ui(term, 1U, 1U);
            for (i = 0U; ; ++i) {
                if (i != 0U) append(&b, ",");
                mpq_div(weight, term, prefix); append_q(&b, weight);
                if (i == k || b.failed) break;
                set_uint(divisor, i, 1U); mpq_mul(term, term, a); mpq_div(term, term, divisor);
            }
            append(&b, "]");
        }
    } else {
        append(&b, ",\"next_K\":"); append_uint(&b, k);
        if (counter_limit) append(&b, ",\"resource_reason\":\"UINT64_COUNTER\"");
    }
    append(&b, "}");
    if (b.failed) { free(b.data); code = 3; } else *out_json = b.data;
done:
    mpq_clears(a, epsilon, term, prefix, next, twice_next, upper, delta, divisor, twice_a, weight, NULL);
    return code;
}
