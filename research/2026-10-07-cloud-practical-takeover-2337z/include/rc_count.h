#ifndef RC_COUNT_H
#define RC_COUNT_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Exact normalized Poisson-prefix numerical certificate, not a JC solver.
 * Inputs: bounded ASCII integer or n/positive-d; flags must be 0 or 1.
 * Return 0: complete CERTIFIED or RESOURCE_LIMIT JSON; 2: invalid-input JSON;
 * 3: allocation/internal failure (out_json may be NULL). Caller owns JSON and
 * must release it with rc_count_free. out_json must be non-NULL and is cleared
 * before work. GMP allocation failure remains fatal under GMP's allocator;
 * an externally killed/failing process publishes no certificate.
 * has_limit=0 ignores max_steps; has_limit=1 counts inspected cutoffs.
 * include_weights=1 adds exact normalized weights only on CERTIFIED.
 */
int rc_count_certificate_json(const char *a, const char *epsilon,
                              uint64_t max_steps, int has_limit,
                              int include_weights, char **out_json);
void rc_count_free(char *json);

#ifdef __cplusplus
}
#endif
#endif
