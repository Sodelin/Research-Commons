#include "rc_count.h"
#include <assert.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

static int fail_allocation = 0;
void *__real_realloc(void *, size_t);
void *__wrap_realloc(void *p, size_t n) {
    return fail_allocation ? NULL : __real_realloc(p, n);
}

int main(void) {
    char *json = NULL;
    assert(rc_count_certificate_json("0", "1/4", 1, 1, 1, &json) == 0);
    assert(json && strstr(json, "\"status\":\"CERTIFIED\"") && strstr(json, "\"weights\":[\"1\"]"));
    rc_count_free(json); json = NULL;
    assert(rc_count_certificate_json(NULL, "1/4", 1, 1, 0, &json) == 2);
    assert(json && strstr(json, "INVALID_INPUT")); rc_count_free(json);
    assert(rc_count_certificate_json("0", "1/4", 1, 2, 0, &json) == 2);
    rc_count_free(json);
    assert(rc_count_certificate_json("0", "1/4", 1, 1, 2, &json) == 2);
    rc_count_free(json);
    assert(rc_count_certificate_json("0", "1/4", 1, 1, 0, NULL) == 3);
    fail_allocation = 1;
    assert(rc_count_certificate_json("0", "1/4", 1, 1, 0, &json) == 3 && json == NULL);
    assert(rc_count_certificate_json("bad", "1/4", 1, 1, 0, &json) == 3 && json == NULL);
    fail_allocation = 0;
    rc_count_free(NULL);
    return 0;
}
