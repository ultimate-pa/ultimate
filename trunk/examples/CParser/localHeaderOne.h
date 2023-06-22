/*
 * Header file that can be included as source file in test C programs where
 * this source file is located using the
 *
 *   # include "q-char-sequence" new-line
 *
 * preprocessor directive (see C standard, section 6.10.2).
 */

typedef struct status {
    int retval;
} status_t;

static inline status_t funcFromLocalHeaderOne(void)
{
    status_t ret = { .retval = 3 };
    return ret;
}
