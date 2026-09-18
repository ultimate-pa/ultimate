/*
 * Header file that can be included as source file in test C programs where
 * this source file is located using one of the
 *
 *   # include "q-char-sequence" new-line
 *   # include <h-char-sequence> new-line
 *
 * preprocessor directives (see C standard, section 6.10.2).
 */

typedef struct ret {
    int code;
} ret_t;

static inline ret_t funcFromDirectoryHeaderOne(void)
{
    ret_t ret = { .code = 2 };
    return ret;
}
