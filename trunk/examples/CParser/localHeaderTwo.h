/*
 * Header file that can be included as source file in test C programs where
 * this source file is located using the
 *
 *   # include "q-char-sequence" new-line
 *
 * preprocessor directive (see C standard, section 6.10.2).
 */

static inline int funcFromLocalHeaderTwo(void)
{
    int var = 5;
    return var;
}
