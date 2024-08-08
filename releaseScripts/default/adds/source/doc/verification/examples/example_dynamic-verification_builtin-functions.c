/*
 * Copyright (C) 2024 Manuel Bentele
 * 
 * This file is part of the ULTIMATE program analysis framework.
 * 
 * The ULTIMATE program analysis framework is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 * 
 * The ULTIMATE program analysis framework is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE program analysis
 * framework. If not, see http://www.gnu.org/licenses/.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE program analysis framework, or
 * any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing
 * parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE program analysis framework
 * grant you additional permission to convey the resulting work.
 */

/**
 * Example program to show use of built-in verification functions for dynamic verification (runtime verification).
 * 
 * The example program can be compiled with a C compiler (e.g. GNU C compiler) and can then be executed.
 * 
 * \author Manuel Bentele
 * \version 0.2.4
 */

/**
 * Select functions and data types for dynamic program analysis (runtime verification).
 * 
 * \note This macro must be defined before including the <verification/verification.h> header file.
 */
#define DYNAMIC_VERIFICATION

#include <stdio.h>
#include <verification/verification.h>

/**
 * Entry point of the example program using built-in verification functions for dynamic (runtime) verification.
 * 
 * \return Returns the status code value 17 which is used as the argument to the implicit call to exit().
 * 
 * \note The example program does not terminate successfully because a call to __VERIFIER_error() occurs shortly before
 *       the end of execution. Thus the program contains an error and is not correct.
 */
int main(void)
{
    int ret = 17;

    __VERIFIER_assume(ret == 17);

    __VERIFIER_atomic_begin();
    __VERIFIER_atomic_end();

    printf("__VERIFIER_nondet_bool: %d\n", __VERIFIER_nondet_bool());
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L && __STDC_VERSION__ <= 201710L
    printf("__VERIFIER_nondet__Bool: %d\n", __VERIFIER_nondet__Bool());
#endif
    printf("__VERIFIER_nondet_char: %d\n", __VERIFIER_nondet_char());
    printf("__VERIFIER_nondet_uchar: %u\n", __VERIFIER_nondet_uchar());
    printf("__VERIFIER_nondet_pchar: %p\n", __VERIFIER_nondet_pchar());
    printf("__VERIFIER_nondet_short: %d\n", __VERIFIER_nondet_short());
    printf("__VERIFIER_nondet_ushort: %u\n", __VERIFIER_nondet_ushort());
    printf("__VERIFIER_nondet_unsigned: %u\n", __VERIFIER_nondet_unsigned());
    printf("__VERIFIER_nondet_int: %d\n", __VERIFIER_nondet_int());
    printf("__VERIFIER_nondet_uint: %u\n", __VERIFIER_nondet_uint());
    printf("__VERIFIER_nondet_size_t: %lu\n", __VERIFIER_nondet_size_t());
#if defined(_GNU_SOURCE)
    printf("__VERIFIER_nondet_loff_t: %ld\n", __VERIFIER_nondet_loff_t());
#endif
    printf("__VERIFIER_nondet_long: %ld\n", __VERIFIER_nondet_long());
    printf("__VERIFIER_nondet_ulong: %lu\n", __VERIFIER_nondet_ulong());
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
    printf("__VERIFIER_nondet_longlong: %lld\n", __VERIFIER_nondet_longlong());
    printf("__VERIFIER_nondet_ulonglong: %llu\n", __VERIFIER_nondet_ulonglong());
#endif
#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
# if defined(__STDC_VERSION__) && 202311L <= __STDC_VERSION__
    /* Format specifier for printing 128-bit decimal values is available since C23 and later. */
    printf("__VERIFIER_nondet_int128: %w128d\n", __VERIFIER_nondet_int128());
    printf("__VERIFIER_nondet_uint128: %w128u\n", __VERIFIER_nondet_uint128());
# else
    /* Use largest legacy format specifier for printing part of the 128-bit decimal value. */
    printf("__VERIFIER_nondet_int128: %lld\n", (long long) __VERIFIER_nondet_int128());
    printf("__VERIFIER_nondet_uint128: %llu\n", (unsigned long long) __VERIFIER_nondet_uint128());
# endif
#endif
    printf("__VERIFIER_nondet_float: %f\n", __VERIFIER_nondet_float());
    printf("__VERIFIER_nondet_double: %lf\n", __VERIFIER_nondet_double());
    printf("__VERIFIER_nondet_pointer: %p\n", __VERIFIER_nondet_pointer());

    __VERIFIER_error();

    return ret;
}
