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
 * Verification functions and data types built into Ultimate for static program analysis.
 * 
 * \author Manuel Bentele
 * \version 0.2.4
 */

#ifndef __ULTIMATE_H
#define __ULTIMATE_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include <stddef.h>
#if defined(_GNU_SOURCE)
# include <sys/types.h>
#endif

/**
 * Provides assumptions about the program's state or behavior.
 * 
 * When this function is called with a specific assumption, it instructs the verification tool to consider that
 * assumption as true for the purpose of an analysis.
 * 
 * \param assumption Expression that is used as assumption for an analysis.
 */
extern void __VERIFIER_assume(int assumption);

/**
 * Indicates an error condition.
 */
extern void __VERIFIER_error(void);

/**
 * Marks the beginning of a critical section in the program.
 * 
 * This function helps to ensure that certain operations are executed atomically, without interruption or interference
 * from other threads or processes, thereby preventing race conditions and ensuring the correctness of the program's
 * behavior.
 */
extern void __VERIFIER_atomic_begin(void);

/**
 * Marks the end of a critical section in the program.
 * 
 * This function helps to ensure that the operations within the critical section are executed atomically, without
 * interruption or interference from other threads or processes, maintaining the integrity of the program's execution
 * and preventing race conditions.
 */
extern void __VERIFIER_atomic_end(void);

/**
 * Returns a boolean value non-deterministically.
 * 
 * \return Non-deterministic boolean value.
 */
extern bool __VERIFIER_nondet_bool(void);

#if defined(__STDC_VERSION__) && 199901L <= __STDC_VERSION__ && __STDC_VERSION__ <= 201710L
/**
 * Returns a boolean value non-deterministically.
 * 
 * \return Non-deterministic boolean value.
 * 
 * \note The function is available for the boolean type _Bool, which is only defined from C99 to C20.
 */
extern _Bool __VERIFIER_nondet__Bool(void);
#endif

/**
 * Returns a signed character value non-deterministically.
 * 
 * \return  Non-deterministic signed character value.
 */
extern char __VERIFIER_nondet_char(void);

/**
 * Returns an unigned character value non-deterministically.
 * 
 * \return  Non-deterministic unsigned character value.
 */
extern unsigned char __VERIFIER_nondet_uchar(void);

/**
 * Returns a character pointer value non-deterministically.
 * 
 * \return  Non-deterministic character pointer value.
 * 
 * \note The function returns an arbitrary pointer value. This pointer can point to any memory area and not just to
 *       free areas. Thus, the function does not return a fresh pointer value.
 */
extern char* __VERIFIER_nondet_pchar(void);

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 */
extern short __VERIFIER_nondet_short(void);

/**
 * Returns an unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
extern unsigned short __VERIFIER_nondet_ushort(void);

/**
 * Returns a unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
extern unsigned __VERIFIER_nondet_unsigned(void);

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 */
extern int __VERIFIER_nondet_int(void);

/**
 * Returns a unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
extern unsigned int __VERIFIER_nondet_uint(void);

/**
 * Returns an unsigned integer value for sizes non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value for sizes.
 */
extern size_t __VERIFIER_nondet_size_t(void);

#if defined(_GNU_SOURCE)
/**
 * Returns a signed integer value for file sizes and offsets non-deterministically.
 * 
 * \return Non-deterministic signed integer value for file sizes and offsets.
 */
extern loff_t __VERIFIER_nondet_loff_t(void);
#endif

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 */
extern long __VERIFIER_nondet_long(void);

/**
 * Returns a unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
extern unsigned long __VERIFIER_nondet_ulong(void);

#if defined(__STDC_VERSION__) && 199901L <= __STDC_VERSION__
/**
 *  Returns a signed integer value non-deterministically.
 *
 *  \return Non-deterministic signed integer value.
 *
 *  \note The function is available for the type long long, which has been defined since C99.
 */
extern long long __VERIFIER_nondet_longlong(void);

/**
 * Returns an unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 * 
 * \note The function is available for the type unsigned long long, which has been defined since C99.
 */
extern unsigned long long __VERIFIER_nondet_ulonglong(void);
#endif 

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 * 
 * \note The type __int128 scalar type for targets which have an integer mode wide enough to hold 128 bits.
 *       This type is an GNU extension and only supported by GNU compilers.
 */
extern __int128 __VERIFIER_nondet_int128(void);

/**
 * Returns an unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 * 
 * \note The type unsigned __int128 scalar type for targets which have an integer mode wide enough to hold 128 bits.
 *       This type is an GNU extension and only supported by GNU compilers.
 */
extern unsigned __int128 __VERIFIER_nondet_uint128(void);
#endif

/**
 * Returns a signed floating point value non-deterministically.
 * 
 * \return Non-deterministic signed floating point value.
 */
extern float __VERIFIER_nondet_float(void);

/**
 * Returns a signed double-precision floating point value non-deterministically.
 * 
 * \return Non-deterministic signed double-precision floating point value.
 */
extern double __VERIFIER_nondet_double(void);

/**
 * Returns a pointer value non-deterministically.
 * 
 * \return  Non-deterministic pointer value.
 * 
 * \note The function returns an arbitrary pointer value. This pointer can point to any memory area and not just to
 *       free areas. Thus, the function does not return a fresh pointer value.
 */
extern void* __VERIFIER_nondet_pointer(void);

#ifdef __cplusplus
}
#endif

#endif  /* __ULTIMATE_H */
