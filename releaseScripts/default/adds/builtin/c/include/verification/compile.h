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
 * Verification functions and data types for dynamic program analysis (runtime verification).
 * 
 * \author Manuel Bentele
 * \version 0.3.0
 */

#ifndef __COMPILE_H
#define __COMPILE_H

#ifdef __cplusplus
extern "C" {
#endif

#include <assert.h>
#include <limits.h>
#include <float.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#if defined(_GNU_SOURCE)
# include <sys/types.h>
#endif

#if defined(__RDRND__)

# include <immintrin.h>

/**
 * Initializes the hardware accelerated random number generator.
 * 
 * \note The function is automatically executed before the main function of the program to be verified.
 */
void __attribute__ ((constructor)) setup_rdrand(void) {}

/**
 * Generates a random 1-bit unsigned value using hardware acceleration.
 */
bool rdrand1(void)
{
    unsigned short value = 0;
    do {} while(!_rdrand16_step(&value));
    return value % 2;
}

/**
 * Generates a random 8-bit unsigned value using hardware acceleration.
 */
uint8_t rdrand8(void)
{
    unsigned short value = 0;
    do {} while(!_rdrand16_step(&value));
    return value % 256;
}

/**
 * Generates a random 16-bit unsigned value using hardware acceleration.
 */
uint16_t rdrand16(void)
{
    unsigned short value = 0;
    do {} while(!_rdrand16_step(&value));
    return value;
}

/**
 * Generates a random 32-bit unsigned value using hardware acceleration.
 */
uint32_t rdrand32(void)
{
    unsigned int value = 0;
    do {} while(!_rdrand32_step(&value));
    return value;
}

/**
 * Generates a random 64-bit unsigned value using hardware acceleration.
 */
uint64_t rdrand64(void)
{
    unsigned long long value = 0;
    do {} while(!_rdrand64_step(&value));
    return value;
}

# if defined(__GNUC__) && defined(__SIZEOF_INT128__)
/**
 * Generates a random 128-bit unsigned value using hardware acceleration.
 */
unsigned __int128 rdrand128(void)
{
    return ((unsigned __int128)rdrand64() << 64) | rdrand64();
}
# endif

# define  RANDOM1   rdrand1()
# define  RANDOM8   rdrand8()
# define  RANDOM16  rdrand16()
# define  RANDOM32  rdrand32()
# define  RANDOM64  rdrand64()
# if defined(__GNUC__) && defined(__SIZEOF_INT128__)
#  define RANDOM128 rdrand128()
# endif

#else

# include <stdlib.h>
# include <time.h>

/**
 * Initializes the random number generator.
 * 
 * \note The function is automatically executed before the main function of the program to be verified.
 */
void __attribute__ ((constructor)) setup_rand(void)
{
    time_t t;
    srand((unsigned)time(&t));
}

/**
 * Generates a random 1-bit unsigned value.
 */
bool rand1(void)
{
    return rand() % 2;
}

/**
 * Generates a random 8-bit unsigned value.
 */
uint8_t rand8(void)
{
    return rand() % 256;
}

/**
 * Generates a random 16-bit unsigned value.
 */
uint16_t rand16(void)
{
    return rand() % 65536;
}

/**
 * Generates a random 32-bit unsigned value.
 */
uint32_t rand32(void)
{
    return rand();
}

/**
 * Generates a random 64-bit unsigned value.
 */
uint64_t rand64(void)
{
    return ((uint64_t)rand32() << 32) | rand32();
}

# if defined(__GNUC__) && defined(__SIZEOF_INT128__)
/**
 * Generates a random 128-bit unsigned value.
 */
unsigned __int128 rand128(void)
{
    return ((unsigned __int128)rand64() << 64) | rand64();
}
# endif

# define  RANDOM1   rand1()
# define  RANDOM8   rand8()
# define  RANDOM16  rand16()
# define  RANDOM32  rand32()
# define  RANDOM64  rand64()
# if defined(__GNUC__) && defined(__SIZEOF_INT128__)
#  define RANDOM128 rand128()
# endif
#endif

#define CONCAT(x,y) (x ## y)
#define JOIN(x,y)  CONCAT(x,y)

/**
 * Generates a random unsigned value between zero and the positiv upper bound of a type with specified bit WIDTH.
 */
#define RANDOM_UNSIGNED_VALUE(WIDTH) (JOIN(RANDOM, WIDTH))

/**
 * Generates a random signed value between the lower bound MIN and the positiv upper bound of a type with specified
 * bit WIDTH.
 */
#define RANDOM_SIGNED_VALUE(WIDTH, MIN) (RANDOM_UNSIGNED_VALUE(WIDTH) + MIN)

/**
 * Generates a random floating-point value for TYPE between a negative lower bound MIN and a positive upper bound MAX
 * using a specified RANDOM implementation providing maximum value RDMAX.
 */
#define RANDOM_FLT_VALUE(RANDOM, RDMAX, TYPE, MIN, MAX) (((MAX - MIN) * ((TYPE)RANDOM / RDMAX)) + MIN)

/**
 * Generates a 32-bit random floating-point value between a negative lower bound MIN and a positive upper bound MAX.
 */
#define RANDOM32_FLT_VALUE(MIN, MAX) RANDOM_FLT_VALUE(RANDOM32, INT32_MAX, float, MIN, MAX)

/**
 * Generates a 64-bit random floating-point value between a negative lower bound MIN and a positive upper bound MAX.
 */
#define RANDOM64_DBL_VALUE(MIN, MAX) RANDOM_FLT_VALUE(RANDOM64, INT64_MAX, double, MIN, MAX)

#ifndef PTR_WIDTH
/**
 * Bit width of pointer types.
 */
#define PTR_WIDTH __INTPTR_WIDTH__
#endif

/**
 * Generates a random pointer value.
 */
#define RANDOM_PTR_VALUE(TYPE) ((TYPE)RANDOM_UNSIGNED_VALUE(PTR_WIDTH))

/**
 * Provides assumptions about the program's state or behavior.
 * 
 * When this function is called with a specific assumption, it will be ignored.
 * 
 * \param assumption Expression that is used as assumption for an analysis.
 * 
 * \note The function is not implemented for runtime verification.
 */
void __VERIFIER_assume(int assumption) {}

/**
 * Indicates an error condition.
 * 
 * When this function is called, it will abort the program execution.
 */
void __VERIFIER_error(void)
{
    abort();
}

/**
 * Marks the beginning of a critical section in the program.
 * 
 * This function helps to ensure that certain operations are executed atomically, without interruption or interference
 * from other threads or processes, thereby preventing race conditions and ensuring the correctness of the program's
 * behavior.
 * 
 * \note The function is not implemented for runtime verification.
 */
void __VERIFIER_atomic_begin(void) {}

/**
 * Marks the end of a critical section in the program.
 * 
 * This function helps to ensure that the operations within the critical section are executed atomically, without
 * interruption or interference from other threads or processes, maintaining the integrity of the program's execution
 * and preventing race conditions.
 * 
 * \note The function is not implemented for runtime verification.
 */
void __VERIFIER_atomic_end(void) {}

#ifndef BOOL_WIDTH
/**
 * Bit width of boolean types bool and _Bool.
 */
# define BOOL_WIDTH 1
#endif

/**
 * Returns a boolean value non-deterministically.
 * 
 * \return Random boolean value.
 */
bool __VERIFIER_nondet_bool(void)
{
    return RANDOM_UNSIGNED_VALUE(BOOL_WIDTH);
}

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L && __STDC_VERSION__ <= 201710L
/**
 * Returns a boolean value non-deterministically.
 * 
 * \return Random boolean value.
 * 
 * \note The function is available for the boolean type _Bool, which is only defined from C99 to C20.
 */
_Bool __VERIFIER_nondet__Bool(void)
{
    return RANDOM_UNSIGNED_VALUE(BOOL_WIDTH);
}
#endif

/**
 * Returns a signed character value non-deterministically.
 * 
 * \return Random signed character value.
 */
char __VERIFIER_nondet_char(void)
{
    return RANDOM_SIGNED_VALUE(__SCHAR_WIDTH__, CHAR_MIN);
}

/**
 * Returns an unigned character value non-deterministically.
 * 
 * \return Non-deterministic unsigned character value.
 */
unsigned char __VERIFIER_nondet_uchar(void)
{
    return RANDOM_UNSIGNED_VALUE(__SCHAR_WIDTH__);
}

/**
 * Returns a character pointer value non-deterministically.
 * 
 * \return  Non-deterministic character pointer value.
 * 
 * \note The function returns an arbitrary pointer value. This pointer can point to any memory area and not just to
 *       free areas. Thus, the function does not return a fresh pointer value.
 */
char* __VERIFIER_nondet_pchar(void)
{
    return RANDOM_PTR_VALUE(char*);
}

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 */
short __VERIFIER_nondet_short(void)
{
    return RANDOM_SIGNED_VALUE(__SHRT_WIDTH__, SHRT_MIN);
}

/**
 * Returns an unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
unsigned short __VERIFIER_nondet_ushort(void)
{
    return RANDOM_UNSIGNED_VALUE(__SHRT_WIDTH__);
}

/**
 * Returns a unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
unsigned __VERIFIER_nondet_unsigned(void)
{
    return RANDOM_UNSIGNED_VALUE(__INT_WIDTH__);
}

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 */
int __VERIFIER_nondet_int(void)
{
    return RANDOM_SIGNED_VALUE(__INT_WIDTH__, INT_MIN);
}

/**
 * Returns a unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
unsigned int __VERIFIER_nondet_uint(void)
{
    return RANDOM_UNSIGNED_VALUE(__INT_WIDTH__);
}

/**
 * Returns an unsigned integer value for sizes non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value for sizes.
 */
size_t __VERIFIER_nondet_size_t(void)
{
    return RANDOM_UNSIGNED_VALUE(__SIZE_WIDTH__);
}

#if defined(_GNU_SOURCE)
/**
 * Returns a signed integer value for file sizes and offsets non-deterministically.
 * 
 * \return Non-deterministic signed integer value for file sizes and offsets.
 */
loff_t __VERIFIER_nondet_loff_t(void)
{
    return RANDOM_SIGNED_VALUE(__LONG_WIDTH__, LONG_MIN);
}
#endif

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 */
long __VERIFIER_nondet_long(void)
{
    return RANDOM_SIGNED_VALUE(__LONG_WIDTH__, LONG_MIN);
}

/**
 * Returns a unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 */
unsigned long __VERIFIER_nondet_ulong(void)
{
    return RANDOM_UNSIGNED_VALUE(__LONG_WIDTH__);
}

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
/**
 *  Returns a signed integer value non-deterministically.
 *
 *  \return Non-deterministic signed integer value.
 *
 *  \note The function is available for the type long long, which has been defined since C99.
 */
long long __VERIFIER_nondet_longlong(void)
{
    return RANDOM_SIGNED_VALUE(__LONG_LONG_WIDTH__, LLONG_MIN);
}

/**
 * Returns an unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 * 
 * \note The function is available for the type unsigned long long, which has been defined since C99.
 */
unsigned long long __VERIFIER_nondet_ulonglong(void)
{
    return RANDOM_UNSIGNED_VALUE(__LONG_LONG_WIDTH__);
}
#endif

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
# ifndef INT128_MIN
/**
 * Minimum value of the __int128 scalar type.
 */
#  define INT128_MIN (-INT128_MAX - 1)
# endif
# ifndef INT128_MAX
/**
 * Maximum value of the __int128 scalar type.
 */
#  define INT128_MAX (__int128) (((unsigned __int128) 1 << ((__SIZEOF_INT128__ * __CHAR_BIT__) - 1)) - 1)
# endif

# ifndef INT128_WIDTH
/**
 * Bit width of the __int128 signed scalar type.
 */
#  define INT128_WIDTH 128
# endif

# ifndef UINT128_WIDTH
/**
 * Bit width of the __int128 unsigned scalar type.
 */
#  define UINT128_WIDTH 128
#endif

/**
 * Returns a signed integer value non-deterministically.
 * 
 * \return Non-deterministic signed integer value.
 * 
 * \note The type __int128 is a scalar type for targets which have an integer mode wide enough to hold 128 bits.
 *       This type is an GNU extension and only supported by GNU compilers.
 */
__int128 __VERIFIER_nondet_int128(void)
{
    return RANDOM_SIGNED_VALUE(INT128_WIDTH, INT128_MIN);
}

/**
 * Returns an unsigned integer value non-deterministically.
 * 
 * \return Non-deterministic unsigned integer value.
 * 
 * \note The type unsigned __int128 scalar type for targets which have an integer mode wide enough to hold 128 bits.
 *       This type is an GNU extension and only supported by GNU compilers.
 */
unsigned __int128 __VERIFIER_nondet_uint128(void)
{
    return RANDOM_UNSIGNED_VALUE(UINT128_WIDTH);
}
#endif

/**
 * Returns a signed floating point value non-deterministically.
 * 
 * \return Non-deterministic signed floating point value.
 */
float __VERIFIER_nondet_float(void)
{
    return RANDOM32_FLT_VALUE(FLT_MIN, FLT_MAX);
}

/**
 * Returns a signed double-precision floating point value non-deterministically.
 * 
 * \return Non-deterministic signed double-precision floating point value.
 */
double __VERIFIER_nondet_double(void)
{
    return RANDOM64_DBL_VALUE(DBL_MIN, DBL_MAX);
}

/**
 * Returns a pointer value non-deterministically.
 * 
 * \return  Non-deterministic pointer value.
 * 
 * \note The function returns an arbitrary pointer value. This pointer can point to any memory area and not just to
 *       free areas. Thus, the function does not return a fresh pointer value.
 */
void* __VERIFIER_nondet_pointer(void)
{
    return RANDOM_PTR_VALUE(void*);
}

#ifdef __cplusplus
}
#endif

#endif  /* __COMPILE_H */
