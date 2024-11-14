// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2024 M. Ebbinghaus <ebbima@informatik.uni-freiburg.de>
// SPDX-FileCopyrightText: 2024 F. Schuessele <schuessf@informatik.uni-freiburg.de>
// SPDX-FileCopyrightText: 2024 D. Klumpp <klumpp@informatik.uni-freiburg.de>
//
// SPDX-License-Identifier: LicenseRef-BSD-3-Clause-Attribution-Vandikas

typedef unsigned long int pthread_t;

union pthread_attr_t
{
  char __size[36];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;

extern void __assert_fail(const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "parallel-parallel-sum-1.wvr.c", 21, __extension__ __PRETTY_FUNCTION__); }
extern int pthread_create (pthread_t *__restrict __newthread,
      const pthread_attr_t *__restrict __attr,
      void *(*__start_routine) (void *),
      void *__restrict __arg) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 3)));
extern int pthread_join (pthread_t __th, void **__thread_return);

typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int   __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
extern void  __VERIFIER_atomic_begin();
extern void  __VERIFIER_atomic_end();

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int i1, i2, i3, i4, x, y, c1, c2, n;

void* thread1() {
  while ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not( i1 < n );
    i1++;
    x++;
	c1++;
	__VERIFIER_atomic_end();
  }

  return 0;
}

void* thread2() {
  while ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not( i2 < n );
    i2++;
    x--;
	assume_abort_if_not( c1 >= 0 );
    __VERIFIER_atomic_end();
  }

  return 0;
}

void* thread3() {
  while ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not( i3 < n );
    i3++;
    y++;
	c2++;
	__VERIFIER_atomic_end();
  }

  return 0;
}

void* thread4() {
  while ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not( i4 < n );
    i4++;
    y--;
	assume_abort_if_not( c2 >= 0 );
    __VERIFIER_atomic_end();
  }

  return 0;
}

int main() {
  pthread_t t1, t2, t3, t4;

  // initialize global variables
  i1  = __VERIFIER_nondet_int();
  i2  = __VERIFIER_nondet_int();
  i3  = __VERIFIER_nondet_int();
  i4  = __VERIFIER_nondet_int();
  x  = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  c1 = __VERIFIER_nondet_int();
  c2 = __VERIFIER_nondet_int();
  n   = __VERIFIER_nondet_int();
  assume_abort_if_not(n < 2147483647);

  // main method
  assume_abort_if_not( i1 == i2 && i1 == i3 && i1 == i4 && x == i1 && x == y && x == 0 && c1 == 0 && c2 == 0);

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);
  pthread_create(&t4, 0, thread4, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_join(t4, 0);

  assume_abort_if_not( ( i1 == i2 && i1 == i3 && i1 == i4 && i1 == n ) && !( x == 0 && y == 0));
  reach_error();

  return 0;
}