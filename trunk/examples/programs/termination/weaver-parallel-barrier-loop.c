//#Nonterminating

/*
 * Extracted from svcomp/weaver/parallel-barrier-loop.wvr.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-08-01
 *
 */

typedef unsigned long int pthread_t;

union pthread_attr_t
{
  char __size[36];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;

extern int pthread_create (pthread_t *__restrict __newthread,
      const pthread_attr_t *__restrict __attr,
      void *(*__start_routine) (void *),
      void *__restrict __arg) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 3)));
extern int pthread_join (pthread_t __th, void **__thread_return);

extern _Bool __VERIFIER_nondet_bool(void);
extern void  __VERIFIER_atomic_begin();
extern void  __VERIFIER_atomic_end();

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

_Bool f1_2, f2_3;


void* thread1() {
  while ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    f1_2 = 1;
    __VERIFIER_atomic_end();
    __VERIFIER_atomic_begin();
    assume_abort_if_not(f2_3);
    __VERIFIER_atomic_end();

    __VERIFIER_atomic_begin();
    f1_2 = 0;
    __VERIFIER_atomic_end();
    __VERIFIER_atomic_begin();
    assume_abort_if_not(!f2_3);
    __VERIFIER_atomic_end();
  }

  return 0;
}

void* thread2() {
  while ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    f2_3 = 1;
    __VERIFIER_atomic_end();
    __VERIFIER_atomic_begin();
    assume_abort_if_not(f1_2);
    __VERIFIER_atomic_end();

    __VERIFIER_atomic_begin();
    f2_3 = 0;
    __VERIFIER_atomic_end();
    __VERIFIER_atomic_begin();
    assume_abort_if_not(!f1_2);
    __VERIFIER_atomic_end();
  }

  return 0;
}

int main() {
  pthread_t t1, t2;

  __VERIFIER_atomic_begin();
  f1_2 = 0;
  f2_3 = 0;
  __VERIFIER_atomic_end();

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);

  return 0;
}