//#Unsafe

/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2024-10-22
 */

typedef unsigned long pthread_t;

int x, y, z;

int memorder_SEQCST = 5;

void* thread1(void* ptr) {
  _Bool weak = 1;
  _Bool success = __atomic_compare_exchange_n(&x, &y, 42, weak, memorder_SEQCST, memorder_SEQCST);
  if (! success) {
    x = -1; // RACE, reachable since weak __atomic_compare_exchange_n may spuriously fail
  }
}

void* thread2(void* ptr) {
  int local;
  __atomic_load(&x, &local, memorder_SEQCST);
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
