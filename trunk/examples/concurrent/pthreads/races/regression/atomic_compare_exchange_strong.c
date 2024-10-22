//#Safe

/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2024-10-22
 */

typedef unsigned long pthread_t;

int x, y;

int memorder_SEQCST = 5;

void* thread1(void* ptr) {
  _Bool weak = 0;
  _Bool success = __atomic_compare_exchange_n(&x, &y, 42, weak, memorder_SEQCST, memorder_SEQCST);
  if (! success) {
    x = -1; // access would race, but is unreachable as strong __atomic_compare_exchange_n cannot fail here
    return;
  }

  int local;
  __atomic_load(&x, &local, memorder_SEQCST);
  if (local != 42) {
    x = -1; // access would race, but is unreachable as strong __atomic_compare_exchange_n cannot fail here
    return;
  }

  y = 6;
  weak = 1;
  success = __atomic_compare_exchange_n(&x, &y, 0, weak, memorder_SEQCST, memorder_SEQCST);
  if (success) {
    x = -1; // access would race, but is unreachable as __atomic_compare_exchange_n will fail (x stores 42, y stores 6, so they differ)
    return;
  }

  __atomic_load(&x, &local, memorder_SEQCST);
  if (local != 42) {
    x = -1; // access would race, but is unreachable as the previous __atomic_compare_exchange_n failed and x still stores 42 (not 0)
    return;
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
