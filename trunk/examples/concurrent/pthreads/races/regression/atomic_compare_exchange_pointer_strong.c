//#Safe

/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2024-10-22
 */

typedef unsigned long pthread_t;

int x, y;
int z = 42;

int memorder_SEQCST = 5;

void* thread1(void* ptr) {
  _Bool weak = 0;
  _Bool success = __atomic_compare_exchange(&x, &y, &z, weak, memorder_SEQCST, memorder_SEQCST);
  if (! success) {
    x = -1; // access would race, but is unreachable as strong __atomic_compare_exchange cannot fail here
    return;
  }

  int local;
  __atomic_load(&x, &local, memorder_SEQCST);
  if (local != 42) {
    x = -1; // access would race, but is unreachable as strong __atomic_compare_exchange cannot fail here
    return;
  }
}

void* thread2(void* ptr) {
  int local;
  __atomic_load(&x, &local, memorder_SEQCST);
  __atomic_load(&z, &local, memorder_SEQCST);
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
