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
  y = 6;
  _Bool weak = 1;
  _Bool success = __atomic_compare_exchange(&x, &y, &z, weak, memorder_SEQCST, memorder_SEQCST);
  if (success) {
    x = -1; // access would race, but is unreachable as __atomic_compare_exchange will fail (x stores 21, y stores 6, so they differ)
    return;
  }

  int local;
  __atomic_load(&x, &local, memorder_SEQCST);
  if (local != 21) {
    x = -1; // access would race, but is unreachable as the previous __atomic_compare_exchange failed and x still stores 21 (not 42)
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
  x = 21;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
