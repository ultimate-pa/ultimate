//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-12-04
 */

typedef unsigned long pthread_t;

int x;

void* thread1() {
  int local = 1;
  __atomic_store(&x, &local, 5);
}

void* thread2() {
  int local = x; // Non-atomic access -> RACE
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
