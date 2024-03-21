//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-01-23
 */

typedef unsigned long pthread_t;

int x, y;

void* thread1() {
  __atomic_store(&x, &y, 5); // Non-atomic access on y -> RACE
}

void* thread2() {
  int local = 0;
  __atomic_store(&y, &local, 5);
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
