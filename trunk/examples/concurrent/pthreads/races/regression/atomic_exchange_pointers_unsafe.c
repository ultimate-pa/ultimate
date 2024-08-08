//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-01-09
 */

typedef unsigned long pthread_t;

int *x, *y;

void* thread1() {
  int local;
  __atomic_exchange(x, y, &local, 5);
}

void* thread2() {
  int local = *x; // Non-atomic access -> RACE
}

int main() {
  pthread_t t1, t2;
  x = malloc(sizeof(int));
  y = malloc(sizeof(int));
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
