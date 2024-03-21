//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-08-07
 */

typedef unsigned long pthread_t;

int x, y;

void* thread1() {
  int local;
  __atomic_exchange(&x, &y, &local, 5);
}

void* thread2() {
  int local;
  __atomic_load(&x, &local, 5);
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
