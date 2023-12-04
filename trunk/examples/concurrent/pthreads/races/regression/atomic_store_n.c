//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-12-04
 */

typedef unsigned long pthread_t;

int x, y;

void* thread1() {
  __atomic_store_n(&x, 1, 5);
}

void* thread2() {
  int local = __atomic_load_n(&x, 5);
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
