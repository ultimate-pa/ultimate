//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-18
 */

typedef unsigned long pthread_t;

_Atomic int x[10];

void* thread1() {
  int local = x[7];
}

void* thread2() {
  x[7] = 42;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
