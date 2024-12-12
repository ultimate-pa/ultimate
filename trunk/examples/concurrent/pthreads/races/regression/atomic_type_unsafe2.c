//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-30
 */

typedef unsigned long pthread_t;

_Atomic int x;
int y;

void* thread1() {
  x = (y += 3); // Race: y is not atomic and its increment is not executed atomically either
}

void* thread2() {
  __atomic_store_n(&y, 5, 5); // Race
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
