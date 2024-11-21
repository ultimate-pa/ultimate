//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-07-19
 */

typedef unsigned long pthread_t;

int x;
int c = 4;

void* thread1() {
  __atomic_store_n(&x, 1, ++c); // Data-Race: ++c is not executed atomically
}

void* thread2() {
  int local = __atomic_load_n(&c, 5);
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
