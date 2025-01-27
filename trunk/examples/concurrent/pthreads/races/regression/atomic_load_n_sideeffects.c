//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-07-19
 */

typedef unsigned long pthread_t;

int c;
int x[2] = {0, 1};

void* thread1() {
  __atomic_load_n(x + c++, 5);
}

void* thread2() {
  int local = c;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
