//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-24
 */

typedef unsigned long pthread_t;

_Atomic int* x;

void* thread1() {
  (*(x++))++; // Race: The pointer x itself is not atomic and its increment is not executed atomically either
}

void* thread2() {
  _Atomic int* y = __atomic_load_n(&x, 5); // Race
}

int main() {
  pthread_t t1, t2;
  x = malloc(sizeof(_Atomic int));
  *x = 7;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
