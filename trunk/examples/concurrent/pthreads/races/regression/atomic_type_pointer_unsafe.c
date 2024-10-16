//#Unsafe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-18
 */

typedef unsigned long pthread_t;

// This defines an atomic pointer
// See https://stackoverflow.com/questions/42082219/declaring-atomic-pointers-vs-pointers-to-atomics
int * _Atomic x;
int * _Atomic y;

void* thread1() {
  *x = *y; // Race: The dereference is not atomic
}

void* thread2() {
  *y = *x; // Race: The dereference is not atomic
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
