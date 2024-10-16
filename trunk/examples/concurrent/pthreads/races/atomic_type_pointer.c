//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-18
 *
 * This is an example where the pointer itself is atomic, not the underlying type
 * (see https://stackoverflow.com/questions/42082219/declaring-atomic-pointers-vs-pointers-to-atomics)
 *
 * We currently are not able to deal with atomic pointers,
 * we cannot even parse the atomic keyword properly at this location.
 */

typedef unsigned long pthread_t;

int * _Atomic x;
int * _Atomic y;

void* thread1() {
  x = y; // No race: the pointer itself is atomic, not the underlying type
}

void* thread2() {
  y = x; // No race: the pointer itself is atomic, not the underlying type
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
