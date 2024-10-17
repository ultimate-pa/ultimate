//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-16
 */

typedef unsigned long pthread_t;

_Atomic int x;
_Atomic int* p;

void* thread1() {
  *p = x;
}

void* thread2() {
  x = *p;
}

int main() {
  p = malloc(sizeof(int));
  *p = 0;
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
