//#Safe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 */

typedef unsigned long pthread_t;

struct MYSTRUCT {
  int field;
};

struct MYSTRUCT x;
struct MYSTRUCT y;

void* thread1() {
  x.field = 3;
  return 0;
}

void* thread2() {
  y.field = 4;
  return 0;
}

int main() {
  pthread_t t1, t2;

  y = x; // copies the struct

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
