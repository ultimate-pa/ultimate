//#Unsafe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 */

typedef unsigned long pthread_t;

int ARRAY[4];

void* thread1() {
  ARRAY[1] = 3; // RACE
  return 0;
}

void* thread2() {
  ARRAY[1] = 4; // RACE
  return 0;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
