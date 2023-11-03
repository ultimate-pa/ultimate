//#Unsafe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 *
 * As of 2022-03-25, this fails because our memcpy implementation does not support data race detection.
 */

typedef unsigned long pthread_t;

int ARRAY1[4];
int ARRAY2[4];

void* thread1() {
  ARRAY1[0] = 3; // RACE
  return 0;
}

void* thread2() {
  memcpy(ARRAY1, ARRAY2, 4*sizeof(int)); // RACE
  return 0;
}

int main() {
  pthread_t t1, t2;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
