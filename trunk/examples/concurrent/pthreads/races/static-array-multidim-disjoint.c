//#Safe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 */

typedef unsigned long pthread_t;

int ARRAY[4][3];
int ROW[3];

void* thread1() {
  ARRAY[2][2] = 3;
  return 0;
}

void* thread2() {
  ROW[2] = 4;
  return 0;
}

int main() {
  pthread_t t1, t2;

  ARRAY[1] = ROW;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
