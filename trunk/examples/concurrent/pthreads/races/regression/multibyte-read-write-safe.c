//#Safe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 17. 11. 2022
 */

typedef unsigned long pthread_t;

typedef struct mystruct {
  int a;
  int b;
  int c;
  long long d;
  long long e;
  long long f;
  short g;
  short h;
  short i;
} MY_STRUCT;
MY_STRUCT x;

void* thread(MY_STRUCT *ptr) {
  ptr->g = 3;
  return 0;
}

int main() {
  pthread_t t;
  pthread_create(&t, 0, thread, &x);

  x.h = -4;
}
