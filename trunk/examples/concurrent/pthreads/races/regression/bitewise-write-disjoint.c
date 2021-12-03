//#Safe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 */

typedef unsigned long pthread_t;

int* ptr;

void* thread() {
  char* ch = (char*)ptr;
  ch[1] = (char)1;

  return 0;
}

int main() {
  pthread_t t;
  int x = 0;

  ptr = &x;
  pthread_create(&t, 0, thread, 0);

  char* ch = (char*)ptr;
  ch[3] = (char)2;
}
