//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-16
 */

_Atomic int x;

void* thread(void* arg) {
  ++x;
}

int main() {
  pthread_t t1, t2, t3;
  pthread_create(&t1, NULL, thread, NULL);
  pthread_create(&t2, NULL, thread, NULL);
  pthread_create(&t3, NULL, thread, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  pthread_join(t3, NULL);
  //@ assert x == 3;
}
