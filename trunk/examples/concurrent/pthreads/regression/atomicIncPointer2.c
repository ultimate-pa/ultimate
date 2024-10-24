//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-10-24
 */

typedef _Atomic int atomic_int;

atomic_int *x;

void* thread(void* arg) {
  *x += 2;
}

int main() {
  x = malloc(sizeof(int));
  *x = 0;
  pthread_t t1, t2, t3;
  pthread_create(&t1, NULL, thread, NULL);
  pthread_create(&t2, NULL, thread, NULL);
  pthread_create(&t3, NULL, thread, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  pthread_join(t3, NULL);
  //@ assert *x == 6;
}
