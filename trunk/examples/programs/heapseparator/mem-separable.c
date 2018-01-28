//#Safe
int main() {
  int *p = malloc(4);
  int *q = malloc(4);

  *p = 0;
  *q = 1;

  int x = *p;
  int y = *q;

  //@ assert p != q;

  free(p);
  free(q);
}
