
int main() {
  int *p = malloc(4);
  int *q = malloc(4);
  int *r = malloc(4);

  *p = 0;
  *q = 0;
  *r = 0;

  int x = *p;
  int y = *q;
  int z = *r;

  free(p);
  free(q);
  free(r);
}
