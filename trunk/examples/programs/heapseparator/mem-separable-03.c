
int main() {
  int *p = malloc(4);
  int *q = malloc(4);
  int *r = malloc(4);
  int *s = malloc(4);
  int *t = malloc(4);

  *p = 0;
  *q = 0;
  *r = 0;
  *s = 0;
  *t = 0;

  int x = *p;
  int y = *q;
  int z = *r;
  int i = *s;
  int j = *t;

  free(p);
  free(q);
  free(r);
  free(s);
  free(t);
}
