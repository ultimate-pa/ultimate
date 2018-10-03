int nondet() {
  int i;
  return i;
}

int main() {

  int *p1 = malloc(sizeof(int));
  int *p2 = malloc(sizeof(int));

  *p1 = 0;
  *p2 = 0;

  while (nondet()) {
    if (nondet()) {
      (*p1)++;
    } else {
      (*p2)--;
    }
  }

  int v1 = *p1;
  //@ assert v1 >= 0;
  int v2 = *p2;
  //@ assert v2 <= 0;
}

