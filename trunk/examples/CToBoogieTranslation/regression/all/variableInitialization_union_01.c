//#Safe

int main() {
  union un {
    int i;
    int *p;
  } u = { 1 };

  //@ assert u.i == 1;
}
