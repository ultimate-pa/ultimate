//#Safe

int main() {
  union un {
    int i;
    int *p;
  };

  struct stu {
    int x;
    union un u;
  } s = { 1 };

  //@ assert s.x == 1;
  //@ assert s.u.i == 0;
}
