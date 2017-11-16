//#Safe
int main() {
  struct stu {
    int i;
    int *p;
  } s1 = { 1 };


  struct stu s2 = s1;

  //@ assert s2.i == 1;
  //@ assert s2.p == 0;
}
