//#Safe
int main() {
   struct stu2 {
      int i1;
      int *p;
   } s1 = { 3 , 0 };

  struct stu1 {
    struct stu2 s;
    int i;
  } s2 = { s1,  1 };


  //@ assert s2.s.i1 == 3;
  //@ assert s2.s.p == 0;
  //@ assert s2.i == 1;
}
