//#Safe
int main() {
  int a[3] = { 1, 2, 3};
  if (a[0] != 1) {
    //@ assert \false;
  }
  if (a[1] != 2) {
    //@ assert \false;
  }
  if (a[2] != 3) {
    //@ assert \false;
  }
//  //@ assert a[0] == 1;
//  //@ assert a[1] == 2;
//  //@ assert a[2] == 3;
}
