//#Safe
int main() {
  int a[2][3] = { { 1 }, 4, 5 };

  if (a[0][0] != 1) {
    //@assert \false;
  }
  if (a[0][1] != 0) {
    //@assert \false;
  }
  if (a[0][2] != 0) {
    //@assert \false;
  }
  if (a[1][0] != 4) {
    //@assert \false;
  }
  if (a[1][1] != 5) {
    //@assert \false;
  }
  if (a[1][2] != 0) {
    //@assert \false;
  }


//  //@ assert a[0][0] == 1;
//  //@ assert a[0][1] == 0;
//  //@ assert a[0][2] == 0;
//  //@ assert a[1][0] == 4;
//  //@ assert a[1][1] == 5;
//  //@ assert a[1][2] == 0;
}
