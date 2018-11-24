//#Safe
/*
 * Note that this test only compiles with warnings, since an initializer has too many elements.
 * The specified (through assertions) behaviour matches gcc.
 */
int main() {
  int a[2][3][2] = { 1, 2, 3, { 4, 5 }};

//  for (int i0 = 0; i0 < 2; i0++) {
//    for (int i1 = 0; i1 < 3; i1++) {
//      for (int i2 = 0; i2 < 2; i2++) {
//        printf("a[%i][%i][%i]: %i\n", i0, i1, i2, a[i0][i1][i2]);
//      }
//    }
//  }

  if (a[0][0][0] != 1) {
    //@assert \false;
  }
  if (a[0][0][1] != 2) {
    //@assert \false;
  }
  if (a[0][1][0] != 3) {
    //@assert \false;
  }
  if (a[0][1][1] != 4) {
    //@assert \false;
  }
  if (a[0][2][0] != 0) {
    //@assert \false;
  }
  if (a[0][2][1] != 0) {
    //@assert \false;
  }
  if (a[1][0][0] != 0) {
    //@assert \false;
  }
  if (a[1][0][1] != 0) {
    //@assert \false;
  }
  if (a[1][1][0] != 0) {
    //@assert \false;
  }
  if (a[1][1][1] != 0) {
    //@assert \false;
  }
  if (a[1][2][0] != 0) {
    //@assert \false;
  }
  if (a[1][2][1] != 0) {
    //@assert \false;
  }



//  //@ assert a[0][0][0] == 1;
//  //@ assert a[0][0][1] == 2;
//  //@ assert a[0][1][0] == 3;
//  //@ assert a[0][1][1] == 4;
//  //@ assert a[0][2][0] == 0;
//  //@ assert a[0][2][1] == 0;
//  //@ assert a[1][0][0] == 0;
//  //@ assert a[1][0][1] == 0;
//  //@ assert a[1][1][0] == 0;
//  //@ assert a[1][1][1] == 0;
//  //@ assert a[1][2][0] == 0;
//  //@ assert a[1][2][1] == 0;

//  for (int i0 = 0; i0 < 2; i0++) {
//    for (int i1 = 0; i1 < 3; i1++) {
//      for (int i2 = 0; i2 < 2; i2++) {
//	if (i0 == 0 && i1 == 0 && i2 == 0) {
//	  continue;
//	}
//        if (i0 == 0 && i1 == 0 && i2 == 1) {
//	  continue;
//	}
//        //@ assert a[i0][i1][i2] == 0;
//      }
//    }
//  }
}
