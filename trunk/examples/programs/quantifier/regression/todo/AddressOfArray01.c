//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2014-06-04

void procWithArray();

void procWithArray() {
    _Bool a[5];
    a[2] = 0;
    _Bool *p;
    p = &(a[2]);
    if (*p != 0) {
        //@ assert \false;
    }
}