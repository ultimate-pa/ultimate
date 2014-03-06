//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013
// TODO: extend this example by an example where we also short circuit 
// conditions while accessing an array.
// We can not do this now, because the operators && and || are only implemented
// for _Bool and we do not yet support casts.

int main() {
    int x = 0;
    int a[1];
    a[0] = 42;
    int z = a[x++];
    //@ assert z == 42 && x == 1;
}
