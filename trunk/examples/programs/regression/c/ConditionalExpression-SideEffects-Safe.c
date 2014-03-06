//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.2.2013

int foo(int a, int b, int c) {
    int x = a;
    int y = b;
    int z = c;
    int n = (x++ == 0) ? y++ : z++;
    //@ assert x == a + 1;
    //@ assert a == 0 ==> n == b;
    //@ assert a == 0 ==> y == b + 1;
    //@ assert a != 0 ==> n == c;
    //@ assert a != 0 ==> z == c + 1;
}

int main() {
    int a, b, c;
    int res = foo(a,b,c);
    return 0;
}