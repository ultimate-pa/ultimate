//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: November 2013

int g;

int (((increase)))(int a);


int main() {
    int ((x)) = g;
    g = increase(x);
    //@ assert x == g-1;
}


int increase(int a) {
    int (b) = a;
    b++;
    return b;
}