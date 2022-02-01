//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2017-01-18

typedef int ganzzahl;
typedef ganzzahl lol;

extern int foo(lol x);



int main() {
    ganzzahl x;
    int y = foo(x);
    return 0;
}


int foo(ganzzahl x) {
    return 0;
}
