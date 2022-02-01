//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 25.4.2014
// reveals that empty loop body was not supported


int main() {
    int x = 0;
    for (; x != 3; x++ );
    //@ assert x == 3;

}
