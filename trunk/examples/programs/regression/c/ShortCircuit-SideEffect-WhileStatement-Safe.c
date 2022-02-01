//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013
// apparently useless inner while loop is used to check that no auxilliary
// temporary variable occurs in a derived loop invariant

int main() {
    int x = 1;
    int y = 1;
    while( (x++ == 0) && (y++ == 0) ) {
        int a; while (a) { int b; a = b; }
        //@ assert x >= 2 && y >= 2;
    }

}
