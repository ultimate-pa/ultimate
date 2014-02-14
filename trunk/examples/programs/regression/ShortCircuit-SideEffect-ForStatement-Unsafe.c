//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013
// apparently useless inner while loop is used to check that no auxilliary
// temporary variable occurs in a derived loop invariant

int main() {
    int x = 1;
    int y = 1;
    for (int i = 0; (x++ != 0) || (y++ != 0); i++ ) {
        int a; while (a) { int b; a = b; }
        //@ assert y >= 2;
    }

}
