//#Syntax
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013
// Bug: missing semicolon is not unsupportedSyntax but incorrectSyntax

int main() {
    int x = 1;
    int y = 1;
    do {
        int a; while (a) { int b; a = b; }
        //@ assert x >= 1 && y >= 1;
    }
    while( (x++ != 0) && (y++ != 0) )

}
