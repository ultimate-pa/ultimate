//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.2.2013

//Bug in r8195.  ACSL Parser unable to handle paranthesis.


int main() {
    //@ assert (1==1 || 1==0) && 0==1;
}