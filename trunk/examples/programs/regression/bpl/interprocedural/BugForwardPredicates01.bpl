//#Safe
// Bug with oldVars that was revealed in the termination analysis.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-06-14

implementation main() returns (){
    assert (5 >= old(x)) && (7 >= x);
}

var x : int;

implementation ULTIMATE.start() returns (){

    x := 0;
    call main();
}

procedure main() returns ();
modifies x;

procedure ULTIMATE.start() returns ();
modifies x;

