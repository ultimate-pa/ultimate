//#Terminating
// Bug with oldVars in supporting invariants. Switch of termination argument
// simplification to reproduce.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-06-14

implementation main() returns (){
    ~y := ~y;
    while (~x > 0)
    {
        ~x := ~x - ~y;
    }
}

var ~x : int;

var ~y : int;

implementation ULTIMATE.init() returns (){
    ~x := 300;
    ~y := 2;
}

implementation ULTIMATE.start() returns (){

    call ULTIMATE.init();
    call main();
}

procedure main() returns ();
modifies ~y, ~x;

procedure ULTIMATE.init() returns ();
modifies ~x, ~y;

procedure ULTIMATE.start() returns ();
modifies ~x, ~y;

