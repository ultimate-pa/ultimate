//#Safe
/*
 * Bug: p != q missing after second malloc
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
implementation main() returns ()
{
    var p : int;
    var q : int;

    call p := ~malloc();
    call q := ~malloc();
    call ~free(p);
    call ~free(q);
    return;
}



var valid : [int]bool;

procedure ~free(pointer:int) returns ();
    requires valid[pointer];
    free ensures old(valid)[pointer := false] == valid;
    modifies valid;

procedure ~malloc() returns (addr:int);
    free ensures false == old(valid)[addr];
    free ensures old(valid)[addr := true] == valid;
    modifies valid;


procedure main() returns ();
    modifies valid;



procedure ULTIMATE.start() returns ();
    modifies valid;

implementation ULTIMATE.start() returns ()
{
    call main();
    return;
}

// true
//call main
// true
//fst summary
//   valid[p] = true
//snd summary
//   valid[p] == true && valid[q] == true
//third summary
//   p == q && valid[p] == false && valid[q] == false||  p != q && valid[p] == false && valid[q] == true

