// #Safe
// Reveals but in quantifier elimination.
// Occurs while computing WP.
// 
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2017-09-04

implementation main() returns (){
    var a : [int,int]int;
    var ib,io,kb,ko : int;

    assume (ib == kb) && (io == ko);
    assert a[ib,io] == a[kb,ko];
}

procedure main() returns ();
modifies ;
