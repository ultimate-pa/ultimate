//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2021-10-18
 * 
 * Reveals bug in prenex normal form.
 * If two quantified variables have the same name one of them is ignored.
 */



var x, y, xx, yy : int;
var a : [int]int;

procedure main() returns ();
modifies y, x;

implementation main() returns (){
    assume (exists k:int :: 2*k==x && a[k]==xx) && (exists k:int :: 2*k==y && a[k]==yy);
    while(*){}
    assert (x+y) % 2 == 0;
}

