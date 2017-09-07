//#Safe
//
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2017-07-31
implementation nonMain() returns ()
{
    var i : int;
    var k : int;

	a[i] := 23;
	a[k] := 42;
    assume 42 == a[i];
    assert k == i;
}

var a : [int]int;

procedure nonMain() returns ();
    modifies a;
