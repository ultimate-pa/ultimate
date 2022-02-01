//#Safe
// Problem: 
// * Equality of x and 0 is detected via solver.
// * We replace a[0] by 42 because we have equality in formula.
// * We replace a[x] by z because we have equality in formula.
// We should replace a[0] and a[x] by common formulas because of equivalence.
//
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2017-08-27
implementation main() returns (#res : int){
    var x : int;
    var a : [int]int;
    var z : int;

    assume a[0] == 42;
    assume 0 <= x && x < 1;
    z := a[x];
    assert z == 42;
}

procedure main() returns (#res : int);
modifies ;
