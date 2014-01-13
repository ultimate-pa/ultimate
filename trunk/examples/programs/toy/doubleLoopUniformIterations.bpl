/* //#Safe
 Author: musab@informatik.uni-freiburg.de
 Program where trace abstraction with forwards predicates resp. backwards predicates
 can't prove its correctness.
 The problem is, that we need a predicate {x = y} but neither forwards predicates nor
 backwards predicates do get such a predicate.
*/

procedure Main() returns ();

implementation Main() returns () {
    var x, y : int;
    x := 0;
    y := 0;
    while (*) {
       x := x + 1;
       y := y + 1;
    }
    while (x != 0) {
       x := x - 1;
       y := y - 1;
    }
    assert(x == 0);
    assert(y == 0);
}



