//#Safe
/*
 * Version of the LockingExample with arrays.
 * Date: 24.08.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure lockingEx()
{
  var L, new, auld: int;
  var a: [int]int;

  assume L != new;
  assume new != auld;
  assume auld != L;
  
  a[L] := 0;

  while (true) {
    assert(a[L] != 1);
    a[L] := 1;
    a[auld] := a[new];
    if (*) {
      a[L] :=0;
      a[new] := a[new] + 1;
    }
    if (a[new] == a[auld]) {
      break;
    }
  } 
}

