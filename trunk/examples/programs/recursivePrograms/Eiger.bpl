//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 14.5.2011
 *
 * Example with several features:
 * - invariant that needs local and global vars
 * - procedure called in different contexts
 * - global var modified only by some procedures.
 */

var decreases: int;
var increases: int;

procedure Main(a: int);
modifies decreases, increases;

implementation Main(a: int)
{
  var c: int;
  decreases := 0;
  increases := 0;
  c := a;
  while (*) {
    call c := increaseByTwo(c);
    call c := decreaseByOne(c);
  }
  
  assert ( increases + increases == decreases );
  assert ( c == a + increases );
}

procedure decreaseByOne(x: int) returns (res: int);
modifies decreases;

implementation decreaseByOne(x: int) returns (res: int)
{
  decreases := decreases + 1;
  res := x - 1;
}

procedure increaseByTwo(x: int) returns (res: int);
modifies decreases, increases;

implementation increaseByTwo(x: int) returns (res: int)
{
  increases := increases + 1;
  res := x + 3;
  call res := decreaseByOne(res);
}


  
