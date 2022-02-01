//#Safe
/*
 * Reveals bug that can be reproduced using the old computation of nested
 * interpolants in r9719
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 28.9.2013
 */

var decreases: int;
var increases: int;

procedure Main(a: int);
modifies decreases, increases;

implementation Main(a: int)
{
  decreases := 0;
  increases := 0;
  while (*) {
    call increaseByTwo();
  }
  
  assert ( increases == decreases );
}

procedure decreaseByOne() returns ();
modifies decreases;

implementation decreaseByOne() returns ()
{
  decreases := decreases + 1;
}

procedure increaseByTwo() returns ();
modifies decreases, increases;

implementation increaseByTwo() returns ()
{
  increases := increases + 1;
  call decreaseByOne();
}


  
