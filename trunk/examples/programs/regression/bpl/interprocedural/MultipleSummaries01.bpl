//#Safe
/* 
 * Program that might reveal bugs in computation of Hoare annotation.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-08-14
 * 
 */


procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
  var x, y: int;
  assume x > 0;
  y := 23;
  call x, y :=  proc(x, y);
  assert x > 0;
    while (*) {
    // prevent large block encoding
  }
  assert y == 42;
}

procedure proc(a, b: int) returns (A, B: int);

implementation proc(a, b: int) returns (A, B: int)
{
  A := a + 1;
  while (*) {
    // prevent large block encoding
  }
  B := b + 19;
}
 
