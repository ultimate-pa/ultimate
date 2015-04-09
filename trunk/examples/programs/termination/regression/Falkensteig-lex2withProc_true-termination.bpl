//#terminating
/*
 * Date: 10.11.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y: int;

procedure main()
modifies x, y;
{
  assume true;
  while (x>0 && y>0) {
    if (*) {
      call x := decrease(x);
    } else {
      x := x + 1;
      call y := decrease(y);
    }
  }
}

procedure decrease(a: int) returns (res: int)
{
  if (*) {
    res := a - 1;
  } else {
    res := a - 7;
  }
    
}