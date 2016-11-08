//#Safe
/*
 * Regression test to check that we handle constants correctly
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-09-13
 *
 */

const ninetyone : int;

procedure McCarthy(x: int) returns (res: int);

implementation McCarthy(x: int) returns (res: int)
{
  if (x>100) {
    res := x-10;
  }
  else {
    call res :=  McCarthy(x + 11);
    call res := McCarthy(res);
  }
}


procedure Main(a: int) returns (b: int);
ensures b == ninetyone || a > 101;
//assert(a<=101 ==> b != 90);

implementation Main(a: int) returns (b: int)
{
  assume ninetyone == 91;
  call b := McCarthy(a);
}
