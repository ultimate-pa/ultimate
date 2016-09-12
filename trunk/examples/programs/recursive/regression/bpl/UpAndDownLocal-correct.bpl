//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: August 2010
 *
 * The Program is correct with respect to the ensures statement in the Main
 * procedure.
 */


procedure Main(z: int);
free requires z>=0;

implementation Main(z: int)
{
  var y: int;
  y:= z;
  call y := UpAndDownLocal(z);
  assert y == z;
}


procedure UpAndDownLocal(x: int) returns (res: int);

implementation UpAndDownLocal(x: int) returns (res: int)
{
  res:=x+1;
  if (*) {
    call res := UpAndDownLocal(res);
//    assert (x == 5 ==> res == 10);
  }
  res:=res-1;
}
  
