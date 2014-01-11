//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 9.3.2012
 *
 */


procedure Main(z: real);
free requires z>=0.0;

implementation Main(z: real)
{
  var y: real;
  y:= z;
  call y := UpAndDownLocal(z);
  assert y == z;
}


procedure UpAndDownLocal(x: real) returns (res: real);

implementation UpAndDownLocal(x: real) returns (res: real)
{
  res:=x+1.0;
  if (*) {
    call res := UpAndDownLocal(res);
  }
  res:=res-1.0;
}
  
