//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 7.5.2011
 *
 * Version of UpAndDownLocal with two procedures.
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
    call res := UpAndDownLocalTwo(res);
  }
  res:=res-1;
}
  
  
procedure UpAndDownLocalTwo(xTwo: int) returns (resTwo: int);

implementation UpAndDownLocalTwo(xTwo: int) returns (resTwo: int)
{
  resTwo:=xTwo+2;
  if (*) {
    call resTwo := UpAndDownLocal(resTwo);
  }
  resTwo:=resTwo-2;
}