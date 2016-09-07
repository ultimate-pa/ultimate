//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 9.3.2012
 */

var g: real;

procedure Main(z: real);
free requires z>=0.0;
ensures g==z;
modifies g;

implementation Main(z: real)
{
  g:= z;
  call UpAndDownGlobal();
  assert g == z;
}

procedure UpAndDownGlobal() returns ();
modifies g;

implementation UpAndDownGlobal() returns ()
{
//  var x: real;

  g:=g+1.0;
  if (*) {
    call UpAndDownGlobal();
  }
  g:=g-1.0;
}
  
