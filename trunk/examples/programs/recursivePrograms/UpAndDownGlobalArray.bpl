//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: April 2012
 */

var g: [int]int;
var i: int;

procedure Main(z: int);
free requires z>=0;
ensures g[i]==z;
modifies g;

implementation Main(z: int)
{
  g[i]:= z;
  call UpAndDownGlobal();
  assert g[i] == z;
}

procedure UpAndDownGlobal() returns ();
modifies g;

implementation UpAndDownGlobal() returns ()
{
//  var x: int;

  g[i]:=g[i]+1;
  if (*) {
    call UpAndDownGlobal();
  }
  g[i]:=g[i]-1;
}
  
