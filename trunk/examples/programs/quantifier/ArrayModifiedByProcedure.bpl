//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 14.09.2013

var a : [int] int;

implementation main() returns ()
{
  call write(0,23);
  assert a[0] == 23;
}

procedure main() returns ();
  modifies a;
  
procedure write(index:int, data:int) returns();
  modifies a;
  ensures old(a)[index := data] == a;

