//#Unsafe
// Reveals bug in r9602 global vars in requires of procedure are
// interpreted as the variable after executing the procedure (instead of
// before executing the procedure. According to this wrong implementation
// the specification of the increment2 procedure is already inconsistent.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 14.09.2013

var g : int;

implementation main() returns ()
{
  g :=  2;
  call increment2();
  assert g == 0;
}

procedure main() returns ();
  modifies g;
  
procedure increment2() returns();
  modifies g;
  requires g == 2;
  ensures g == old(g) + 1;
  ensures g == 3;

