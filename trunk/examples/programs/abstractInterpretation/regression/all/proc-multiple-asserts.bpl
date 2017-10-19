//#Safe


var x,y,z : int; 
 
procedure ULTIMATE.init()
modifies x,y,z;
{
  x := 2;
  y := 1;
  z := 0;
  
  call dec();
  assert x == y;
  call dec();
  assert x == z;
}


procedure dec() returns ()
modifies x;
{ 
	x := x - 1;
}

