//#Safe


var x : int; 
 
procedure ULTIMATE.init()
modifies x;
{
  x := 1;
  call dec();

  assert x >= 0;
}


procedure dec() returns ()
modifies x;
{ 
	x := x -1;
}

