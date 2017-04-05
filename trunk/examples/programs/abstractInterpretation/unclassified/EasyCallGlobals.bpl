//#Safe
/*
 * 
 *
 */
var x, y: int;

procedure main()
modifies x,y;
{
  	
  y := 10;
  x := 10;
  
  call x := add(x, y);
  
  assert(x == 50);
}

procedure add(a, b : int) returns (res : int)
modifies x;
{ 
  x := x + 10;
  res := a + b + x + y; 
}