//#Unsafe
/*
 * 
 *
 */

var x, y: int;

procedure main()
modifies x,y;
{  	
  y := 10;
  x := 0;
   
  call x := add(x, y);
  call x := add(x, y);
  
  assert(x == 20);
}

procedure add(a, b : int) returns (res : int)
modifies y;
{ 
  y := y + 1; 
  res := a + b; 
}