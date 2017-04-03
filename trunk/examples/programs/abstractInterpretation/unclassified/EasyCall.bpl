//#Safe
/*
 * 
 *
 */


procedure main()
{
  var x, y : int;
	
  y := 10;
  x := 10;
  
  call x := add(x, y);
  
  assert(x == 20);
}

procedure add(a, b : int) returns (res : int)
{ 
  res := a + b; 
}