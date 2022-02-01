//#Safe
/*
 *
 *
 */


procedure main()
{
  var x, y : int;
	
  y := 30;
  x := 10;
  
  call x := add(x);
  
  assert(x == 20);
}

procedure add(a : int) returns (res : int)
{ 
  res := a + a; 
}