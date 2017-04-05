//#Safe
/*
 * In the else branch the variables are declared in a different order
 *
 */

procedure main()
{
  var x, y: int;
  
  x := 5;
  call y := f(x);
  
  assert(y <= x);
}

procedure f(a : int) returns (res : int)
{
  var x, y : int;
  if(*)
  {	
	x := 0;
	call res := f(a - 1);
    y := 0;	
  }
  else
  {
    y := 0;	
	x := 0;
	res := a;
  }
}