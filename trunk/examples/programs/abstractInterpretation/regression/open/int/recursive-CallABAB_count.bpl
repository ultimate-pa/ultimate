//#Safe
/*
 * Calling two functions in an alternating fashion
 *
 */
var g : int;

procedure Main()
modifies g;
{
  var x : int;
  g := 0;
  call x := dispatch(20, 20);
  
  assert(g <= 14);
}


procedure dispatch(a, b : int) returns (res : int)
modifies g;
{ 
	if( a + b <= 0 )
	{
		res := a + b;
		return;
	}
	
	g := g + 1;
	if( a > b )
	{
		call res := funA(a, b);
	}
	else
	{
		call res := funB(a, b);	
	}
}

procedure funA(a, b : int) returns (res : int)
modifies g;
{ 
	call res := dispatch( a - 2, b - 1 );
}


procedure funB(a, b : int) returns (res : int)
modifies g;
{ 
	call res := dispatch( a - 1, b - 2 );
}

