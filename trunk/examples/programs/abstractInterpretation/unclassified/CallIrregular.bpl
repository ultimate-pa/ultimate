//#Safe
/*
 * Calling two functions in an alternating fashion
 *
 */


procedure main()
{
  var x : int;
  call x := A( 1, 0, 1000 ); 
  assert(x == 1000);
}


procedure A( a, b, goal : int) returns ( res : int )
{ 	
	if(a >= goal)
	{
		res := a + b;
		return;
	}
		
	call res := B( a, 1, goal );	
}

procedure B( a, b, goal : int ) returns ( res : int )
{ 
	if( b < a )
	{
		call res := B( a , b + 1, goal );
	}
	else
	{
		call res := A( a + 1 , b, goal );
	}
}

