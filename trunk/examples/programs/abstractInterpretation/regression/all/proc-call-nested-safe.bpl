//#Safe
/*
 * Calling two functions in an alternating fashion
 *
 */

procedure ULTIMATE.start()
{
  var x : int;
  call x := foo();
  assert(x <= 1);
}

procedure foo() returns (resFoo : int)
{ 
	if(*)
	{
		call resFoo := funA();
	}
	else
	{
		call resFoo := funB();	
	}
}

procedure funA() returns (resA : int)
{ 
	resA := 0;
}


procedure funB() returns (resB : int)
{ 
	resB := 1;
}

