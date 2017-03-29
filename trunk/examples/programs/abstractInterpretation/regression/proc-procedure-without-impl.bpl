//#Safe 

procedure foo() returns ()
{
    var x, y : int;
	x := 0;
	y := x;
	
	while (x < 10){
		call x := inc_without_impl(x);
	}
	
	assert x == y + 10;
    
}

procedure inc_without_impl(value : int) returns ( res : int);
requires value >= 0;
ensures res == value + 1;
