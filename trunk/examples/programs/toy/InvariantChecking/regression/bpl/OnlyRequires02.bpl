//#InvalidAnnotation
/* 
 * 
 * Author: Matthias Heizmann
 * Date: 2024-08-21
 */


procedure caller() returns ()
requires true;
ensures true;
{
	var x : int;
	x := 5;
	call callee(5);
}

procedure callee(a : int) returns ()
requires true;
ensures true;
{
	var i : int;
	i := 0;
    while (*)
	invariant i >= 0 && a >= 1;
	{
		i := a;
		assert i > 0;
    }
}
