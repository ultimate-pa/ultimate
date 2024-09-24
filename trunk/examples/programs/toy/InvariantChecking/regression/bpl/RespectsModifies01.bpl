//#ValidAnnotation
/* 
 * Author: Matthias Heizmann
 * Date: 2024-08-21
 */

var g,f : int;

procedure caller() returns ()
modifies g,f;
requires true;
ensures true;
{
	var x,y : int;
	g := x;
	f := y;
	call callee();
	assert g >= x && f == y;
}

procedure callee() returns ()
modifies g;
requires true;
ensures g >= old(g);
{
	while (*)
	invariant g >= old(g);
	{
		g := g + 1;
    }
}
