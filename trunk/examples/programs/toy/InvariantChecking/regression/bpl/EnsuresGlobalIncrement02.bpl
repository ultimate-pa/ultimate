//#InvalidAnnotation
/* 
 * Author: Matthias Heizmann
 * Date: 2024-08-21
 */

var g : int;

procedure caller() returns ()
modifies g;
requires true;
ensures true;
{
	var x : int;
	g := x;
	call callee();
	assert g >= x;
}

procedure callee() returns ()
modifies g;
requires true;
ensures g >= old(g);
{
	while (*) {
		g := g + 1;
    }
}
