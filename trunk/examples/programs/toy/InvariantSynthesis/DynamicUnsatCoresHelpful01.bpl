//#Safe
/* * 
 * Date: 2017-01-15 
 * An example that shows how the dynamic increase of pattern conjuncts/disjuncts at some specific locations can help to
 * verify it.
 */
 var x, y, a, b, c, d: int;
  
procedure main()
modifies a, b, c, d, x,y;
{
  x := 0;
  y := 42;
  while (*) {
    x := x + 1;
    y := y - 1;
  }
  a := 1;
  // b := a;
  c := 0;
  while (*) {
	  if (c == 0) {
		  c := 1;
		  a := 0;
		  // b := a;
	  } else {
		  a := 1;
		  // b := a;
		  c := 0;
	  }
  }
  assert (x + y <= 42 && ((a == 1 ) || c == 1));
} 
