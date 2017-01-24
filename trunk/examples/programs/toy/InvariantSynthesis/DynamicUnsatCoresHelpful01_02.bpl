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
  a := 1;
  // b := a;
  d := 0;
  while (*) {
	  if (d == 0) {
		  // a := d;
		  a := 0;
		  d := 1;
	  } else {
		  // a := d;
		  a := 1;
		  d := 0;
	  }
  }
  assert ((a == 1) || d == 1);
} 
