//#Safe
/*
 * Some sequentialization of MirabelleConcurrentIncrement.bpl
 * Currently, we find invariants with Camel and Penguin
 * refinement strategies.
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2019-08-12
 * 
 */

var x, y, n : int;

procedure ULTIMATE.start()
  modifies x,y;
{

  assume x == y;

  while(x < n || y < n) {
	  if (*) {
		  if (x < n) {
			x := x + 1;
		  }
	  } else {
		  if (y < n) {
			y := y + 1;
		  }
	  }
  }

  assert x == y;

}

