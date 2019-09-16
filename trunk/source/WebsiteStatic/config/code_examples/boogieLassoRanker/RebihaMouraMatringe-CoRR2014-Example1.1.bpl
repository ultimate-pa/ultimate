//#rNonTermination
/*
 * Date: 2015-07-06
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Example 1.1 from
 * Rachid Rebiha, Nadir Matringe, Arnaldo Vieira Moura:
 * Generating Asymptotically Non-Terminating Initial Values for Linear Programs. 
 * CoRR abs/1407.4556 (2014)
 * 
 */

procedure main() returns ()
{
  var x, y, z: real;
  while (x - 0.5*y - 2.0*z > 0.0) {
	  x, y, z :=
	      (0.0-20.0)*x - 9.0*y + 75.0*z, 
		  (0.0-7.0 / 20.0) * x + 97.0 / 20.0 * y + 21.0/4.0 * z,
		  37.0 / 97.0 * x + 3.0 / 97.0 * y - 40.0 / 97.0 * z;
  }
}

