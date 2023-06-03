//#rTerminationDerivable
/*
 * Program from Fig.7 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 * 
 * Has a 2-phase ranking function, but neither a lexicographic nor a nested 
 * ranking function.
 *
 * Date: 24.03.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure proc() returns () {
  var a,i,b,j,c,M,N: int;
  a := i;
  b := j;
  c := 0;
  while (i<M || j<N) {
    i := i + 1;
    j := j + 1;
    c := c + 1;
  }
}
