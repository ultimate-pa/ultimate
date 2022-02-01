//#Safe
/*
 * Date: 25.7.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Program obtained by the program transformation which TERMINATOR uses to
 * prove termination of MyFavoriteProgram, given the transition invariant
 * y'<y \/ x'<x.
 *
 */

procedure TerminatorSmall()
{
  var x, xAlt, y, yAlt, pcAlt: int;

  pcAlt := 0;

  while (true) {
    assert(pcAlt != 1 || x<xAlt || y<yAlt);
    if (*) {
      if (pcAlt == 0) {
	xAlt := x;
	yAlt := y;
	pcAlt := 1;
      }
    }
    if (*) {
      y := y-1;
    }
    else {
      x := x-1;
      havoc y;
    }
  }
}

