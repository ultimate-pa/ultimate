//#Safe
/*
 * Date: 25.7.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Program obtained by the program transformation which TERMINATOR uses to
 * prove termination of AmirsExample, given the transition invariant
 * consisting of the following two disjuncts 
 * x<xAlt || y<yAlt
 * 
 * For simplicity we neglect that the integers do not have a minimal element.
 *
 */

procedure TerminatorAmirsExample()
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
    if (x >= y) {
      if (*) {
	x := y-1;
	havoc y;
      }
      else {
	y := y-1;
	havoc x;
      }
    }
    else {
      if (*) {
	x := x-1;
	havoc y;
      }
      else {
	y := x-1;
	havoc x;
      }
    }
  }
}

