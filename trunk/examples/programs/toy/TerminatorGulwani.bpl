//#Safe
/*
 * Date: 27.6.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Program obtained by the program transformation which TERMINATOR uses to
 * prove termination of the example in  Figure 1 of
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow Refinement and Progress 
 * Invariants for Bound Analysis.
 *
 * We use the transition invariant ....
 *
 */

procedure Terminator()
{
  var id, maxId, tmp, tmpAlt, pcAlt: int;

  pcAlt := 0;
  assume ( 0 <= id && id < maxId );
  tmp := id+1;

  while (tmp != id) {
    assert(pcAlt != 1 || (tmp>tmpAlt && tmpAlt <= maxId) || (tmpAlt > id && tmp <= id));
    if (*) {
      if (pcAlt == 0) {
	tmpAlt := tmp;
	pcAlt := 1;
      }
    }
    if (tmp <= maxId) {
      tmp := tmp+1;
    }
    else {
      tmp := 0;
    }
  }
}

