//#rTerminationDerivable
/*
 * Simple (simplest?) program that has a 2-phase ranking function but no
 * 2-nested ranking function.
 *
 * Date: 24.03.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure proc() returns () {
  var y,z: int;
  while (z >= 0) {
    y := y - 1;
    if (y >= 0) {
      havoc z;
    } else {
      z := z - 1;
    }
  }
}
