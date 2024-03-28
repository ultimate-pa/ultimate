//#rTermination
/*
 * Simplified version of the example consts1 that was used in
 * 2013CAV - Brockschmidt,Cook,Fuhs - Better termination proving through cooperation
 * as is available at the following URL
 * http://verify.rwth-aachen.de/brockschmidt/Cooperating-T2/
 * 
 * Date: 7.02.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
var v : int;
  v := 300;
  while (true) {
    v := v - 1;
    if (*) {
      assume(v <= 99);
    } else {
      assume(101 <= v);
    }
  }
}

