//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2020-04-09
 * 
 * The Sunshine&Rain Markov chain encoded as a program.
 * If we omit the assumption ps+pr==1.0 in the loop body
 * Automizer is unable to prove the specification.
 * If we have this assumption, Automizer proves that the
 * specification hold (in four iterations) and outputs the
 * following loop invariant.
 * 2.0 * pr + 3/5 <= 2.0 * ps
 */

procedure main() returns () {
  var ps, pr : real;
  ps := 1.0;
  pr := 0.0;
  while(*)
//       invariant ps >= (3.0/5.0) && pr < (2.0/5.0);
  {
      assume ps+pr == 1.0;
      assert (ps >= (3.3/5.0));
      ps, pr := 0.75 * ps + 0.5 * pr, 0.25 * ps + 0.5 * pr;
  }
}


