//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2020-04-09
 * 
 * Variant of ProbabilisticLeaderElection.bpl where
 * have only three variables p1,p2,p3 that sum up the
 * probabilities that we have one, two, or three tokens.
 * 
 */

procedure main() returns () {
  var p1, p2, p3 : real;
  // The variable d measures the distance between the probability
  // that a leader is elected to the probability one.
  // The variable dOld stores this probability for the last round.
  var d, dOld, q : real;
  p1 := 0.0;
  p2 := 0.0;
  p3 := 1.0;
  d := 1.0 - p1;
  while(*)
  {
	  // Check that the sum of all probabilities is always one.
      assert p3 + p2 + p1 == 1.0;
      p3,
	  p2,
	  p1
	  := 
	  (1.0/4.0) * p3, // p3
	  (9.0/12.0) * p2 + (3.0/4.0) * p3,// p2
	  p1 + (3.0/12.0) * p2; // p1
	  dOld := d;
	  d := 1.0 - p1;
	  q := d / dOld ;
	  // Check that the distance is decreasing by a constant factor
	  // which would imply convergence.
	  assert dOld == 1.0 || d < dOld / 1.1;
  }
}


