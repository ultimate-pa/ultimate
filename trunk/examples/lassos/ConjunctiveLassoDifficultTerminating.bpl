//#rTermination
/*
 * Date: 2014-01-25
 * Author: leike@informatik.uni-freiburg.de
 *
 * This is one of two brother examples that may be one of the
 * most difficult conjunctive lassos.
 *
 * The eigenvalues are 1 and 1/2.
 * In an execution, the value of q increases until it reaches almost 55,
 * then decreases to negative infinity.
 *
 * This is the terminating brother, because it terminates when reaching 54.
 */

procedure main() returns (q: real, a: real, b: real)
{
	q := 0.0;
	a := 16.0;
	b := 8.0;
	while (q <= 54.0) {
		q := q + a - 1.0;
		a := 0.5*a + b;
		b := 0.5*b;
	}
}
