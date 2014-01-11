//#Safe
/*
 * Implementation of McCarthy's 91 function. The program is correct with
 * respect to assertions.
 * In order to proof correctness one has to infer some requires/ensures pairs
 *
 * The example is taken from our POPL'10 paper "Nested Interpolants".
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 */

/*@ requires \true;
  @ ensures x > 101 || \result == 91;
  @*/
int f91(int x);

int f91(int x) {
	if (x > 100)
		return x -10;
	else {
		return f91(f91(x+11));
	}
}