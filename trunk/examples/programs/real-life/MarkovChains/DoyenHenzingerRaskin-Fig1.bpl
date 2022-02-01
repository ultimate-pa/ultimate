//#Safe
/* 
 * Program encodes that the two Markov chains from Figure 1 of the following
 * publication are equivalent.
 * 
 * 2008IJFCS - Doyen,Henzinger,Raskin - Equivalence of Labeled Markov Chains
 *
 * Author: Matthias Heizmann
 * Date: 2016-04-04
 */


procedure main() returns (){
	// states of Markov chain on the left-hand side
	var q11, q12, q13, q14, q15, q16, q17, q18 : real;
	
	// states of the Markov chain on the right hand side
	var q21, q22, q23, q24, q25 : real;

	// initial probability for being in a state
	q11 := 1.0;
	q12 := 0.0;
	q13 := 0.0;
	q14 := 0.0;
	q15 := 0.0;
	q16 := 0.0;
	q17 := 0.0;
	q18 := 0.0;

	
	q21 := 1.0;
	q22 := 0.0;
	q23 := 0.0;
	q24 := 0.0;
	q25 := 0.0;

	while (true) {
		// check that probablity for output a is similar in both Markov chains
		assert (q11/2.0 + q11/2.0
			+ q12*2.0/3.0 + q12/3.0
			+ q13/3.0 + q13*2.0/3.0
			+ q14*1.0 + q16*1.0
			==
			q21*1.0
			+ q22/2.0 + q22/2.0
			+ q23*1.0);
		// check that probablity for output b is similar in both Markov chains
		assert (q15*1.0 + q17*1.0 == q24*1.0);
		// check that probablity for output c is similar in both Markov chains
		assert (q18*1.0 == q25*1.0);
		
		
		if (*) {
			// effect of taking a transition whose output is a
			q18 := q14 + q16;
			q17 := q13*2.0/3.0;
			q16 := q13/3.0;
			q15 := q12/3.0;
			q14 := q12*2.0/3.0;
			q13 := q11/2.0;
			q12 := q11/2.0;
			q11 := 0.0;
			
			q25 := q23;
			q24 := q22/2.0;
			q23 := q22/2.0;
			q22 := q21;
			q21 := 0.0;
		} else if (*) {
			// effect of taking a transition whose output is b
			q18 := q15 + q17;
			q17 := 0.0;
			q16 := 0.0;
			q15 := 0.0;
			q14 := 0.0;
			q13 := 0.0;
			q12 := 0.0;
			q11 := 0.0;
			
			q25 := q24;
			q24 := 0.0;
			q23 := 0.0;
			q22 := 0.0;
			q21 := 0.0;
		} else {
			// effect of taking a transition whose output is c
			q17 := 0.0;
			q16 := 0.0;
			q15 := 0.0;
			q14 := 0.0;
			q13 := 0.0;
			q12 := 0.0;
			q11 := 0.0;
			
			q24 := 0.0;
			q23 := 0.0;
			q22 := 0.0;
			q21 := 0.0;
		}
	}
}

