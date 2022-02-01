//#Safe
/* 
 * Program encodes that two simple Markov chains are equivalent.
 * 
 * Author: Matthias Heizmann
 * Date: 2016-04-05
 */


procedure main() returns (){
	// states of Markov chain on the left-hand side
	var q0, q1 : real;
	
	// states of the Markov chain on the right hand side
	var p0, p1, p2, p3 : real;

	// initial probability for being in a state
	q0 := 1.0;
	q1 := 0.0;
	
	p0 := 1.0;
	p1 := 0.0;
	p2 := 0.0;
	p3 := 0.0;

	while (true) {
		// check that probablity for output a is similar in both Markov chains
		assert (q0 == p0 + p2);
		// check that probablity for output b is similar in both Markov chains
		assert (q1 == p1 + p3);
		
		
		if (*) {
			// effect of taking a transition whose output is a
			q1 := q0;
			q0 := 0.0;
			
			p3 := p2*4.0/5.0 + p0*1.0/2.0;
			p1 := p2*1.0/5.0 + p0*1.0/2.0;
			p2 := 0.0;
			p0 := 0.0;
		} else {
			// effect of taking a transition whose output is b
			q0 := q1;
			q1 := 0.0;
			
			p2 := p1*1.0/3.0 + p3*1.0/7.0;
			p0 := p1*2.0/3.0 + p3*6.0/7.0;
			p1 := 0.0;
			p3 := 0.0;
		}
	}
}

