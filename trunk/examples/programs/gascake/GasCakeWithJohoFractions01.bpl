//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-25
 */

procedure main() returns () {
    var input : real;
    var output : real;
	var internal : real;
	internal := 0.0;
	output := 0.0;
	while (true)
	// the following invariant is sufficient to prove that both assert statements always hold
	invariant (internal * (9.0 / 10.0) + output >= 0.0 && internal * (9.0 / 10.0) + output <= 100.0 && 0.0 <= output && output <= 100.0);
	// the following invariant is NOT sufficient to prove that both assert statements always hold
	// however if we add this invariant, Ultimate Automizer is able to prove correctness and to infer the invariant above
// 	invariant (internal * (9.0 / 10.0) + output >= 0.0 && internal * (9.0 / 10.0) + output <= 100.0);

	{
 		havoc input;
//  		input := 100.0;
		assume (input >= 0.0 && input <= 100.0);
		output, internal := output + internal * 0.02, input * (2.0 / 81.0) + (output * (2.0 / 81.0) * -1.0 + internal * (43.0 / 45.0));
		assert 0.0 <= output;
		assert output <= 100.0; 
	}
}
