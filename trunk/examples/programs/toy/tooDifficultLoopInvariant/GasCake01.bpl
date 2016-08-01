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
 	invariant (internal * 0.9 + output >= -0.00001) && (internal * 0.9 + output <= 100.00001) && (output >= -0.00001) && (output <= 100.00001) && (internal >= -56.0);
	{
		havoc input;
// 		input := 100.0;
		assume (input >= 0.0 && input <= 100.0);
		output, internal := output + internal * 0.02, input * 0.02469135802 + (output * 0.02469135802 * -1.0 + internal * 0.9555555556);
 		assert -0.00001 <= output && output <= 100.00001;
	}
}
