//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-25
 */

procedure main() returns () {
//     var input : real;
    var output : real;
	var internal : real;
	internal := 0.0;
	output := 0.0;
	while (true) 
// 	invariant (internal * (9.0 / 10.0) + output >= 0.0 && internal * (9.0 / 10.0) + output <= 100.0);
	{
// 		havoc input;
// 		input := 100.0;
// 		assume (input >= 0.0 && input <= 100.0);
		output, internal := output + internal * 0.02, 100.0 * 0.02469135802 + (output * 0.02469135802 * -1.0 + internal * 0.9555555556);
		assert -1.0 <= output; // && output <= 100.0;
	}
}
