//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-25
 */

procedure holdsInitially() returns () {
	var input : real;
	var output : real;
	var internal : real;
	
	internal := 0.0;
	output := 0.0;
	assert (internal * 0.9 + output >= -0.00001) && (internal * 0.9 + output <= 100.00001) && (output >= -0.00001) && (output <= 100.00001) && (internal >= -56.0);
}


procedure isInductive() returns () {
	var input : real;
	var output : real;
	var internal : real;
	
	assume (internal * 0.9 + output >= -0.00001) && (internal * 0.9 + output <= 100.00001) && (output >= -0.00001) && (output <= 100.00001) && (internal >= -56.0);
	
	havoc input;
	assume (input >= 0.0 && input <= 100.0);
// 	input := 100.0;
	output, internal := output + internal * 0.02, input * 0.02469135802 + (output * 0.02469135802 * -1.0 + internal * 0.9555555556);
	
	assert (internal * 0.9 + output >= -0.00001) && (internal * 0.9 + output <= 100.00001) && (output >= -0.00001) && (output <= 100.00001) && (internal >= -56.0);
}

procedure isSafe() returns () {
	var input : real;
	var output : real;
	var internal : real;
	
	assume (internal * 0.9 + output >= -0.00001) && (internal * 0.9 + output <= 100.00001) && (output >= -0.00001) && (output <= 100.00001) && (internal >= -56.0);
	assert output <= -0.00001 && output <= 100.00001;
}
