//#Safe
//author: ermis@informatik.uni-freiburg.de
/*
 * Test global variables for Chainsaw
 */
var x, y: int;



procedure foo() returns (result: int);
modifies x,y;
ensures result > 0;

procedure bar();
modifies y;
ensures y > 0;

implementation foo() returns (result: int) {
	x:=0;
	call bar();
	result := x+y;
}

implementation bar() {
	havoc y;
	assume y > 0;
}

