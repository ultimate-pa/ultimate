//#Safe
// Based on the small program from section 2 of the paper
// manually translated by DD
//
// #LTLProperty: <>[]AP(x==1)
// 
// Property should hold 
// 
// Additional comments: 
// * There was no method, so I pasted the code in ULTIMATE.start() 

var x : int;

procedure ULTIMATE.start() 
modifies x;
{
	x := 1;
	while (*) {	
		x:=0;
	}
	
	x := 0;
	x := 1;
	//assert x == 0;
	while (true) {}
}

