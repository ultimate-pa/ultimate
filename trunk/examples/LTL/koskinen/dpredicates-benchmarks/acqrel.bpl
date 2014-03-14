// Based on benchmark acqrel.c
// manually translated by DD
//
// #LTLProperty: x U (!x && [](a -> <>b))
// #IRS: a: A = 1
// #IRS: b: R = 1
// #IRS: x: init = 0
// 
// Property should hold 
// 
// Additional comments: 
// * init is new and necessary to state that the property should only be analysed after init 
// * ULTIMATE.start() replaced an empty main() method 

var A, R : int;
var init : int;

procedure init() 
modifies A,R;
{ 
	A := 0;
	R := 0; 
}

procedure body() 
modifies A,R;
{
	var x : int;
	var n : int;	
	while(*) 
	{
		A := 1;
		A := 0;
		havoc n;
		while(n>0) {
		  n := n -1 ;
		}
		R := 1;
		R := 0;
	}
	while(true) { 
	
		x:= x; 
	}
}

procedure ULTIMATE.start() 
modifies A,R,init;
{
	init := 0;
	call init();
	init := 1;
	call body();
}
