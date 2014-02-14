//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 01.04.2012
 * 
 * Reduced version of Jeremis and Vincents nT_TRE.bpl
 * 
 * Using StrongesPost determinizer the Hoare Annotation is not inductive 
 *
 */




procedure Main()
{
	var x : int;
        var ret: bool;
	
	x:= 1;

        call ret:= nT(x);

	assert(ret != false);
}

procedure nT(x : int) returns (ret : bool)
{
	var y : int;
	var verum : bool;
	
//	havoc y;
//	assume( y == x || y == 0);

	y := x;
	if(*) {
		y := 0;
	}
	
	while (true) 
	{
		call verum := alwaysTrue(y);
		if (!verum) { ret := false; return; }

	}
}

procedure alwaysTrue(x : int) returns (ret : bool)
{
	var CallRet : bool;
	
	 call CallRet := isZero(x);
	 if (CallRet) {
	 	ret := true;
	 }
	 else
	 {
	 	call ret := notZero(x);
	 }
}

procedure isZero(x : int) returns (ret : bool)
{
	if (x == 0) {
		ret := true;
	} else {
		ret := false;
	}
}

procedure notZero(x : int) returns (ret : bool)
{
	if (x != 0) {
		ret := true;
	} else {
		ret := false;
	}
}