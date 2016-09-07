//#Safe
//////////////////////////////////////////////////////////////////
/////////// testing the property AG(x==0 or x!=0)
// 1 while(*) {
// 2   x := 1;
// 3   n := *;
// 4   while(n>0) {
// 5     n := n - 1;
// 6     }
// 7   x := 0;
// 8 }
// 9 while(true) { skip }
//////////////////////////////////////////////////////////////////

procedure Test()
{
	var x : int;
	var n : int;

        var ret: bool;
	x:= 1;
	havoc n;
        call ret:= encT(x,n);

	assert(ret != false);
}

procedure encT(x : int, n : int) returns (ret : bool)
ensures x==1 ==> ret != false;
{
	var x_local : int;
	var n_local : int;
	var star : bool;
	var blockCall : bool;
	
	x_local := x;
	n_local := n;

	havoc star;
	while(star) {

	
		x_local := 1;
		// BLOCK 1
		call blockCall := encLT(x_local, n_local);
		if (!blockCall) { ret := false; return; }
		havoc star;
		if (star) {	ret := true; return;}
		// END BLOCK 1
		
		havoc n_local;
		while (n_local > 0) {
		
			n_local := n_local -1;
			
		}
		
		x_local := 0;
		// BLOCK 1
		call blockCall := encLT(x_local, n_local);
		if (!blockCall) { ret := false; return; }
		havoc star;
		if (star) {	ret := true; return;}
		// END BLOCK 1
		
		havoc star;
	}
	while (true) 
	{

	}
}

// -------
procedure encLT(x : int, n : int) returns (ret : bool)
ensures (x == 0 || x == 1) ==> ret != false;
{
	var x_local : int;
	var n_local : int;
	var CallRet : bool;
	var star : bool;
	
	x_local := x;
	n_local := n;

	 call CallRet := encLLT(x_local, n_local);
	 if (CallRet) {
	 	ret := true;
	 }
	 else
	 {
	 	call ret := encRLT(x_local, n_local);
	 }

}

procedure encLLT(x : int, n : int) returns (ret : bool)
ensures x == 0 <==> ret !=false;
{
	if (x == 0) {
		ret := true;
	} else {
		ret := false;
	}
}

procedure encRLT(x : int, n : int) returns (ret : bool)
ensures x == 1 <==> ret !=false;
{
	if (x == 1) {
		ret := true;
	} else {
		ret := false;
	}
}