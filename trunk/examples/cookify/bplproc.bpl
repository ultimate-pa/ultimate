var gvar1 : bool;
var gvar2 : int;

procedure main() 
modifies gvar2;
{
	var lvar1 : bool;
	call lvar1 := S(12);
}

procedure S(n : int) returns (retn : bool) 
modifies gvar2; 
{
	var lvar1 : int;
	lvar1 := gvar2;
	if (n == 0) {
		retn := true;
		call gvar2 := T(true);
		return;
	}
	retn := false;
}

procedure T(b : bool) returns (retn : int) {
	retn := 3;
}