//#Safe
procedure main() {
	var i : int;
	i := if (i == 0) then -2 else 1;
	assert i != 2;
}
