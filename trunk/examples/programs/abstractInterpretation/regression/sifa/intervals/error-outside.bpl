//#Safe
procedure main() {
	var i : int;
	assume i >= 3;
	assume i <= 5;
	assert i != 8;
}
