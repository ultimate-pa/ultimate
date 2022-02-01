//#Safe
procedure main() {
	var i : real;
	while (i <= 999.0) {
		i := i + 1.0;
	}
	assert i >= 1000.0;
}
