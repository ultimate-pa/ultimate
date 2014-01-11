//#Safe
// Author: Evren, Alex

procedure main() {
var w,x,y,z,n: int;

	n := w + x + y + z;
	
	while(x != 0) {
		if (*) {
			w := w + 1;
			x := x - 1;
		}
		if (*) {
			x := x + 1;
			y := y - 1;
		}
		if (*) {
			y := y + 1;
			z := z - 1;
		}
		if (*) {
			z := z + 1;
			w := w - 1;
		}
	}
	
	assert(n == w + y + z);
}
