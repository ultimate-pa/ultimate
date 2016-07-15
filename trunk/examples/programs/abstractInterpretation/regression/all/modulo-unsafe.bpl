//#Unsafe
// 0 % n should always be 0 
procedure foo() {
	var x: int;
	x := 0;
	if(x % 4294967296 < 99){
		assert false;
	}
}