//#Unsafe
// 6.10.2016 DD: 
// Congruence domain reports safe on this example. 
// If assume 2 > x is replaced by assume x < 2, the bug is not present. 

procedure ULTIMATE.start() {
	var x: int;
	assume 2 > x ;
	assert x != 0;
}
