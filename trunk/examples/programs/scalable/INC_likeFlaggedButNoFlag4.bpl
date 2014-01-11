//#Safe
/*
 * author: nutz@informatik.uni-freiburg.de
 */

procedure foo(){
	var x:int;
	var y, z, a:int;

	x:=0;
	y:=0;
	z:=0;
	a:=0;
	
	if(*) {
		if(*) {
			while(*) {
				x := x + 1;
			}
	} else {
			while(*) {
				y := y + 1;
			}
		}
	} else {
		if(*) {
			while(*) {
				z := z + 1;
			}
		}
		else {
			while(*) {
				a := a + 1;
			}
		}
	}
	
	assert((x>=0 && y==0 && z==0 && a==0) || (x==0 && y>=0 && z==0 && a==0) || (x==0 && y==0 && z>=0 && a==0) || (x==0 && y==0 && z==0 && a>=0));
}
