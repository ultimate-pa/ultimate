//#Safe
/*
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

procedure foo(){
	var x:int;
	var y:int;

	x:=0;
	y:=0;
	
	if(*) {
		while(*) {
			x := x + 1;
		}
	}
	else {
		while(*) {
			y := y + 1;
		}
	}
	
	assert((x==0 && y>=0) || (y==0 && x>=0));
}
