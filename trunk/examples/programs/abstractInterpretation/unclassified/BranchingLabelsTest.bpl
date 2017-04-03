//#Safe
procedure foo() {
	var x,y:int;
	x:=0;
	if (x>0) {
		x:=x-1;
	}
	else {
		x:=x+1;
	}
	if (*) {
		x:=x-1;
	}
	else {
		x:=x+1;
	}
	if (x>0) {
		x:=x-1;
	}
	if (*) {
		x:=x-1;
	}
}
