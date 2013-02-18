procedure foo() {
	var x,y:int;
	x:=0;
	while(*) 
	invariant (x>=0);{
		if (*) {
			if (x>0) {
				x:=x-1;
			}
			else {
				x:=x+1;
			}
		} else if (*) {
			if (y>0) {
				y:=y-1;
			}
			else {
				y:=y+1;
			}
		}
	}
}

procedure bar() {
	var x,y:int;
	x:=0;
	while(*) 
	invariant (x>=0);{
		if (*) {
			if (x>0) {
				x:=x-1;
			}
		} else {
			if (y>0) {
				y:=y-1;
			}
		}
	}
}