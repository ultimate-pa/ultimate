//#Safe
//author: nutz@informatik.uni-freiburg.de

procedure foo(){
	var x:int;
	var y, z, a, x1, x2, x3, x4:int;

	x:=0;
	y:=0;
	z:=0;
	a:=0;
	x1:=0;
	x2:=0;
	x3:=0;
	x4:=0;

	if(*) {	
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
			} else {
				while(*) {
					a := a + 1;
				}
			}
		}
	} else {
		if(*) {	
			if(*) {
				while(*) {
					x1 := x1 + 1;
				}	
			} else {
				while(*) {
					x2 := x2 + 1;
				}
			}
		} else {
			if(*) {
				while(*) {
					x3 := x3 + 1;
				}
			} else {
				while(*) {
					x4 := x4 + 1;
				}
			}
		}
	}

	assert((x>=0 && y==0 && z==0 && a==0 && x1==0 && x2==0 && x3==0 && x4==0) || (x==0 && y>=0 && z==0 && a==0 && x1==0 && x2==0 && x3==0 && x4==0) || (x==0 && y==0 && z>=0 && a==0 && x1==0 && x2==0 && x3==0 && x4==0) 	|| (x==0 && y==0 && z==0 && a>=0 && x1==0 && x2==0 && x3==0 && x4==0) 	|| (x==0 && y==0 && z==0 && a==0 && x1>=0 && x2==0 && x3==0 && x4==0) 	|| (x==0 && y==0 && z==0 && a==0 && x1==0 && x2>=0 && x3==0 && x4==0) || (x==0 && y==0 && z==0 && a==0 && x1==0 && x2==0 && x3>=0 && x4==0) || (x==0 && y==0 && z==0 && a==0 && x1==0 && x2==0 && x3==0 && x4>=0));
}
